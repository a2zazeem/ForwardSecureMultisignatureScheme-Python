# This is a python implementation of Pixel Signature scheme
# This code generates test vectors for the scheme, that is used to
# cross compare with rust's test vectors, to ensure the correctness
# of the implementation.

# This code is of low quality, and should not be used for any purpose
# other than testing and debugging.

# change this path to they python bls code
import sys
import time

def start_time():
  return time.time()

def end_time():
  return time.time()

from random import randint
sys.path.append("/Users/zhenfei/Documents/GitHub/bls_sigs_ref/python-impl")
import filecmp
import copy
from hashlib import sha256

from curve_ops import g1gen, g2gen, point_neg, point_add, point_mul
from param import default_param
from keyupdate import sk_update, time_to_vec
from keygen import key_gen, serialize_sk, print_sk
from serdesZ import serialize
from sig import sign_present, serialize_sig, print_sig
from pairing import multi_pairing

g2 = g2gen # using fixed generator for g2
D = 4   # depth
# subgroup order
q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
h = 0
hv = [0] * (D+1) ## vector of D+1 group elements in G1


def G1add(a, b):
    return point_add(a, b)


def G2add(a, b):
    return point_add(a, b)

def G1rand():
#  if r is None:
#    r = randint(1,q-1)
  return G1mul(g1gen,randint(1,q-1))

def G1mul(a, b):
    ## a group element, b scalar
    return point_mul(b, a)


def vip(va, vb):
## return inner product of va, vb
## in group setting: this is over G1
    ans = G1mul(va[0],vb[0])
    for i in range(1,len(va)):
      ans = G1add(ans, G1mul(va[i],vb[i]))
    return ans

def hw(wv):
  ## h_0 prod hj^wj
  ## wv is a vector
  return vip(hv[:len(wv)+1], [1]+wv)

def G2neg(a):
    return point_neg(a)

def tmv(tv, M):
## returns the vector associated with time tv and message M
  return tv + [0] * (D-len(tv)-1) + [M]

def GTtestpp(va, vb):
    ## checks whether <va, vb> == 0
    return (multi_pairing(va, vb) == 1)

def sig_aggregation(signatures):
    aggregated_signature = list(signatures[0])  # Copy the first signature

    for signature in signatures[1:]:
        aggregated_signature[2] = tuple(
            fq2_elem1 * fq2_elem2 for (fq2_elem1, fq2_elem2) in zip(aggregated_signature[2], signature[2])
        )
        aggregated_signature[1] = tuple(
            fq_elem1 * fq_elem2 for (fq_elem1, fq_elem2) in zip(aggregated_signature[1], signature[1]))
        new_agg_sig = [aggregated_signature[2], aggregated_signature[1]]
    return new_agg_sig

def key_aggregation(public_keys):
    aggregated_public_key = public_keys[0]  # Copy the first public key

    for public_key in public_keys[1:]:
        aggregated_public_key = tuple(
            fq_elem1 * fq_elem2 for (fq_elem1, fq_elem2) in zip(aggregated_public_key, public_key)
        )
    return aggregated_public_key

def verify(pk, tar_time, M, sig):
  ## check e(sig[1], g2) = e(h, pk) * e(hw(tv) h_D^M, sig[0])
  if isinstance(M,bytes):
    M = int(sha256(M).hexdigest(),base=16) % q
    tv = time_to_vec(tar_time, D)
  return GTtestpp( [sig[1],    h,  hw(tmv(tv,M))],
                   [G2neg(g2), pk, sig[0] ] )

def setup(mode=None):
  global h, hv
  if (mode==0):
    h = g1gen
    for i in range(0,D+1):
      hv[i] = G1mul(g1gen,i+1)
  else:
    h = G1rand()
    for i in range(0,D+1):
      hv[i] = G1rand()



def vadd(va, vb):
## input: vectors va, vb
## return coordinate-wise addition of va, vb
## in group setting: first entry over G2, remaining entries over G1
  assert (len(va) > 0)
  ans = [ G2add(va[0],vb[0]) ]
  for i in range(1,len(va)):
      ans.append( G1add(va[i],vb[i]) )
  return ans

def vmul(va, b):
## multiply each entry of vector va by scalar b
## in group setting: first entry over G2, remaining entries over G1
  assert (len(va) > 0)
  ans = [ G2mul(va[0],b) ]
  for i in range(1,len(va)):
      ans.append( G1mul(va[i],b) )
  return ans



def tkey_rand(tsk,w,r=None):
  if r is None:
    r = randint(1,q-1)
  ha = hw(w)  ## h_0 prod hj^wj
  hvb = hv[len(w)+1:] ## h_{|w|+1}, ..., h_D
  return vadd(tsk, vmul([g2] + [ha] + hvb, r))

def tkey_delegate(tsk,w,wplus):
  ## delegates tsk_w to tsk_{w || wplus} -- doesn't mutate
  ## doesn't randomize
  # assert len(tsk) == D-len(w)+2
  wnew = w + wplus
  ans = tsk[0:1] # g2^r
  ans.append(vip(tsk[1:len(wplus)+2], [1]+wplus)) ## computes (h_0 prod hj^wj)^r for wnew
  ans.extend(tsk[len(wplus)+2:]) ## h_{|wnew|+1}^r, ..., h_D^r
  return ans


def test_vector(seed,msg):
    setup(0)
    keygen_start_time = time.time()
    pk, sk1 = key_gen(seed)
    keygen_end_time = time.time()
    keygen_time = keygen_end_time - keygen_start_time
    # print("Keygen Time = ", keygen_time)
    sk2 = sk_update(copy.deepcopy(sk1), default_param, 3, seed)
    sig_start_time = time.time()
    sig = sign_present(sk2, 3, default_param, msg)
    sig_end_time = time.time()
    print("Signature Time = ", sig_end_time-sig_start_time)

    sk_back_up = copy.deepcopy(sk1)
    # print("public key size: ", sys.getsizeof(pk))
    # print("secret key size: ", sys.getsizeof(sk1))
    # print("Signature Size: ", sys.getsizeof(sig))

    # update the secret key sequentially, and make sure the
    # updated key matched rust's outputs.
    # for i in range(2,4):
    #     print("updating to time %d"%i)
    #
    #     # updated sk and signatures
    #     sk2 = sk_update(copy.deepcopy(sk), default_param, i, seed)
    #     sig = sign_present(sk2, i, default_param, msg)
    #     print("updated secret key size: ", sys.getsizeof(sk2))
    #     print("updated sig size: ", sys.getsizeof(sig))
    #     sk = copy.deepcopy(sk2)
    #
    # sk = copy.deepcopy(sk_back_up)
    # for i in range(2,4):
    #
    #     cur_time = sk[1][0][0]
    #     tar_time = cur_time+i
    #     print("updating from time %d to time %d"%(cur_time, tar_time))
    #
    #     # updated sk and signatures
    #     sk2 = sk_update(copy.deepcopy(sk), default_param, tar_time, b"")
    #     sig = sign_present(sk2, tar_time, default_param, msg)
    #
    #     print("updated secret key size: ", sys.getsizeof(sk2))
    #     print("updated sig size: ", sys.getsizeof(sig))
    #     sk = copy.deepcopy(sk2)
    return pk , sig, sk2



if __name__ == "__main__":
    def main():
        seed1 = b"this is a very long seed1 for pixel tests"
        seed2 = b"this is a very long seed2 for pixel tests"
        seed3 = b"this is a very long seed3 for pixel tests"
        message = b'This is going to be a message of 100 bytes for a sample program run'
        pk1, sig1, sk1 = test_vector(seed1, message)
        pk2, sig2, sk2 = test_vector(seed2, message)
        pk3, sig3, sk3 = test_vector(seed3, message)
        # print("sig1 = ", sig1)
        # print("sig2 = ", sig2)
        # print("sig3 = ", sig3)
        key_agg_start_time = time.time_ns()
        agg_pk = key_aggregation([pk1,pk2,pk3])
        key_agg_end_time = time.time_ns()
        key_agg_time = key_agg_end_time - key_agg_start_time
        print("Key Aggregation Time in nanoseconds: ", key_agg_time)



        # print("agg_pk = ", agg_pk)
        sig_aggregation_start_time = int(time.time_ns())
        signat = sig_aggregation([sig1,sig2,sig3])
        sig_aggregation_end_time = int(time.time_ns())
        print("Signature Aggregation Time in nanoseconds: ", sig_aggregation_end_time-sig_aggregation_start_time)
        # print("agg_sig = ", signat)


        # print("agg pks and agg signature are:", agg_pk, signat)
        verification_start_time = time.time() * 1000
        verify(agg_pk, 3, message, signat)
        verification_end_time = time.time() * 1000
        print("Verification Successful")
        print("Verification Time: ", verification_end_time-verification_start_time)

    main()