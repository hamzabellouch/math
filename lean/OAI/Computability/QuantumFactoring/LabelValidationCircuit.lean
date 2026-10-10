import Mathlib
import OAI.Computability.QuantumFactoring.OrderCandidateLaw
import OAI.Computability.QuantumFactoring.RetrospectiveCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- Every returned denominator, in EVERY mode, undergoes the full arithmetic
check. No primality or order oracle appears in the network. -/
def labelValidNet {k w : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w) : BooleanNetwork k 1 :=
  (wordLt (wordConstant (BitVec.ofNat w 0)) d).band
    ((wordLt d (wordConstant (BitVec.ofNat w (2^n)))).band
      ((wordLt j d).band
        ((equalOn ((j.pair d).comp (gcdNet w)) (wordConstant (BitVec.ofNat w 1))).band
          (equalOn (powOn a m d) (wordConstant (BitVec.ofNat w 1))))))

lemma labelValidNet_value {k w : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w)
    (hn : n<w) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (labelValidNet n a m d j).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat := by
  have hp : 1<2^w := Nat.one_lt_two_pow (by omega)
  have hB : 2^n<2^w := Nat.pow_lt_pow_right (by decide) hn
  simp only [labelValidNet,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,
    equalOn_value,eval_comp,eval_pair,gcdNet_value,powOn_value a m d x hm,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hB,
    ValidLabel,Nat.Coprime]

lemma labelValidNet_count {k w c : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w)
    (ha : a.net.count≤c) (hm : m.net.count≤c) (hd : d.net.count≤c) (hj : j.net.count≤c) :
    (labelValidNet n a m d j).net.count ≤
      9*c+2*w*(216*w*w+300*w+100)+w+w*(3672*w*w+436*w+36)+344*w+70 := by
  have h0 := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 0)) d
  have hB := wordLt_count d (wordConstant (n:=k) (BitVec.ofNat w (2^n)))
  have hjd := wordLt_count j d
  have hg := equalOn_count ((j.pair d).comp (gcdNet w)) (wordConstant (n:=k) (BitVec.ofNat w 1))
  have hp := equalOn_count (powOn a m d) (wordConstant (n:=k) (BitVec.ofNat w 1))
  have hgc := gcdNet_count w
  have hpow := powOn_count a m d
  simp only [count_comp,count_pair,wordConstant_count] at h0 hB hjd hg hp
  simp only [labelValidNet,count_band]
  omega

end ExactQuantumFactoring.OrderTrial


end

end OAI
