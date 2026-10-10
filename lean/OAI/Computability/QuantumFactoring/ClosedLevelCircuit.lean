import Mathlib
import OAI.Computability.QuantumFactoring.SplitCandidate
import OAI.Computability.QuantumFactoring.PrimePowerLevels
import OAI.Computability.QuantumFactoring.PrimeComponentCircuit
import OAI.Computability.QuantumFactoring.TwoAdicCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- Compute the odd part by a bounded gcd and exact integer division. -/
def oddPartNet {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k n :=
  (a.pair (primeComponent a (wordConstant (BitVec.ofNat n 2)))).comp (div n)

lemma oddPartNet_value {k n : ℕ} (hn : 2 ≤ n) (a : BooleanNetwork k n)
    (x : Basis k) (ha : (bitsValue (a.eval x)).toNat≠0) :
    (bitsValue ((oddPartNet a).eval x)).toNat=
      (bitsValue (a.eval x)).toNat/2^padicValNat 2 (bitsValue (a.eval x)).toNat := by
  have h2 : 2<2^n := lt_of_lt_of_le (by decide : 2<2^2)
    (Nat.pow_le_pow_right (by decide : 0<2) hn)
  have hc : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat n 2)).eval x)).toNat=2 := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]
  have hh:=primeComponent_value a (wordConstant (BitVec.ofNat n 2)) x ha
    (by rw [hc];exact Nat.prime_two)
  rw [hc,Nat.factorization_def _ Nat.prime_two] at hh
  rw [oddPartNet,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,hh]

/-- An exact level count, selected by the bounded divisibility predicate.
The branch at t≥n is zero since a is a nonzero n-bit word. -/
def closedLevelNet {k n : ℕ} (a : BooleanNetwork k n) (t : ℕ) : BooleanNetwork k n :=
  if t=0 then oddPartNet a
  else if t<n then wordMux (a.comp (dividesNet n (2^t)))
    (((oddPartNet a).pair (wordConstant (BitVec.ofNat n (2^(t-1))))).comp (mul n))
    (wordConstant (BitVec.ofNat n 0))
  else wordConstant (BitVec.ofNat n 0)

lemma closedLevelNet_value {k n : ℕ} (hn : 2≤n) (a : BooleanNetwork k n)
    (x : Basis k) (ha : (bitsValue (a.eval x)).toNat≠0) (t : ℕ) :
    (bitsValue ((closedLevelNet a t).eval x)).toNat=
      closedLevelCount (bitsValue (a.eval x)).toNat t := by
  have hodd:=oddPartNet_value hn a x ha
  have hv:=twoadic_lt_width ha (bitsValue (a.eval x)).isLt
  rw [closedLevelNet,closedLevelCount]
  by_cases ht : t=0
  · rw [ite_eq_left ht,ite_eq_left ht,hodd]
  · rw [ite_eq_right ht,ite_eq_right ht]
    by_cases htn : t<n
    · rw [ite_eq_left htn,wordMux_eval]
      have hd : (a.comp (dividesNet n (2^t))).eval x 0=true ↔
          t≤padicValNat 2 (bitsValue (a.eval x)).toNat := by
        rw [eval_comp,dividesNet_value _ _ _ (Nat.pow_lt_pow_right (by decide : 1<2) htn),
          padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha]
      by_cases he : t≤padicValNat 2 (bitsValue (a.eval x)).toNat
      · rw [ite_eq_left (hd.mpr he),ite_eq_left he,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,hodd,
          wordConstant_eval,BitVec.toNat_ofNat]
        have hc : 2^(t-1)<2^n:=Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
        rw [Nat.mod_eq_of_lt hc]
        have hdvd : 2^padicValNat 2 (bitsValue (a.eval x)).toNat∣(bitsValue (a.eval x)).toNat :=
          (padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha).mpr le_rfl
        have hp : 2^(t-1)≤2^padicValNat 2 (bitsValue (a.eval x)).toNat :=
          Nat.pow_le_pow_right (by decide : 0<2) (by omega)
        have hb := Nat.mul_le_mul_left ((bitsValue (a.eval x)).toNat/
          2^padicValNat 2 (bitsValue (a.eval x)).toNat) hp
        rw [Nat.div_mul_cancel hdvd] at hb
        rw [Nat.mod_eq_of_lt (hb.trans_lt (bitsValue (a.eval x)).isLt),Nat.mul_comm]
      · rw [ite_eq_right (fun h=>he (hd.mp h)),ite_eq_right he,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]
    · rw [ite_eq_right htn,ite_eq_right (by omega),wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]

def oddPartBound (n c : ℕ) : ℕ := c+primeComponentBound n (c+n)+216*n*n+56*n+6
lemma oddPartNet_count {k n c : ℕ} (a : BooleanNetwork k n) (ha : a.net.count≤c) :
    (oddPartNet a).net.count≤oddPartBound n c := by
  have hp:=primeComponent_count a (wordConstant (BitVec.ofNat n 2))
    (c:=c+n) (by omega) (by rw [wordConstant_count];omega)
  have hd:=div_count n
  simp only [oddPartNet,count_comp,count_pair]
  dsimp only [oddPartBound]
  omega

def closedLevelBound (n c : ℕ) : ℕ := oddPartBound n c+c+1000*n*n+1000*n+100
lemma closedLevelNet_count {k n c : ℕ} (a : BooleanNetwork k n) (ha : a.net.count≤c) (t : ℕ) :
    (closedLevelNet a t).net.count≤closedLevelBound n c := by
  have ho:=oddPartNet_count a ha
  have hd:=dividesNet_count n (2^t)
  have hm:=mul_count n
  rw [closedLevelNet]
  by_cases ht : t=0
  · rw [ite_eq_left ht]
    dsimp only [closedLevelBound];omega
  · rw [ite_eq_right ht]
    by_cases htn : t<n
    · rw [ite_eq_left htn,wordMux_count,count_comp,count_comp,count_pair,
        wordConstant_count,wordConstant_count]
      dsimp only [closedLevelBound]
      nlinarith
    · rw [ite_eq_right htn,wordConstant_count]
      dsimp only [closedLevelBound]
      omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
