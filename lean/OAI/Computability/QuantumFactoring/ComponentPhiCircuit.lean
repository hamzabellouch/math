import Mathlib
import OAI.Computability.QuantumFactoring.CanonicalResidueCircuit
import OAI.Computability.QuantumFactoring.ClosedLevelCircuit

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

/-- Euler's prime-power formula, implemented by n-bit arithmetic on the
computed gcd component. Divisibility by p is a verified-call precondition. -/
def componentPhiNet {k n : ℕ} (m p : BooleanNetwork k n) : BooleanNetwork k n :=
  let q:=primeComponent m p
  natSubOn q ((q.pair p).comp (div n))

lemma componentPhiNet_value {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime)
    (hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat) :
    (bitsValue ((componentPhiNet m p).eval x)).toNat=
      primePowerUnitCount (bitsValue (p.eval x)).toNat
        ((bitsValue (m.eval x)).toNat.factorization (bitsValue (p.eval x)).toNat) := by
  have hq:=primeComponent_value m p x hm hp
  have he:=hp.factorization_pos_of_dvd hm hd
  rw [componentPhiNet,natSubOn_value,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,hq]
  obtain ⟨e,he'⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  rw [he',primePowerUnitCount,Nat.succ_sub_one,pow_succ,Nat.mul_div_cancel _ hp.pos]
  simpa only [Nat.mul_one,Nat.one_mul,Nat.mul_comm] using
    (Nat.mul_sub_left_distrib ((bitsValue (p.eval x)).toNat^e) (bitsValue (p.eval x)).toNat 1).symm

lemma componentPhiNet_ne_zero {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime)
    (hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat) :
    (bitsValue ((componentPhiNet m p).eval x)).toNat≠0 := by
  rw [componentPhiNet_value m p x hm hp hd,primePowerUnitCount]
  exact Nat.ne_of_gt (Nat.mul_pos (by have := hp.two_le;omega) (Nat.pow_pos hp.pos))

def componentPhiBound (n c : ℕ) : ℕ := 4*primeComponentBound n c+2*c+1000*n*n+1000*n+100
lemma componentPhiNet_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (componentPhiNet m p).net.count≤componentPhiBound n c := by
  have hq:=primeComponent_count m p hm hp
  have hd:=div_count n
  have hs:=natSubOn_count (primeComponent m p) (((primeComponent m p).pair p).comp (div n))
  simp only [count_comp,count_pair] at hs
  change (natSubOn _ _).net.count≤_
  dsimp only [componentPhiBound]
  nlinarith

def componentLevelNet {k n : ℕ} (m p : BooleanNetwork k n) (t : ℕ) : BooleanNetwork k n :=
  wordMux (dividesOn p m) (closedLevelNet (componentPhiNet m p) t)
    (wordConstant (BitVec.ofNat n 1))

lemma componentLevelNet_value {k n : ℕ} (hn : 2≤n) (m p : BooleanNetwork k n)
    (x : Basis k) (hm : (bitsValue (m.eval x)).toNat≠0)
    (hp : ((bitsValue (p.eval x)).toNat).Prime) (t : ℕ) :
    (bitsValue ((componentLevelNet m p t).eval x)).toNat=
      if (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat then
        closedLevelCount (primePowerUnitCount (bitsValue (p.eval x)).toNat
          ((bitsValue (m.eval x)).toNat.factorization (bitsValue (p.eval x)).toNat)) t
      else 1 := by
  rw [componentLevelNet,wordMux_eval]
  by_cases hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat
  · rw [ite_eq_left ((dividesOn_value p m x).mpr hd),ite_eq_left hd,
      closedLevelNet_value hn _ x (componentPhiNet_ne_zero m p x hm hp hd),
      componentPhiNet_value m p x hm hp hd]
  · rw [ite_eq_right (fun h=>hd ((dividesOn_value p m x).mp h)),ite_eq_right hd,
      wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by decide))]

def componentLevelBound (n c : ℕ) : ℕ :=
  2*c+216*n*n+308*n+50+closedLevelBound n (componentPhiBound n c)+8*n
lemma componentLevelNet_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count≤c) (hp : p.net.count≤c) (t : ℕ) :
    (componentLevelNet m p t).net.count≤componentLevelBound n c := by
  have hc:=closedLevelNet_count (componentPhiNet m p) (componentPhiNet_count m p hm hp) t
  have hd:=dividesOn_count p m
  rw [componentLevelNet,wordMux_count,wordConstant_count]
  dsimp only [componentLevelBound]
  nlinarith
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
