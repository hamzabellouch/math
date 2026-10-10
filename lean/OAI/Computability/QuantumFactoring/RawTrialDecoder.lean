import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialLabelCircuit
import OAI.Computability.QuantumFactoring.TrialControlCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- Exact ordinary trial decoder, including the sampler's full workspace test,
continued-fraction reconstruction, arithmetic validation, and all three retained
coin tests. Its inputs are actual retained raw bits. -/
def rawAcceptNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k 1 :=
  trialAcceptOn n (toWidth (decodeWidth u s n) a) (toWidth (decodeWidth u s n) m)
    (toWidth (decodeWidth u s n) (rawMode r)) (trialDenNet r) (trialNumNet r)
    (toWidth (decodeWidth u s n) (rawResidue r)) (toWidth (decodeWidth u s n) (rawCoin r))
    (samplerSelectedNet a m (rawSample r))

lemma rawAcceptNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (rawAcceptNet a m r).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (labelPair s n y).1 (labelPair s n y).2 ∧
      labelEvent s n (a.eval x) (m.eval x) (labelPair s n y).1 (labelPair s n y).2 y := by
  have hu : u≤decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n<decodeWidth u s n := by unfold decodeWidth; omega
  have hw : 2≤decodeWidth u s n := by unfold decodeWidth; omega
  have hc : retentionBits n≤decodeWidth u s n := by unfold decodeWidth; omega
  have hm' : 2≤(bitsValue ((toWidth (decodeWidth u s n) m).eval x)).toNat := by
    rw [toWidth_value m hu]; exact hm
  rw [rawAcceptNet,trialAcceptOn_value _ _ _ _ _ _ _ _ _ hn hw x hm']
  simp only [toWidth_value a hu,toWidth_value m hu,toWidth_value (rawMode r) hw,
    toWidth_value (rawResidue r) hn.le,toWidth_value (rawCoin r) hc,
    trialDenNet_value r x y h,trialNumNet_value r x y h,
    rawMode_eval r x y h,rawResidue_eval r x y h,rawCoin_eval r x y h,
    samplerSelectedNet_eval,rawSample_eval r x y h]
  rw [labelEvent_self]
  rfl

def trialValueNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (decodeWidth u s n) :=
  wordMux (rawAcceptNet a m r) (trialDenNet r) (wordConstant (BitVec.ofNat (decodeWidth u s n) 0))

lemma trialValueNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((trialValueNet a m r).eval x)).toNat=(trialResult s n (a.eval x) (m.eval x) y).getD 0 := by
  classical
  rw [trialValueNet,wordMux_eval]
  by_cases ht : (rawAcceptNet a m r).eval x 0=true
  · rw [ite_eq_left ht,trialDenNet_value r x y h]
    have hh := (rawAcceptNet_value a m r x y h hm).mp ht
    simp only [trialResult,ite_eq_left hh,Option.getD_some]
  · rw [ite_eq_right ht,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]
    have hh := mt (rawAcceptNet_value a m r x y h hm).mpr ht
    simp only [trialResult,ite_eq_right hh,Option.getD_none]

lemma trialResult_getD_lt {u s n : ℕ} (a m : Basis u) (y : Raw u s n) :
    (trialResult s n a m y).getD 0<2^n := by
  classical
  unfold trialResult
  dsimp only
  split_ifs with h
  · exact h.1.2.1
  · change 0<2^n
    positivity

/-- Only VALID ordinary candidates are narrowed to n bits. This does not apply
to the separately completed rare guess, whose whole transition word is kept. -/
def trialSmallValueNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (trialValueNet a m r).comp (resizeWord (decodeWidth u s n) n)
lemma trialSmallValueNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((trialSmallValueNet a m r).eval x)).toNat=(trialResult s n (a.eval x) (m.eval x) y).getD 0 := by
  rw [trialSmallValueNet,eval_comp,resizeWord_value,BitVec.toNat_setWidth,
    trialValueNet_value a m r x y h hm,Nat.mod_eq_of_lt (trialResult_getD_lt _ _ _)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
