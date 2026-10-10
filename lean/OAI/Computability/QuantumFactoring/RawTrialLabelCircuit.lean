import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialFields

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

abbrev decodeSteps (s : ℕ) := 2*(s+3)+1
abbrev decodeWidth (u s n : ℕ) := cfWidth (s+3) (decodeSteps s)+u+n+retentionBits n+(s+3)+3

def recoveredPairNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n+decodeWidth u s n) :=
  recoveryNet (wordConstant (BitVec.ofNat (decodeWidth u s n) (2^(s+2))))
    (wordConstant (BitVec.ofNat (decodeWidth u s n) (2^n)))
    (toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))) (decodeSteps s)

def trialPairNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n+decodeWidth u s n) :=
  wordMux (wordLt (toWidth (decodeWidth u s n) (rawMode r))
      (wordConstant (BitVec.ofNat (decodeWidth u s n) 2)))
    (recoveredPairNet r)
    ((toWidth (decodeWidth u s n) (rawDen r)).pair (toWidth (decodeWidth u s n) (rawNum r)))
def trialDenNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n) :=
  (trialPairNet r).comp (leftNet (decodeWidth u s n) (decodeWidth u s n))
def trialNumNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n) :=
  (trialPairNet r).comp (rightNet (decodeWidth u s n) (decodeWidth u s n))

lemma recoveredPairNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    ∃ d j : Basis (decodeWidth u s n),
      (recoveredPairNet r).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=
        scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY y.2.1)) (decodeSteps s) := by
  have hw : cfWidth (s+3) (decodeSteps s)≤decodeWidth u s n := by unfold decodeWidth; omega
  have hs : s+2<decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n<decodeWidth u s n := by unfold decodeWidth; omega
  have hQ : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^(s+2)))).eval x)).toNat=2^(s+2) := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]
  have hB : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^n))).eval x)).toNat=2^n := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)]
  have hy : (bitsValue ((toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))).eval x)).toNat =
      Triangular.outputNumber (sampleY y.2.1) := by
    rw [toWidth_value _ hs.le,eval_comp,rawSample_eval r x y h,sampleYNet_eval,bitsValue_toNat]
    rfl
  obtain ⟨d,j,hd,hv⟩ := recoveryNet_value
    (wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^(s+2))))
    (wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^n)))
    (toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))) (decodeSteps s) hw x
    (by rw [hQ]; exact Nat.pow_lt_pow_right (by decide) (by omega))
    (by rw [hy,Triangular.outputNumber,← bitsValue_toNat]
        exact (bitsValue (sampleY y.2.1)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  exact ⟨d,j,hd,by simpa only [hQ,hB,hy] using hv⟩

lemma trialPairNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    ∃ d j : Basis (decodeWidth u s n),
      (trialPairNet r).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=labelPair s n y := by
  have hw : 2≤decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n≤decodeWidth u s n := by unfold decodeWidth; omega
  have h2 : 2<2^(decodeWidth u s n) := lt_of_lt_of_le (by decide : 2<2^2)
    (Nat.pow_le_pow_right (by decide) hw)
  have hm : (wordLt (toWidth (decodeWidth u s n) (rawMode r))
      (wordConstant (BitVec.ofNat (decodeWidth u s n) 2))).eval x 0=
      decide ((bitsValue y.1).toNat<2) := by
    rw [wordLt_eval,toWidth_value _ hw,rawMode_eval r x y h,wordConstant_eval,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]
  by_cases ht : (bitsValue y.1).toNat<2
  · obtain ⟨d,j,hd,hv⟩ := recoveredPairNet_value r x y h
    refine ⟨d,j,?_,?_⟩
    · rw [trialPairNet,wordMux_eval,hm,ite_eq_left (by simpa only [decide_eq_true_eq] using ht),hd]
    · rw [labelPair,ite_eq_left ht]
      exact hv
  · refine ⟨(toWidth (decodeWidth u s n) (rawDen r)).eval x,
      (toWidth (decodeWidth u s n) (rawNum r)).eval x,?_,?_⟩
    · rw [trialPairNet,wordMux_eval,hm,ite_eq_right (by simpa only [decide_eq_true_eq] using ht),eval_pair]
    · rw [toWidth_value _ hn,toWidth_value _ hn,rawDen_eval r x y h,rawNum_eval r x y h,
        labelPair,ite_eq_right ht]

lemma trialDenNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    (bitsValue ((trialDenNet r).eval x)).toNat=(labelPair s n y).1 := by
  obtain ⟨d,j,hd,hv⟩ := trialPairNet_value r x y h
  rw [trialDenNet,eval_comp,hd,leftNet_eval]
  exact congrArg Prod.fst hv
lemma trialNumNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    (bitsValue ((trialNumNet r).eval x)).toNat=(labelPair s n y).2 := by
  obtain ⟨d,j,hd,hv⟩ := trialPairNet_value r x y h
  rw [trialNumNet,eval_comp,hd,rightNet_eval]
  exact congrArg Prod.snd hv

end ExactQuantumFactoring.OrderTrial


end

end OAI
