import Mathlib
import OAI.Computability.QuantumFactoring.SamplerDecodeCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

def rawMode {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k 2 :=
  r.comp (leftNet 2 (OrderSample.width u (s+2)+guessWidth n))
def rawSample {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (OrderSample.width u (s+2)) :=
  (r.comp (rightNet 2 (OrderSample.width u (s+2)+guessWidth n))).comp
    (leftNet (OrderSample.width u (s+2)) (guessWidth n))
def rawGuesses {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (guessWidth n) :=
  (r.comp (rightNet 2 (OrderSample.width u (s+2)+guessWidth n))).comp
    (rightNet (OrderSample.width u (s+2)) (guessWidth n))
def rawDen {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (rawGuesses r).comp (leftNet n (n+(n+retentionBits n)))
def rawNum {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  ((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp (leftNet n (n+retentionBits n))
def rawResidue {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp
    (rightNet n (n+retentionBits n))).comp (leftNet n (retentionBits n))
def rawCoin {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (retentionBits n) :=
  (((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp
    (rightNet n (n+retentionBits n))).comp (rightNet n (retentionBits n))

lemma rawMode_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawMode r).eval x=y.1 := by
  simp only [rawMode,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval]
lemma rawSample_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawSample r).eval x=y.2.1 := by
  simp only [rawSample,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawGuesses_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawGuesses r).eval x=guessLayout n y.2.2 := by
  simp only [rawGuesses,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,rightNet_eval]
lemma rawDen_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawDen r).eval x=y.2.2.1 := by
  rw [rawDen,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval]
lemma rawNum_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawNum r).eval x=y.2.2.2.1 := by
  rw [rawNum,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawResidue_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawResidue r).eval x=y.2.2.2.2.1 := by
  rw [rawResidue,eval_comp,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawCoin_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawCoin r).eval x=y.2.2.2.2.2 := by
  rw [rawCoin,eval_comp,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,rightNet_eval]

def toWidth {k u : ℕ} (w : ℕ) (a : BooleanNetwork k u) : BooleanNetwork k w :=
  a.comp (resizeWord u w)
lemma toWidth_value {k u w : ℕ} (a : BooleanNetwork k u) (h : u≤w) (x : Basis k) :
    (bitsValue ((toWidth w a).eval x)).toNat=(bitsValue (a.eval x)).toNat := by
  rw [toWidth,eval_comp,resizeWord_toNat h]
lemma toWidth_count {k u w : ℕ} (a : BooleanNetwork k u) :
    (toWidth w a).net.count≤a.net.count+w := by
  rw [toWidth,count_comp]
  exact Nat.add_le_add_left (resizeWord_count u w) _

end ExactQuantumFactoring.OrderTrial


end

end OAI
