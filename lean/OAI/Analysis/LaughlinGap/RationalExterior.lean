import Mathlib
import OAI.Analysis.LaughlinGap.RationalFourCoefficients
import OAI.Analysis.LaughlinGap.RationalRows

namespace OAI

/-! Rational Exterior. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def wordSign {n : ℕ} : List (Fin n) → ℚ
  | [] => 1
  | j :: js => if j ∈ js then 0 else
    (-1:ℚ)^(js.toFinset.filter (fun k => k < j)).card * wordSign js

lemma word_empty (n : ℕ) (js : List (Fin n)) (x : Hilbert n) :
    word js x ∅ = (wordSign js : ℂ) * x js.toFinset := by
  induction js generalizing x with
  | nil => simp [wordSign,word]
  | cons j js ih =>
    rw [word_cons,Module.End.mul_apply,ih]
    by_cases h : j ∈ js
    · simp [wordSign,h,transition_apply,List.mem_toFinset]
    · simp only [wordSign,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,
        transition_apply,List.mem_toFinset,h,decide_false,ite_true,flip_of_not_mem
          (show j ∉ js.toFinset by simpa using h),List.toFinset_cons,sign,ite_false]
      ring

lemma word_adjoint_vacuum {n : ℕ} (js : List (Fin n)) :
    (word js).adjoint (vacuum n) = (wordSign js : ℂ) • EuclideanSpace.single js.toFinset 1 := by
  apply ext_inner_right ℂ
  intro x
  simp only [LinearMap.adjoint_inner_left,inner_vacuum_left,word_empty,inner_smul_left,
    EuclideanSpace.inner_single_left,map_ratCast]
  simp

end LaughlinGap.Occupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma limitingPair_roots {p x y : ℕ} (h : x+y=p+1) :
    limitingExteriorPairCoefficient p x y = ((x:ℝ)-(y:ℝ))*rootFactorial p /
      (Real.sqrt 2^p*rootFactorial x*rootFactorial y) := by
  have he : Real.sqrt ((2:ℝ)^p) = Real.sqrt 2^p :=
    (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr (sqrt_natpow_sq (by norm_num) p).symm
  unfold limitingExteriorPairCoefficient
  rw [ite_eq_left h,Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2^p * x.factorial),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2^p),he]
  dsimp [rootFactorial]
  ring

abbrev FourTerm (D : ℕ) :=
  (Σ n : Fin (D+1), Fin ((n.val+1)/2) × Fin ((D-n.val+2)/2))

def fourTermP {D : ℕ} (a : FourTerm D) : ℕ := D-a.1.val

def fourTermJ {D : ℕ} (a : FourTerm D) : ℕ := a.2.1.val

def fourTermK {D : ℕ} (a : FourTerm D) : ℕ := a.1.val-a.2.1.val

def fourTermX {D : ℕ} (a : FourTerm D) : ℕ := a.2.2.val

def fourTermY {D : ℕ} (a : FourTerm D) : ℕ := D-a.1.val+1-a.2.2.val

lemma fourTerm_balance {D : ℕ} (a : FourTerm D) :
    fourTermX a+fourTermY a=fourTermP a+1 ∧
    fourTermP a+fourTermJ a+fourTermK a=D ∧
    fourTermX a<fourTermY a ∧ fourTermJ a<fourTermK a := by
  have hn := a.1.isLt
  have hj := a.2.1.isLt
  have hx := a.2.2.isLt
  dsimp [fourTermX,fourTermY,fourTermP,fourTermJ,fourTermK] at *
  omega

def fourTermLabels {D : ℕ} (hD : D ≤ 23) (a : FourTerm D) : List (Fin 25) :=
  [⟨fourTermX a,by have := fourTerm_balance a; omega⟩,
   ⟨fourTermY a,by have := fourTerm_balance a; omega⟩,
   ⟨fourTermJ a,by have := fourTerm_balance a; omega⟩,
   ⟨fourTermK a,by have := fourTerm_balance a; omega⟩]

def fourTermCoefficient (D r : ℕ) (a : FourTerm D) : ℚ :=
  vCoefficient D D r (fourTermP a) (fourTermJ a) (fourTermK a) * (2:ℚ)^((r+1)/2) *
    ((fourTermX a:ℚ)-(fourTermY a:ℚ)) * (fourTermP a).factorial *
      (fourTermJ a).factorial * (fourTermK a).factorial / (2:ℚ)^D

lemma four_pair_normalization {D : ℕ} (r : FourCopy D) (a : FourTerm D) :
    fourBodyCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) *
      limitingExteriorPairCoefficient (fourTermP a) (fourTermX a) (fourTermY a) =
      copyNormalization D r.val.val * (fourTermCoefficient D r.val.val a:ℝ) /
        (rootFactorial (fourTermX a)*rootFactorial (fourTermY a)*
          rootFactorial (fourTermJ a)*rootFactorial (fourTermK a)) := by
  rw [← show fourWeightCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) =
      fourBodyCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) by
      simp [fourWeightCoefficientStar]]
  rw [fourWeightCoefficientStar_rational (Nat.le_of_lt_succ r.val.isLt) r.property,
    limitingPair_roots (fourTerm_balance a).1,Nat.sub_self,rootFactorial_zero,mul_one]
  unfold fourTermCoefficient
  push_cast
  field_simp [rootFactorial_ne_zero,Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
  simp only [rootFactorial_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
