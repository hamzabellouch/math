import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory

lemma charFun_sq_intervalIntegrable (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    IntervalIntegrable (fun r => ‖charFun μ r‖^2) volume a b :=
  (continuous_charFun.norm.pow 2).intervalIntegrable a b

lemma charFun_sq_symmetric_band (μ : Measure ℝ) [IsFiniteMeasure μ] {A : ℝ} (hA : 0≤A) :
    (∫ r in Icc (-A) A, ‖charFun μ r‖^2)=2*∫ r in Icc 0 A, ‖charFun μ r‖^2 := by
  have he := intervalIntegral.integral_comp_neg (a:=0) (b:=A) (fun r => ‖charFun μ r‖^2)
  simp only [charFun_neg,Complex.norm_conj,neg_zero] at he
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (charFun_sq_intervalIntegrable μ (-A) 0) (charFun_sq_intervalIntegrable μ 0 A)
  rw [← he] at ha
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -A≤A),
    ← ha,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hA]
  ring

lemma distance_dyadic_band_decomposition (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a t : ℕ} (hat : a≤t) :
    (∫ r in Icc (-((2:ℝ)^t)) ((2:ℝ)^t), ‖charFun μ r‖^2)=
      (∫ r in Icc (-((2:ℝ)^a)) ((2:ℝ)^a), ‖charFun μ r‖^2)+
      2*∑ j∈Finset.Ico a t, ∫ r in Icc ((2:ℝ)^j) ((2:ℝ)^(j+1)), ‖charFun μ r‖^2 := by
  have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f:=fun r => ‖charFun μ r‖^2) (μ:=volume) (a:=fun j => (2:ℝ)^j) hat
    (fun j _ => charFun_sq_intervalIntegrable μ _ _)
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (charFun_sq_intervalIntegrable μ 0 ((2:ℝ)^a))
    (charFun_sq_intervalIntegrable μ ((2:ℝ)^a) ((2:ℝ)^t))
  have hj (j : ℕ) : (2:ℝ)^j≤(2:ℝ)^(j+1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
  simp_rw [intervalIntegral.integral_of_le (hj _),← integral_Icc_eq_integral_Ioc] at ht
  rw [charFun_sq_symmetric_band μ (by positivity),charFun_sq_symmetric_band μ (by positivity),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2^t),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2^a),
    ← ha,← ht]
  ring

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
