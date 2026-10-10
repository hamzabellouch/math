import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336

theorem standardGaussian_sqrt_hasLaw (v : ℝ≥0) :
    HasLaw (fun z : ℝ => Real.sqrt v * z) (gaussianReal 0 v) (gaussianReal 0 1) := by
  have h := gaussianReal_const_mul
    (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  have hv : (⟨(Real.sqrt (v : ℝ)) ^ 2, sq_nonneg _⟩ : ℝ≥0) = v := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt v.coe_nonneg
  simp only [mul_zero, mul_one, id_eq] at h
  convert h using 1
  congr 1
  exact hv.symm

theorem gaussian_absolute_moment_scaling (v : ℝ≥0) (k : ℕ) :
    (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 v) =
      (Real.sqrt (v : ℝ)) ^ k * (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 1) := by
  rw [← (standardGaussian_sqrt_hasLaw v).integral_comp (f := fun z : ℝ => |z| ^ k)
    (by fun_prop)]
  simp only [Function.comp_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

theorem standardGaussian_absolute_first_moment_le_one :
    (∫ z : ℝ, |z| ∂gaussianReal 0 1) ≤ 1 := by
  have hint : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num) |>.abs
  have hsint : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := by
    simpa only [id_eq, Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow' (p := 2)
  have hsq : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    simp only [variance_eq_integral aemeasurable_id, id_eq, integral_id_gaussianReal, sub_zero] at h
    simpa only [id_eq, sub_zero, NNReal.coe_one] using h
  have hle := integral_mono (hint.const_mul 2) (hsint.add (integrable_const 1))
    (fun z : ℝ => show 2 * |z| ≤ z ^ 2 + 1 by nlinarith [sq_nonneg (|z| - 1), sq_abs z])
  simp only [Pi.add_apply] at hle
  rw [integral_const_mul, integral_add hsint (integrable_const 1), hsq, integral_const] at hle
  norm_num at hle
  linarith

theorem gaussian_absolute_first_moment_le_sqrt (v : ℝ≥0) :
    (∫ z : ℝ, |z| ∂gaussianReal 0 v) ≤ Real.sqrt v := by
  have h := gaussian_absolute_moment_scaling v 1
  simp only [pow_one] at h
  rw [h]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left standardGaussian_absolute_first_moment_le_one (Real.sqrt_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {Q : Ω → ℝ} {v : ℝ≥0}

theorem gaussian_hasLaw_integrable_abs_pow (hQ : HasLaw Q (gaussianReal 0 v) P) (k : ℕ) :
    Integrable (fun ω => |Q ω| ^ k) P := by
  let := hQ.isProbabilityMeasure
  simpa only [Real.norm_eq_abs] using
    (hQ.hasGaussianLaw.memLp (p := (k : ℝ≥0∞)) (by simp)).integrable_norm_pow' (p := k)

theorem gaussian_hasLaw_absolute_moment (hQ : HasLaw Q (gaussianReal 0 v) P) (k : ℕ) :
    (∫ ω, |Q ω| ^ k ∂P) =
      (Real.sqrt (v : ℝ)) ^ k * (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 1) := by
  calc
    (∫ ω, |Q ω| ^ k ∂P) = (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 v) :=
      hQ.integral_comp (f := fun z : ℝ => |z| ^ k) (by fun_prop)
    _ = _ := gaussian_absolute_moment_scaling v k

theorem gaussian_hasLaw_second_moment (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, (Q ω) ^ 2 ∂P) = (v : ℝ) := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  simp only [variance_eq_integral aemeasurable_id, id_eq, integral_id_gaussianReal, sub_zero] at h
  calc
    (∫ ω, (Q ω) ^ 2 ∂P) = (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 v) :=
      hQ.integral_comp (f := fun z : ℝ => z ^ 2) (by fun_prop)
    _ = _ := h

theorem gaussian_hasLaw_absolute_first_moment_le (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, |Q ω| ∂P) ≤ Real.sqrt v := by
  calc
    (∫ ω, |Q ω| ∂P) = (∫ z : ℝ, |z| ∂gaussianReal 0 v) :=
      hQ.integral_comp (f := fun z : ℝ => |z|) (by fun_prop)
    _ ≤ _ := gaussian_absolute_first_moment_le_sqrt v

theorem gaussian_setIntegral_absolute_moment (hQ : HasLaw Q (gaussianReal 0 v) P)
    {A : Set Ω} (hA : MeasurableSet A)
    (hind : IndepFun (A.indicator (fun _ : Ω => (1 : ℝ))) Q P) (k : ℕ) :
    (∫ ω in A, |Q ω| ^ k ∂P) =
      P.real A * ((Real.sqrt (v : ℝ)) ^ k *
        (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 1)) := by
  have hZ : AEStronglyMeasurable (fun ω => |Q ω| ^ k) P :=
    (gaussian_hasLaw_integrable_abs_pow hQ k).aestronglyMeasurable
  have hi' := hind.comp measurable_id (by fun_prop : Measurable (fun z : ℝ => |z| ^ k))
  have hi := hi'.integral_fun_mul_eq_mul_integral
    ((measurable_const.indicator hA).aestronglyMeasurable) hZ
  have heq : (fun ω => id (A.indicator (fun _ : Ω => (1 : ℝ)) ω) * |Q ω| ^ k) =
      A.indicator (fun ω => |Q ω| ^ k) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  change (∫ ω, id (A.indicator (fun _ : Ω => (1 : ℝ)) ω) * |Q ω| ^ k ∂P) = _ at hi
  rw [heq, integral_indicator hA] at hi
  simpa only [Function.comp_apply, id_eq, integral_indicator hA, integral_const,
    smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ, gaussian_hasLaw_absolute_moment hQ k] using hi

theorem gaussian_independent_weighted_second_moment
    (hQ : HasLaw Q (gaussianReal 0 v) P) {K : Ω → ℂ}
    (hK : AEMeasurable K P) (hind : IndepFun K Q P) :
    (∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P) =
      (∫ ω, K ω ∂P) * (v : ℂ) := by
  have hi := hind.integral_fun_comp_mul_comp hK hQ.aemeasurable
    (f := id) (g := fun z : ℝ => (z : ℂ) ^ 2) (by fun_prop) (by fun_prop)
  have hmoment : (∫ ω, (Q ω : ℂ) ^ 2 ∂P) = (v : ℂ) := by
    simp only [← Complex.ofReal_pow, integral_complex_ofReal,
      gaussian_hasLaw_second_moment hQ]
  simpa only [id_eq, hmoment] using hi

end Problem336

end

end OAI
