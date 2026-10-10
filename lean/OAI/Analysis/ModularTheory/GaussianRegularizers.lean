import OAI.Analysis.ModularTheory.TranslationWeight
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! Concrete Gaussian regularizers in the modular core. Their square weight
is finite and they converge strongly to the identity. No trace identity is
assumed in this construction. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness

def modularGaussian (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => (Real.exp (-t ^ 2 / (n + 1)) : ℂ)) (by fun_prop) 1 (by
      intro t
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))

@[simp] lemma modularGaussian_apply (n : ℕ) (t : ℝ) :
    modularGaussian n t = (Real.exp (-t ^ 2 / (n + 1)) : ℂ) := rfl

lemma modularGaussian_norm_le (n : ℕ) (t : ℝ) : ‖modularGaussian n t‖ ≤ 1 := by
  simp only [modularGaussian_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

lemma modularGaussian_tendsto (t : ℝ) :
    Tendsto (fun n => modularGaussian n t) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => -t ^ 2 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (-t ^ 2)).comp (tendsto_add_atTop_nat 1)
  have he := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_exp.continuousAt.tendsto.comp h)
  simpa only [Function.comp_def, Real.exp_zero, Complex.ofReal_one, modularGaussian_apply] using he

lemma modularGaussian_integrable (n : ℕ) :
    Integrable (fun t : ℝ => ‖modularGaussian n t‖ ^ 2 * Real.exp (2 * Real.pi * t)) := by
  have hp : (0 : ℝ) < 2 / (n + 1 : ℝ) := by positivity
  have hi := integrable_cexp_quadratic
    (b := ((2 / (n + 1 : ℝ) : ℝ) : ℂ)) (by
      change (0 : ℝ) < 2 / (n + 1 : ℝ)
      exact hp)
    ((2 * Real.pi : ℝ) : ℂ) 0
  convert hi.re using 1
  ext t
  simp only [modularGaussian_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), add_zero]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_add]
  change _ = (Complex.exp ((-(2 / (n + 1 : ℝ)) * t ^ 2 + 2 * Real.pi * t : ℝ) : ℂ)).re
  rw [Complex.exp_ofReal_re, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

def modularGaussianRegularizer (n : ℕ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  modularTranslationCalculus (modularGaussian n)

lemma modularGaussianRegularizer_mem (n : ℕ) :
    modularGaussianRegularizer (H := H) n ∈ modularCrossedProduct (volume : Measure ℝ) S :=
  modularTranslationCalculus_mem S _

lemma modularGaussianRegularizer_finite (n : ℕ) :
    modularCoreSquareWeight S (modularGaussianRegularizer n) < ⊤ :=
  (modularTranslationCalculus_weight_le S _ (modularGaussian_integrable n)).trans_lt
    ENNReal.ofReal_lt_top

lemma modularGaussianRegularizer_strong (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularGaussianRegularizer n f) atTop (𝓝 f) := by
  have h := vectorLpRepresentation_strong modularGaussian (fun _ => 1)
    (by fun_prop) 1 zero_le_one modularGaussian_norm_le (by simp)
    modularGaussian_tendsto (𝓕 f)
  have he : boundedVectorLp (H := H) volume (fun _ => 1) (by fun_prop) 1
      (by simp) = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [boundedVectorLp_ae volume (fun _ => 1) (by fun_prop) 1 (by simp) v]
      with t ht
    change _ = v t
    simpa only [one_smul] using ht
  have hf := (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.continuousAt.tendsto.comp h
  simp only [he, one_apply_eq_self] at hf
  change Tendsto (fun n => modularGaussianRegularizer n f) atTop (𝓝 (𝓕⁻ (𝓕 f))) at hf
  simpa only [fourierInv_fourier_eq] using hf

/-- The finite-square-weight left ideal is strongly dense in the actual
core. This is a semifiniteness step, separate from tracial symmetry. -/
theorem modularCore_finiteWeight_approximation
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S) :
    ∃ R : ℕ → (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)),
      (∀ n, R n ∈ modularCrossedProduct (volume : Measure ℝ) S) ∧
      (∀ n, modularCoreSquareWeight S (R n) < ⊤) ∧
      ∀ f, Tendsto (fun n => R n f) atTop (𝓝 (T f)) := by
  refine ⟨fun n => T * modularGaussianRegularizer n, ?_, ?_, ?_⟩
  · intro n
    exact mul_mem hT (modularGaussianRegularizer_mem S n)
  · intro n
    exact (modularCoreSquareWeight_mul_le S T (modularGaussianRegularizer n)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (modularGaussianRegularizer_finite S n))
  · intro f
    exact T.continuous.continuousAt.tendsto.comp (modularGaussianRegularizer_strong f)

end WeakPureInfiniteness

end

end OAI
