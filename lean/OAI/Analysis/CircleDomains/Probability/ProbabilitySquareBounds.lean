import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Squared density and finite visit bounds survive probability mixtures.
These estimates allow the fused law to retain the original quantitative bounds. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]

theorem sq_lintegral_le_lintegral_sq_of_probability {f : Z → ℝ≥0∞}
    (hf : AEMeasurable f P) : (∫⁻ z, f z ∂P) ^ 2 ≤ ∫⁻ z, f z ^ 2 ∂P := by
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj hf
    (g := fun _ => 1) measurable_const.aemeasurable
  have hb : (∫⁻ z, f z ∂P) ≤ (∫⁻ z, f z ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    simpa [Pi.mul_apply, ENNReal.rpow_two] using h
  apply (pow_le_pow_left' hb 2).trans_eq
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

theorem finite_square_moment_mixture_bound {I : Type*} (F : Finset I)
    (f : I → Z → ℝ≥0∞) (hf : ∀ i ∈ F, Measurable (f i))
    (E : ℝ≥0∞) (hE : ∀ᵐ z ∂P, ∑ i ∈ F, f i z ^ 2 ≤ E) :
    (∑ i ∈ F, (∫⁻ z, f i z ∂P) ^ 2) ≤ E := by
  calc
    _ ≤ ∑ i ∈ F, ∫⁻ z, f i z ^ 2 ∂P :=
      Finset.sum_le_sum fun i hi => sq_lintegral_le_lintegral_sq_of_probability P (hf i hi).aemeasurable
    _ = ∫⁻ z, ∑ i ∈ F, f i z ^ 2 ∂P :=
      (lintegral_finsetSum F (fun i hi => (hf i hi).pow_const 2)).symm
    _ ≤ ∫⁻ _z, E ∂P := lintegral_mono_ae hE
    _ = E := by simp

theorem density_square_integral_mixture_bound {X : Type*} [MeasurableSpace X]
    (σ : Measure X) [SFinite σ] (g : Z × X → ℝ≥0∞) (hg : Measurable g)
    (E : ℝ≥0∞) (hE : ∀ᵐ z ∂P, ∫⁻ x, g (z, x) ^ 2 ∂σ ≤ E) :
    (∫⁻ x, (∫⁻ z, g (z, x) ∂P) ^ 2 ∂σ) ≤ E := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ z, g (z, x) ^ 2 ∂P ∂σ := by
      apply lintegral_mono
      intro x
      exact sq_lintegral_le_lintegral_sq_of_probability P
        (hg.comp measurable_prodMk_right).aemeasurable
    _ = ∫⁻ z, ∫⁻ x, g (z, x) ^ 2 ∂σ ∂P :=
      lintegral_lintegral_swap ((hg.comp measurable_swap).pow_const 2).aemeasurable
    _ ≤ ∫⁻ _z, E ∂P := lintegral_mono_ae hE
    _ = E := by simp

end CircleDomainRigidity

end

end OAI
