import OAI.GroupTheory.PolycyclicRecognition.Algebra.DensityTranslationLimits

namespace OAI

/-! # Errors for density-weighted occupation observables -/

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology

/-- The total variation estimate needed after changing sampling density. -/
theorem norm_integral_density_sub_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ σ f : X → ℝ) (hρ : Integrable ρ μ) (hσ : Integrable σ μ)
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x, ρ x * f x ∂μ) - ∫ x, σ x * f x ∂μ‖ ≤
      C * ∫ x, |ρ x - σ x| ∂μ := by
  have hiρ := hρ.mul_bdd hf (Eventually.of_forall hb)
  have hiσ := hσ.mul_bdd hf (Eventually.of_forall hb)
  rw [← integral_sub hiρ hiσ]
  have hdom : Integrable (fun x => C * |ρ x - σ x|) μ :=
    (hρ.sub hσ).abs.const_mul C
  have hbound (x : X) : ‖ρ x * f x - σ x * f x‖ ≤ C * |ρ x - σ x| := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hh := norm_integral_le_of_norm_le hdom (Eventually.of_forall hbound)
  simpa only [Pi.sub_apply, integral_const_mul] using hh

/-- Small measure-preserving coordinate translations change every bounded
scale-dependent observable by a vanishing amount under a fixed density. -/
theorem density_occupation_error_tendsto_zero
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (ρ : X → ℝ) (hc : Continuous ρ) (hi : Integrable ρ μ)
    (hp : ∀ x, 0 ≤ ρ x)
    {l : Filter ι} [l.IsCountablyGenerated]
    (e : ι → X ≃ᵐ X) (he : ∀ i, MeasurePreserving (e i) μ μ)
    (hlim : ∀ x, Tendsto (fun i => (e i).symm x) l (𝓝 x))
    (f : ι → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i x, ‖f i x‖ ≤ C) :
    Tendsto (fun i => (∫ x, ρ x * f i (e i x) ∂μ) - ∫ x, ρ x * f i x ∂μ)
      l (𝓝 0) := by
  have hpres (i : ι) : MeasurePreserving (e i).symm μ μ := (he i).symm (e i)
  have hL := density_translation_l1_tendsto_zero μ ρ hc hi hp
    (fun i => (e i).symm) hpres hlim
  have hbound (i : ι) :
      ‖(∫ x, ρ x * f i (e i x) ∂μ) - ∫ x, ρ x * f i x ∂μ‖ ≤
        C * ∫ x, |ρ ((e i).symm x) - ρ x| ∂μ := by
    have hchange : (∫ x, ρ x * f i (e i x) ∂μ) =
        ∫ x, ρ ((e i).symm x) * f i x ∂μ := by
      have hh := (he i).integral_comp' (fun x => ρ ((e i).symm x) * f i x)
      simpa only [MeasurableEquiv.symm_apply_apply] using hh
    rw [hchange]
    exact norm_integral_density_sub_le μ (fun x => ρ ((e i).symm x)) ρ (f i)
      ((hpres i).integrable_comp_of_integrable hi) hi (hf i) hC (hb i)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun i => C * ∫ x, |ρ ((e i).symm x) - ρ x| ∂μ) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hL
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall hbound) ht

end PolycyclicRecognition

end OAI
