import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm

namespace OAI

/-! Continuous positive mass densities yield the coefficients of the harmonic form. -/

open Set MeasureTheory
namespace DefocusingNLS

private theorem angular_bound (R M : ℝ) (q : ℝ → ℝ)
    (hq : ∀ r ∈ Icc 0 R, ‖q r‖ ≤ M) :
    ∀ᵐ r ∂spectralAngularMeasure R, ‖q r‖ ≤ M := by
  unfold spectralAngularMeasure
  apply (ae_withDensity_iff (by fun_prop)).2
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr _
  exact hq r hr

noncomputable def spectralContinuousWeight (R : ℝ) (q : ℝ → ℝ) (hq : Continuous q)
    (M : ℝ) (hM : ∀ r ∈ Icc 0 R, ‖q r‖ ≤ M) : SpectralHarmonicWeight R where
  density := q
  bound := M
  radial_measurable := hq.aestronglyMeasurable
  angular_measurable := hq.aestronglyMeasurable
  radial_bound := radialPressureMeasure_bound R M q hM
  angular_bound := angular_bound R M q hM

theorem spectralContinuousWeight_lower (R : ℝ) (q : ℝ → ℝ) (hq : Continuous q)
    (M : ℝ) (hM : ∀ r ∈ Icc 0 R, ‖q r‖ ≤ M)
    (c : ℝ) (hc : ∀ r ∈ Icc 0 R, c ≤ q r) :
    (∀ᵐ r ∂radialPressureMeasure R,
      c ≤ (spectralContinuousWeight R q hq M hM).density r) ∧
    (∀ᵐ r ∂spectralAngularMeasure R,
      c ≤ (spectralContinuousWeight R q hq M hM).density r) := by
  constructor
  · unfold radialPressureMeasure
    apply (ae_withDensity_iff (by fun_prop)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr _
    exact hc r hr
  · unfold spectralAngularMeasure
    apply (ae_withDensity_iff (by fun_prop)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr _
    exact hc r hr

theorem spectralPositiveWeight_exists (R : ℝ) (q : ℝ → ℝ) (hq : Continuous q)
    (hp : ∀ r ∈ Icc 0 R, 0 < q r) :
    ∃ w : SpectralHarmonicWeight R, w.density=q ∧ ∃ c : ℝ, 0 < c ∧
      (∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r) ∧
      (∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hq.norm.continuousOn
  have hb : ∀ r ∈ Icc 0 R, ‖q r‖ ≤ M := fun r hr => hM (mem_image_of_mem _ hr)
  obtain ⟨c,hc,hcq⟩ := isCompact_Icc.exists_forall_le' hq.continuousOn hp
  refine ⟨spectralContinuousWeight R q hq M hb,rfl,c,hc,?_⟩
  exact spectralContinuousWeight_lower R q hq M hb c hcq

end DefocusingNLS

end OAI
