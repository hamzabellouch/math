import OAI.Geometry.RCD.Metric.SignedWeightedRadon

namespace OAI

/-! # Localizing Radon–Nikodym identities of full signed measures -/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

theorem signed_rnDeriv_restrict (ν : SignedMeasure X) {S : Set X} (hS : MeasurableSet S) :
    SignedMeasure.rnDeriv (ν.restrict S) μ =ᵐ[μ] S.indicator (ν.rnDeriv μ) := by
  let σ := ν.toJordanDecomposition.posPart
  let τ := ν.toJordanDecomposition.negPart
  have he : ν.restrict S=(σ.restrict S).toSignedMeasure-(τ.restrict S).toSignedMeasure := by
    conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
    rw [JordanDecomposition.toSignedMeasure,VectorMeasure.restrict_sub,
      Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ S hS,
      Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ S hS]
  rw [he]
  filter_upwards [SignedMeasure.rnDeriv_sub (σ.restrict S).toSignedMeasure (τ.restrict S).toSignedMeasure μ,
    signed_rnDeriv_toSignedMeasure μ (σ.restrict S),signed_rnDeriv_toSignedMeasure μ (τ.restrict S),
    Measure.rnDeriv_restrict σ μ hS,Measure.rnDeriv_restrict τ μ hS] with x hs hσ hτ hσS hτS
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hσ,hτ,hσS,hτS]
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx,SignedMeasure.rnDeriv_def]
    rfl
  · simp only [indicator_of_notMem hx,ENNReal.toReal_zero,sub_self]

theorem signed_rnDeriv_eq_on_of_restrict_eq {ν τ : SignedMeasure X} {S : Set X}
    (hS : MeasurableSet S) (h : ν.restrict S=τ.restrict S) :
    ν.rnDeriv μ =ᵐ[μ.restrict S] τ.rnDeriv μ := by
  filter_upwards [ae_restrict_of_ae (signed_rnDeriv_restrict μ ν hS),
    ae_restrict_of_ae (signed_rnDeriv_restrict μ τ hS),ae_restrict_mem hS] with x hν hτ hx
  rw [h] at hν
  rw [indicator_of_mem hx] at hν hτ
  exact hν.symm.trans hτ

omit [SigmaFinite μ] in
theorem signed_rnDeriv_density {f : X → ℝ} (hf : Integrable f μ) :
    SignedMeasure.rnDeriv (μ.withDensityᵥ f) μ =ᵐ[μ] f := by
  exact (SignedMeasure.eq_rnDeriv (s := (μ.withDensityᵥ f : SignedMeasure X)) 0 f hf
    VectorMeasure.MutuallySingular.zero_left (by rw [zero_add])).symm

end RegularPointCoordinates

end

end OAI
