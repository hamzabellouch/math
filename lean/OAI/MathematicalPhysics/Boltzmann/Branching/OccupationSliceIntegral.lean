import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseSourceMeasure

namespace OAI

/-! # A spacetime occupation measure disintegrated into phase slices -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem occupation_slice_lintegral {F : ℝ × Phase → ℝ} (hF : Measurable F)
    (s b : ℝ) {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂(positiveDensityMeasure volume F).restrict (Prod.fst ⁻¹' Ioc s b)) =
      ∫⁻ t in Ioc s b, ∫⁻ p, f (t,p) ∂phaseSlice F t := by
  have he : Prod.fst ⁻¹' Ioc s b = Ioc s b ×ˢ (univ : Set Phase) := by ext; simp
  rw [positiveDensityMeasure,restrict_withDensity (measurable_fst measurableSet_Ioc),
    Measure.volume_eq_prod,he,← Measure.restrict_prod_eq_prod_univ,
    lintegral_withDensity_eq_lintegral_mul _ hF.ennreal_ofReal hf,
    lintegral_prod _ (hF.ennreal_ofReal.mul hf).aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [phaseSlice,positiveDensityMeasure]
  exact (lintegral_withDensity_eq_lintegral_mul _
    (f := fun p => ENNReal.ofReal (F (t,p)))
    (g := fun p => f (t,p))
    (hF.ennreal_ofReal.comp (measurable_const.prodMk measurable_id))
    (hf.comp (measurable_const.prodMk measurable_id))).symm

end BoltzmannNonuniqueness.WeakTime

end

end OAI
