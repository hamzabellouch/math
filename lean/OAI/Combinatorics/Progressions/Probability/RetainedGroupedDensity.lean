import OAI.Combinatorics.Progressions.Probability.DensityMixtureAELaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem retained_density_flatten {W Q : Type*} [MeasurableSpace W] [Fintype Q]
    (I : Q → Type*) [∀ q, Fintype (I q)] (μ : Measure W) [SFinite μ]
    (f : W × (∀ q, I q → ℝ) → ℝ) :
    (realDensityMeasure (μ.prod volume) f).map
      (fun p => (p.1, (sigmaAxisCoordinates I).symm p.2)) =
      realDensityMeasure (μ.prod volume) (fun p => f (p.1, sigmaAxisCoordinates I p.2)) := by
  let e : W × (∀ q, I q → ℝ) ≃ᵐ W × ((Σ q, I q) → ℝ) :=
    (MeasurableEquiv.refl W).prodCongr (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).prod (sigmaAxisCoordinates_symm_measurePreserving I)
  change (realDensityMeasure (μ.prod volume) f).map e = _
  rw [realDensityMeasure_map_equiv, he.map_eq]
  rfl

end Erdos3

end

end OAI
