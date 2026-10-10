import OAI.Analysis.KadisonKastler.BilateralBlockApproximations
import OAI.Analysis.KadisonKastler.BilateralHalfSpaces

namespace OAI

/-! Unitary-cocycle invariant L2 functions on the bilateral walk are constant. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem bilateral_twisted_invariant_constant (σ : G →* unitary (K →L[ℂ] K))
    (f : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) :
    f = hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, f ω ∂bilateralWalkLaw G) := by
  apply bilateral_L2_constant_of_half_measurable
  · apply aestronglyMeasurable_of_L2_approximations cylinderEvents_le_pi
    intro ε hε
    obtain ⟨m, g, hg, hfg⟩ := exists_symmetricWindow_L2_approximation f (by positivity : 0 < ε / 4)
    refine ⟨bilateralPositiveApprox σ m g, bilateralPositiveApprox_coordinate σ m g, ?_⟩
    rw [dist_eq_norm]
    have he := bilateralPositiveApprox_error σ m f g ht hg
    linarith
  · apply aestronglyMeasurable_of_L2_approximations cylinderEvents_le_pi
    intro ε hε
    obtain ⟨m, g, hg, hfg⟩ := exists_symmetricWindow_L2_approximation f (by positivity : 0 < ε / 4)
    refine ⟨bilateralNegativeApprox σ m g, bilateralNegativeApprox_coordinate σ m g, ?_⟩
    rw [dist_eq_norm]
    have he := bilateralNegativeApprox_error σ m f g ht hg
    linarith

end

end KadisonKastler

end OAI
