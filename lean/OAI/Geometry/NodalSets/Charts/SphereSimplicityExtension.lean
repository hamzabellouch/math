import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientIncrementBounds
import OAI.Geometry.NodalSets.Elliptic.SimplicityRoundCoordinatePerturbation

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem sphere_simplicity_extension (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ) (hlam : lam ≠ 0)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (hzQ : tsupport zeta ⊆ Q) :
    ∃ a b : Base → ℝ,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
      tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
      (∀ x, a (seedSphereFromCoord x) = zeta x*(u (seedSphereFromCoord x))^2) ∧
      (∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
        (fun y ↦ u (seedSphereFromCoord y)) zeta
        (roundCoordGradient (fun y ↦ u (seedSphereFromCoord y))) lam x) ∧
      ∀ x, Yau.weightedDiv roundCoordDensity
        (fun y i ↦ a (seedSphereFromCoord y)*
          roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
        lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0 := by
  obtain ⟨ha,hb,haS,hbS,hformula,hcancel⟩ := round_simplicity_coordinate_perturbation
    (fun y ↦ u (seedSphereFromCoord y)) zeta (seed_scalar_pullback_smooth u hu) hz lam hlam
  obtain ⟨a,has,haQ,haval⟩ := seed_chart_scalar_extension _ ha
    (hQ.of_isClosed_subset isClosed_closure (haS.trans hzQ))
  obtain ⟨b,hbs,hbQ,hbval⟩ := seed_chart_scalar_extension _ hb
    (hQ.of_isClosed_subset isClosed_closure (hbS.trans hzQ))
  refine ⟨a,b,has,hbs,haQ.trans (image_mono (haS.trans hzQ)),
    hbQ.trans (image_mono (hbS.trans hzQ)),haval,hbval,?_⟩
  simpa only [haval,hbval] using hcancel

end
end Yau.Target

end OAI
