import OAI.Geometry.NodalSets.Coefficients.RoundSupportedCorrection
import OAI.Geometry.NodalSets.Elliptic.RealCoordinateEllipticLemmas

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem round_simplicity_coordinate_perturbation
    (u zeta : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ zeta)
    (lam : ℝ) (hlam : lam ≠ 0) :
    let alpha := fun x ↦ zeta x*u x^2
    let beta := simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam
    ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
    tsupport alpha ⊆ tsupport zeta ∧ tsupport beta ⊆ tsupport zeta ∧
    (∀ x, beta x = -lam⁻¹ *
      (u x * Yau.weightedDiv roundCoordDensity (fun y i ↦ zeta y*roundCoordGradient u y i) x +
        2*zeta x*roundCoordFactor x*
          (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2)) ∧
    ∀ x, Yau.weightedDiv roundCoordDensity (fun y i ↦ alpha y*roundCoordGradient u y i) x +
      lam*beta x*u x = 0 := by
  intro alpha beta
  have hV := roundCoordGradient_smooth u hu
  refine ⟨hz.mul (hu.pow 2),simplicityDensityPerturbation_smooth _ _ _ _ _
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') hu hz hV,
    ?_,simplicityDensityPerturbation_tsupport_subset _ _ _ _ _,?_,?_⟩
  · exact tsupport_mul_subset_left
  · intro x
    dsimp [beta,simplicityDensityPerturbation]
    rw [roundCoordGradient_pairing]
    ring
  · intro x
    exact simplicity_coordinate_cancellation _ _ _ _ _ hlam x
      (roundCoordDensity_smooth.differentiable (by simp) x) (roundCoordDensity_pos x).ne'
      (hu.differentiable (by simp) x) (hz.differentiable (by simp) x)
      (fun i ↦ ((contDiff_pi.mp hV) i).differentiable (by simp) x)

end
end Yau.Target

end OAI
