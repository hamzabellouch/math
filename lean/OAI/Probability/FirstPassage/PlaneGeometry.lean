import OAI.Probability.FirstPassage.Target
import OAI.Probability.FirstPassage.LocalDifferentiability
import Mathlib.Tactic.FinCases

namespace OAI

namespace PlanarFPP

noncomputable def direction (b : ℝ) : Plane := WithLp.toLp 2 ![1, b]
noncomputable def transverseUnit : Plane := WithLp.toLp 2 ![0, 1]
noncomputable def xCoord : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
noncomputable def rCoord (b : ℝ) : Plane →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 - b • xCoord

@[simp] theorem xCoord_apply (z : Plane) : xCoord z = z 0 := rfl
@[simp] theorem rCoord_apply (b : ℝ) (z : Plane) : rCoord b z = z 1 - b * z 0 := rfl
@[simp] theorem xCoord_direction (b : ℝ) : xCoord (direction b) = 1 := rfl
@[simp] theorem rCoord_direction (b : ℝ) : rCoord b (direction b) = 0 := by
  simp [rCoord_apply, direction]

theorem plane_reconstruction (b : ℝ) (z : Plane) :
    z = xCoord z • direction b + rCoord b z • transverseUnit := by
  ext i
  fin_cases i <;> simp [direction, transverseUnit, PiLp.add_apply, PiLp.smul_apply]
  ring

theorem norm_positive_homogeneous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z := by
  intro t ht z
  rw [hμ.homogeneous, abs_of_nonneg ht]

theorem planar_extreme_supports (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    let φ := fun t : ℝ => μ (direction b + t • transverseUnit)
    (∀ z, coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (leftSlope φ) z ≤ μ z) ∧
    (∀ z, coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (rightSlope φ) z ≤ μ z) ∧
    coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (leftSlope φ) (direction b) = μ (direction b) ∧
    coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (rightSlope φ) (direction b) = μ (direction b) := by
  exact extreme_supports μ xCoord.toLinearMap (rCoord b).toLinearMap (direction b)
    transverseUnit hμ.triangle (norm_positive_homogeneous μ hμ)
    (xCoord_direction b) (rCoord_direction b) (plane_reconstruction b)

theorem planar_differentiability_of_no_corner (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (b : ℝ)
    (heq : leftSlope (fun t : ℝ => μ (direction b + t • transverseUnit)) =
      rightSlope (fun t : ℝ => μ (direction b + t • transverseUnit))) :
    ∃ ℓ : Plane →L[ℝ] ℝ, HasFDerivAt μ ℓ (direction b) := by
  exact differentiableAt_of_equal_extreme_slopes μ xCoord (rCoord b) (direction b)
    transverseUnit hμ.triangle (norm_positive_homogeneous μ hμ)
    (xCoord_direction b) (rCoord_direction b) (plane_reconstruction b) heq

end PlanarFPP

end OAI
