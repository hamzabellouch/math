import OAI.Geometry.RCD.Harmonic.EuclideanQuadraticDefect
import OAI.Geometry.RCD.Sobolev.BoundaryTorsionProfile
import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds

namespace OAI

/-! # Compact interior torsion tests with a quadratic core -/

open Set Metric MeasureTheory
open scoped ContDiff
noncomputable section
namespace RegularPointCoordinates

def euclideanInteriorTorsion (n : ℕ) (R δ : ℝ) (x : Euclidean n) : ℝ :=
  δ*boundaryTorsionProfile (euclideanQuadraticDefect n R x/δ)

theorem euclideanInteriorTorsion_smooth (n : ℕ) (R δ : ℝ) :
    ContDiff ℝ ∞ (euclideanInteriorTorsion n R δ) :=
  contDiff_const.mul (boundaryTorsionProfile_smooth.comp
    ((euclideanQuadraticDefect_smooth n R).div_const δ))

theorem euclideanInteriorTorsion_nonneg (n : ℕ) (R : ℝ) {δ : ℝ} (hδ : 0≤δ)
    (x : Euclidean n) : 0≤euclideanInteriorTorsion n R δ x :=
  mul_nonneg hδ (boundaryTorsionProfile_nonneg _)

theorem euclideanInteriorTorsion_support (n : ℕ) (R : ℝ) {δ : ℝ}
    (hδ : 0<δ) (hδR : δ<R^2) :
    tsupport (euclideanInteriorTorsion n R δ)⊆closedBall 0 (Real.sqrt (R^2-δ)) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hgt : Real.sqrt (R^2-δ)<‖x‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hn
  have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg _) (norm_nonneg x)).mpr hgt
  rw [Real.sq_sqrt (by linarith : 0≤R^2-δ)] at hsq
  have hq : euclideanQuadraticDefect n R x/δ≤1 := by
    apply (div_le_one hδ).mpr
    dsimp only [euclideanQuadraticDefect]
    linarith
  exact hx (by
    change δ*boundaryTorsionProfile (euclideanQuadraticDefect n R x/δ)=0
    rw [boundaryTorsionProfile_zero hq,mul_zero])

theorem euclideanInteriorTorsion_test {n : ℕ} {R δ : ℝ}
    (hR : 0<R) (hδ : 0<δ) (hδR : δ<R^2) :
    InteriorSmoothTest n R (euclideanInteriorTorsion n R δ) := by
  have hs := euclideanInteriorTorsion_support n R hδ hδR
  have hroot : Real.sqrt (R^2-δ)<R := by
    nlinarith [Real.sq_sqrt (by linarith : 0≤R^2-δ),Real.sqrt_nonneg (R^2-δ)]
  exact ⟨euclideanInteriorTorsion_smooth n R δ,
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (closedBall_subset_ball hroot)⟩

end RegularPointCoordinates

end

end OAI
