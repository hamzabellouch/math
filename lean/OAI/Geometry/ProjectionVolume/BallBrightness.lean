import OAI.Geometry.ProjectionVolume.Brightness
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

namespace OAI

open Set Metric MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace Paper092

noncomputable def euclideanUnitBallVolume (d : ℕ) : ℝ :=
  (volume (closedBall (0 : Euclidean d) 1)).toReal

theorem projection_image_closedBall {d : ℕ} (u : Euclidean d) (R : ℝ) :
    (normalHyperplane u).orthogonalProjectionOnto '' closedBall (0 : Euclidean d) R =
      closedBall (0 : normalHyperplane u) R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_closedBall_zero_iff.mpr
    exact ((normalHyperplane u).norm_orthogonalProjectionOnto_apply_le x).trans
      (mem_closedBall_zero_iff.mp hx)
  · intro hy
    refine ⟨y.val, ?_, (normalHyperplane u).orthogonalProjectionOnto_mem_subspace_eq_self y⟩
    simpa only [mem_closedBall, dist_zero_right, Submodule.norm_coe] using hy

theorem projectionVolume_closedBall_real {d : ℕ} (hd : 2 ≤ d)
    (u : Euclidean d) (hu : u ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    (projectionVolume (closedBall (0 : Euclidean d) R) u).toReal =
      euclideanUnitBallVolume (d - 1) * R ^ (d - 1) := by
  let : Nontrivial (normalHyperplane u) := Module.nontrivial_of_finrank_pos (by
    rw [normalHyperplane_finrank u hu]
    omega)
  let : Nontrivial (Euclidean (d - 1)) := Module.nontrivial_of_finrank_pos (by
    rw [finrank_euclideanSpace_fin]
    omega)
  have hunit : (volume (closedBall (0 : normalHyperplane u) 1)) =
      volume (closedBall (0 : Euclidean (d - 1)) 1) := by
    rw [InnerProductSpace.volume_closedBall, InnerProductSpace.volume_closedBall,
      normalHyperplane_finrank u hu, finrank_euclideanSpace_fin]
  have hball : R • closedBall (0 : normalHyperplane u) 1 = closedBall 0 R := by
    rw [_root_.smul_closedBall _ _ zero_le_one, smul_zero, Real.norm_eq_abs, abs_of_nonneg hR, mul_one]
  unfold projectionVolume
  rw [projection_image_closedBall, ← hball, Measure.addHaar_smul,
    normalHyperplane_finrank u hu, abs_pow, abs_of_nonneg hR,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR _), hunit]
  exact mul_comm _ _

theorem brightness_closedBall {d : ℕ} (hd : 2 ≤ d) (R : ℝ) (hR : 0 ≤ R)
    (u : Euclidean d) :
    brightness (closedBall (0 : Euclidean d) R) u =
      ‖u‖ * (euclideanUnitBallVolume (d - 1) * R ^ (d - 1)) := by
  by_cases hu : u = 0
  · simp [hu, brightness]
  · unfold brightness
    rw [projectionVolume_closedBall_real hd u hu R hR]

theorem brightness_le_ball_bound {d : ℕ} (hd : 2 ≤ d) {K : Set (Euclidean d)}
    {R : ℝ} (hR : 0 ≤ R) (hK : K ⊆ closedBall 0 R) (u : Euclidean d) :
    brightness K u ≤ ‖u‖ * (euclideanUnitBallVolume (d - 1) * R ^ (d - 1)) := by
  exact (brightness_mono hK (isCompact_closedBall _ _) u).trans_eq
    (brightness_closedBall hd R hR u)

theorem ball_subset_projectionBody {d : ℕ} (hd : 2 ≤ d) {K : Set (Euclidean d)}
    (hK : IsCompact K) {a : ℝ} (ha : 0 ≤ a) (hball : closedBall 0 a ⊆ K) :
    closedBall (0 : Euclidean d) (euclideanUnitBallVolume (d - 1) * a ^ (d - 1)) ⊆
      projectionBody K := by
  intro y hy u
  calc
    ⟪u, y⟫ ≤ ‖u‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖u‖ * (euclideanUnitBallVolume (d - 1) * a ^ (d - 1)) :=
      mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hy) (norm_nonneg u)
    _ = brightness (closedBall (0 : Euclidean d) a) u := (brightness_closedBall hd a ha u).symm
    _ ≤ brightness K u := brightness_mono hball hK u

theorem projectionBody_subset_ball {d : ℕ} (hd : 2 ≤ d) {K : Set (Euclidean d)}
    {R : ℝ} (hR : 0 ≤ R) (hK : K ⊆ closedBall 0 R) :
    projectionBody K ⊆
      closedBall (0 : Euclidean d) (euclideanUnitBallVolume (d - 1) * R ^ (d - 1)) := by
  intro y hy
  have hc : 0 ≤ euclideanUnitBallVolume (d - 1) * R ^ (d - 1) := by
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hR _)
  have h := (hy y).trans (brightness_le_ball_bound hd hR hK y)
  rw [real_inner_self_eq_norm_sq] at h
  apply mem_closedBall_zero_iff.mpr
  nlinarith [norm_nonneg y]

end Paper092

end OAI
