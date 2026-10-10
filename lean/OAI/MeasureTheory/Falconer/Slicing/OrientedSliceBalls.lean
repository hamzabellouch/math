import OAI.MeasureTheory.Falconer.Slicing.OrientedSlice
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedBalls

namespace OAI

/-! # Closed-ball bounds in the oriented coordinates of the actual slice -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem oriented_point_ball_eq (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (μ : Measure (Space d)) (c : Space m) (r : ℝ) :
    μ {x | dist (e (V.orthogonalProjectionOnto x)) c < r} =
      (Measure.map V.starProjection μ) (ball (e.symm c : Space d) r) := by
  rw [Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  congr 1
  ext x
  change dist (e (V.orthogonalProjectionOnto x)) c < r ↔
    dist (V.orthogonalProjectionOnto x) (e.symm c) < r
  rw [← e.dist_map (V.orthogonalProjectionOnto x) (e.symm c),e.apply_symm_apply]

theorem oriented_direction_ball_eq (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (ν : Measure (Sphere d)) (c : Space m) (r : ℝ) :
    ν {w | dist (normalize (e (V.orthogonalProjectionOnto (w:Space d)))) c < r} =
      (Measure.map (fun w : Sphere d => normalize (V.starProjection (w:Space d))) ν)
        (ball (e.symm c : Space d) r) := by
  rw [Measure.map_apply (show Measurable
    (fun w : Sphere d => normalize (V.starProjection (w:Space d))) from
      by unfold NormedSpace.normalize; fun_prop) measurableSet_ball]
  congr 1
  ext w
  change dist (normalize (e (V.orthogonalProjectionOnto (w:Space d)))) c < r ↔
    dist (normalize (V.orthogonalProjectionOnto (w:Space d))) (e.symm c) < r
  rw [← slice_isometry_normalize V e]
  rw [← e.dist_map (normalize (V.orthogonalProjectionOnto (w:Space d))) (e.symm c),e.apply_symm_apply]

theorem gaussian_pruned_oriented_point_closed_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K) (hspos : 0 < s)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 4*s+K*((h:ℝ)*(2*δ)) ≤ r i) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤ TP i := by
  have hss : s < 2*s := by linarith
  calc
    _ ≤ ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} :=
      measure_mono (show {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ⊆
        {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} from
          fun x hx => lt_of_le_of_lt hx hss)
    _ = _ := oriented_point_ball_eq (gaussianRowMap A).ker e _ c (2*s)
    _ ≤ _ := gaussian_pruned_point_kernel_ball μ A z δ r TP i hK hbound (by linarith) _

theorem gaussian_pruned_oriented_direction_closed_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K) (hspos : 0 < s)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 4*s+4*(K*((h:ℝ)*δ)) ≤ r i) (c : Space m) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ≤ TD i := by
  have hss : s < 2*s := by linarith
  calc
    _ ≤ ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c < 2*s} :=
      measure_mono (show {w : Sphere d | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ⊆
        {w : Sphere d | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c < 2*s} from
          fun w hw => lt_of_le_of_lt hw hss)
    _ = _ := oriented_direction_ball_eq (gaussianRowMap A).ker e _ c (2*s)
    _ ≤ _ := gaussian_pruned_direction_kernel_ball ν A δ r TD M i hK hbound hsmall (by linarith) _

end Falconer

end OAI
