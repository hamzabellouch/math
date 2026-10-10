import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.InitialAffineCharts

namespace OAI

/-!
# Input charts on fitting planes

A small bilateral plane error bounds the offset of a support center from the fitting
plane. The located affine chart then gives the input disk, with constant normal component,
exact projected range, and image contained in the ambient ball of radius `3 * r`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_fitting_plane_input_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (c : Ambient d) (hc : c ∈ μ.support)
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hεsmall : ε ≤ 1 / 2048)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hfit : bilateralPlaneError μ c (1024 * r) S < ε) :
    ∃ g : closedBall (S.direction.orthogonalProjectionOnto c) ((5 / 2 : ℝ) * r) → Ambient d,
      LipschitzWith 2 g ∧
      LipschitzWith 0 (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)) ∧
      (∀ u, g u ∈ S ∧ S.direction.orthogonalProjectionOnto (g u) = u.val ∧
        g u ∈ closedBall c (3 * r)) ∧
      Set.range g = (S : Set (Ambient d)) ∩ S.direction.orthogonalProjectionOnto ⁻¹'
        closedBall (S.direction.orthogonalProjectionOnto c) ((5 / 2 : ℝ) * r) := by
  have hcenter := (bilateralPlaneError_lt_pointwise μ ⟨c, hc⟩ c (1024 * r) ε
    (by positivity) S hS hfit).1 c (mem_ball_self (by positivity)) hc
  have hoffset : infDist c (S : Set (Ambient d)) ≤ r / 2 := by
    have hm := mul_le_mul_of_nonneg_right hεsmall (show 0 ≤ 1024 * r by positivity)
    linarith
  obtain ⟨g, hLip, hnLip, hcoords, hrange⟩ :=
    exists_located_affine_plane_disk_chart S hS.1 c ((5 / 2 : ℝ) * r)
  refine ⟨g, hLip.weaken (by norm_num), hnLip, ?_, hrange⟩
  intro u
  refine ⟨(hcoords u).1, (hcoords u).2.1, ?_⟩
  have hloc := (hcoords u).2.2
  change dist (g u) c ≤ 3 * r
  linarith

end

end RieszRectifiability

end OAI
