import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionTubeLocation
import OAI.Analysis.RieszRectifiability.Surfaces.ContinuousPerturbedBallCoverage

namespace OAI

/-!
# Inner projection coverage of continuous charts

A chart whose projected displacement is small covers an inner ball in the plane direction.
Bounds on the chart height and the base point's distance to the plane keep the covering
points inside the required ambient ball.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem continuous_chart_inner_projection_coverage {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (c : S.direction) (R : ℝ) (H : closedBall c R → Ambient d)
    (hH : Continuous H) (surface : Set (Ambient d)) (hRange : Set.range H ⊆ surface)
    (p : Ambient d) (ρ e a b : ℝ) (hρ : 0 ≤ ρ)
    (hroom : dist (S.direction.orthogonalProjectionOnto p) c + 2 * ρ ≤ R)
    (hDisp : ∀ u, dist (S.direction.orthogonalProjectionOnto (H u)) u.val ≤ e)
    (hHeight : ∀ u, infDist (H u) (S : Set (Ambient d)) ≤ a)
    (hBase : infDist p (S : Set (Ambient d)) ≤ b)
    (he : e ≤ ρ) (hab : a + b ≤ ρ) :
    closedBall (S.direction.orthogonalProjectionOnto p) ρ ⊆
      S.direction.orthogonalProjectionOnto '' (surface ∩ closedBall p (2 * ρ)) := by
  let P := S.direction
  have hsub : closedBall (P.orthogonalProjectionOnto p) (2 * ρ) ⊆ closedBall c R := by
    intro u hu
    have ht := dist_triangle u (P.orthogonalProjectionOnto p) c
    have hud : dist u (P.orthogonalProjectionOnto p) ≤ 2 * ρ := hu
    change dist u c ≤ R
    linarith
  let j : closedBall (P.orthogonalProjectionOnto p) (2 * ρ) → closedBall c R :=
    fun u => ⟨u.val, hsub u.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hCont : Continuous (fun u => P.orthogonalProjectionOnto (H (j u))) :=
    P.orthogonalProjectionOnto.continuous.comp (hH.comp hj)
  intro z hz
  have hz' : z ∈ closedBall (P.orthogonalProjectionOnto p) (2 * ρ - e) := by
    have hzd : dist z (P.orthogonalProjectionOnto p) ≤ ρ := hz
    change dist z (P.orthogonalProjectionOnto p) ≤ _
    linarith
  obtain ⟨u, hu⟩ := closedBall_covered_by_continuous_perturbation
    (P.orthogonalProjectionOnto p) (2 * ρ) e (by positivity)
    (fun u => P.orthogonalProjectionOnto (H (j u))) hCont (fun u => hDisp (j u)) hz'
  change P.orthogonalProjectionOnto (H (j u)) = z at hu
  refine ⟨H (j u), ⟨hRange ⟨j u, rfl⟩, ?_⟩, hu⟩
  have hprojected : dist (P.starProjection (H (j u))) (P.starProjection p) ≤ ρ := by
    change dist (P.orthogonalProjectionOnto (H (j u))) (P.orthogonalProjectionOnto p) ≤ ρ
    rw [hu]
    exact hz
  have ht := dist_le_projection_add_plane_distances S hS (H (j u)) p
  change dist (H (j u)) p ≤ 2 * ρ
  linarith [hHeight (j u)]

end

end RieszRectifiability

end OAI
