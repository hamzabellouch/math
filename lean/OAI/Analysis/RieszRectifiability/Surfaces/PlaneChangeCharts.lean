import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.CoveredProjectionCharts
import OAI.Analysis.RieszRectifiability.Flatness.PlaneChangeCoverage
import OAI.Analysis.RieszRectifiability.Projections.ProjectionConeTransfer

namespace OAI

/-!
# Reparameterizing a chart over a nearby plane

Small normal slope and a small change of projection leave a positive disk
covered in the new plane. The projection inverse defines a chart on this disk,
with quantitative Lipschitz bounds for the chart and its normal component.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_chart_over_nearby_plane {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (a : P) (ρ : ℝ) (hρ : 0 < ρ)
    (g : closedBall a ρ → Ambient d) (L α : ℝ≥0)
    (hsmall : (L : ℝ) + (α : ℝ) ≤ 1 / 4)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ)) :
    let b := Q.orthogonalProjectionOnto (g ⟨a, mem_closedBall_self hρ.le⟩)
    let r := ρ - ((L : ℝ) + (α : ℝ)) * ρ
    let D := closedBall b r
    0 < r ∧ ∃ h : D → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (2 * (L + α))
        (fun u => (Qᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ Set.range g ∧ Q.orthogonalProjectionOnto (h u) = u.val) ∧
      Set.range h = Set.range g ∩ Q.orthogonalProjectionOnto ⁻¹' D := by
  let b := Q.orthogonalProjectionOnto (g ⟨a, mem_closedBall_self hρ.le⟩)
  let r := ρ - ((L : ℝ) + (α : ℝ)) * ρ
  let D := closedBall b r
  have hr : 0 < r := by
    have hm := mul_le_mul_of_nonneg_right hsmall hρ.le
    dsimp only [r]
    linarith
  have hcontract : L + α < 1 := by
    have h : ((L + α : ℝ≥0) : ℝ) < 1 := by
      rw [NNReal.coe_add]
      linarith
    exact_mod_cast h
  have hcover : D ⊆ Q.orthogonalProjectionOnto '' Set.range g :=
    graph_covers_changed_plane_disk P Q a ρ hρ.le g L α hcontract hcoordinates hnormal hop
  have hstar (u : closedBall a ρ) : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hcoordinates u)
  have hcone : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (L : ℝ) * dist (P.starProjection x) (P.starProjection y) := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    have h := hnormal.dist_le_mul u v
    rw [dist_eq_norm, ← map_sub] at h
    rw [hstar u, hstar v]
    exact h
  have hconeQ : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        ((2 * (L + α) : ℝ≥0) : ℝ) * dist (Q.starProjection x) (Q.starProjection y) := by
    intro x hx y hy
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add] using!
      projection_cone_transfer P Q (Set.range g) L α (hsmall.trans (by norm_num)) hop hcone x hx y hy
  obtain ⟨h, hLip, hnLip, hcoords, hrange⟩ :=
    exists_chart_on_covered_projection Q (Set.range g) (2 * (L + α)) D hcover hconeQ
  have hL : 1 + 2 * (L + α) ≤ (2 : ℝ≥0) := by
    have hh : ((1 + 2 * (L + α) : ℝ≥0) : ℝ) ≤ 2 := by
      rw [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add]
      linarith
    exact_mod_cast hh
  exact ⟨hr, h, hLip.weaken hL, hnLip, hcoords, hrange⟩

end

end RieszRectifiability

end OAI
