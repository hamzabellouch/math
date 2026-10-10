import OAI.Analysis.LipschitzHilbert.Trees.SourceRadialMassBounds
import OAI.Analysis.LipschitzHilbert.Trees.BoundaryDepthCrossing

namespace OAI

/-! The finite sum of literal radial log ratios is bounded by geometric
boundary depth, including the terminal eligibility cutoff. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem radial_log_ratio_sum_le_depth (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon b : ℝ) (hepsilon : 0 < epsilon) (hb : 0 < b)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    (∑ i ∈ Finset.range N, Real.log
      (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)) ≤
      geometricBoundaryDepth epsilon (g.branching:ℝ)⁻¹ b *
        Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  have hG : (1:ℝ) < g.branching := by
    exact_mod_cast (show 1 < g.branching by have := g.branching_ge_two; omega)
  have hinv0 : 0 ≤ (g.branching:ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hinv1 : (g.branching:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hG
  apply boundary_loss_le_geometricDepth
    (g.radialPathLogMass tops slope precision cutoff weight epsilon N top x) _ N
    hepsilon.le hinv0 hinv1 hb
    (fun i => (g.radialPathLogMass_bounds tops slope precision cutoff weight hw epsilon hepsilon
      N top htop he x i).1)
    (fun i => (g.radialPathLogMass_bounds tops slope precision cutoff weight hw epsilon hepsilon
      N top htop he x i).2)
  intro r hcross i hi
  let A := g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x
  let B := g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x
  have hw0 := hw top x
  have hA := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
    (fun t x => (hw t x).le) i top htop (he i hi) (mul_pos hepsilon (g.width_pos i)) x
  have hB := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
    (fun t x => (hw t x).le) i top htop (he i hi) (mul_pos hb (g.width_pos i)) x
  have hA0 : 0 < A := hw0.trans_le hA
  have hB0 : 0 < B := hw0.trans_le hB
  change Real.log (A/B) ≤ _
  by_cases hnext : i+r < N
  · let C := g.nearbyEligibleMass tops slope precision cutoff weight (i+r)
      (epsilon*g.width (i+r)) (slope top) x
    have hC := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) (i+r) top htop (he (i+r) hnext)
      (mul_pos hepsilon (g.width_pos (i+r))) x
    have hC0 : 0 < C := hw0.trans_le hC
    have hCB : C ≤ B := g.nearbyEligibleMass_scale_crossing tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) i r epsilon b (slope top) hcross x
    have hlog := Real.log_le_log hC0 hCB
    simp only [radialPathLogMass,ite_eq_left hi,ite_eq_left hnext]
    change Real.log (A/B) ≤ Real.log (A/weight top x)-Real.log (C/weight top x)
    rw [Real.log_div hA0.ne' hB0.ne',Real.log_div hA0.ne' hw0.ne',
      Real.log_div hC0.ne' hw0.ne']
    linarith
  · have hlog := Real.log_le_log hw0 hB
    simp only [radialPathLogMass,ite_eq_left hi,ite_eq_right hnext,sub_zero]
    change Real.log (A/B) ≤ Real.log (A/weight top x)
    rw [Real.log_div hA0.ne' hB0.ne',Real.log_div hA0.ne' hw0.ne']
    linarith

end LipschitzHilbert.AngularGrid

end

end OAI
