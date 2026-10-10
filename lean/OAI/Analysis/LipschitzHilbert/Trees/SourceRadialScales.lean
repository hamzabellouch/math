import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryGeometry

namespace OAI

/-! The radial eligible sets shrink in both angular radius and precision.
This is the scale inclusion used in the boundary-loss telescoping argument. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem nearbyEligibleTops_subset_of_scale (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    {i j : ℕ} (hij : i ≤ j) {r R : ℝ} (hr : r ≤ R) (s : ℝ) :
    g.nearbyEligibleTops tops slope precision cutoff j r s ⊆
      g.nearbyEligibleTops tops slope precision cutoff i R s := by
  intro t ht
  obtain ⟨htt,he,hd⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr
    ⟨htt,g.eligible_of_le (hp t htt) hij he,hd.trans_le hr⟩

theorem nearbyEligibleMass_le_of_scale (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    {i j : ℕ} (hij : i ≤ j) {r R : ℝ} (hr : r ≤ R) (s : ℝ) (x : X) :
    g.nearbyEligibleMass tops slope precision cutoff weight j r s x ≤
      g.nearbyEligibleMass tops slope precision cutoff weight i R s x :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (g.nearbyEligibleTops_subset_of_scale tops slope precision cutoff hp hij hr s)
    (fun t _ _ => hw t x)

theorem width_add (g : AngularGrid) (i j : ℕ) :
    g.width (i+j) = g.width i*(g.branching:ℝ)⁻¹^j := by
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  unfold width
  rw [pow_add,inv_pow]
  field_simp

theorem nearbyEligibleMass_scale_crossing (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (i r : ℕ) (epsilon b s : ℝ)
    (hcross : epsilon*(g.branching:ℝ)⁻¹^r ≤ b) (x : X) :
    g.nearbyEligibleMass tops slope precision cutoff weight (i+r)
        (epsilon*g.width (i+r)) s x ≤
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) s x := by
  apply g.nearbyEligibleMass_le_of_scale tops slope precision cutoff weight hp hw
    (Nat.le_add_right i r) _ s x
  rw [g.width_add i r]
  nlinarith [mul_le_mul_of_nonneg_right hcross (g.width_pos i).le]

end LipschitzHilbert.AngularGrid

end

end OAI
