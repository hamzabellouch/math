import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockConservation

namespace OAI

/-! Distribute each true child amount among its original top weights.
This is the finite transition identity used to attach one terminal path
to each top, including tops that stop inside a source block. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem sourceBlock_disintegrate_children (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (x : X) (F : ℤ → ℝ) :
    (∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent, F c.val) =
    ∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => g.eligible cutoff (precision t) upper),
      weight t x/g.mass tops slope precision cutoff weight upper (g.index upper (slope t)) x*
        F (g.index upper (slope t)) := by
  let continuing := (g.cellTops tops slope precision cutoff lower parent).filter
    (fun t => g.eligible cutoff (precision t) upper)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hf := Finset.sum_fiberwise_of_maps_to (s := continuing) (t := cells)
    (fun t ht => Finset.mem_image_of_mem (fun t => g.index upper (slope t)) ht)
    (fun t => weight t x/g.mass tops slope precision cutoff weight upper (g.index upper (slope t)) x*
      F (g.index upper (slope t)))
  rw [← Finset.sum_coe_sort] at hf
  calc
    _ = ∑ c : cells, ∑ t ∈ continuing.filter (fun t => g.index upper (slope t) = c.val),
        weight t x/g.mass tops slope precision cutoff weight upper (g.index upper (slope t)) x*
          F (g.index upper (slope t)) := by
      apply Finset.sum_congr rfl
      intro c _
      have hm : 0 < g.mass tops slope precision cutoff weight upper c.val x :=
        g.mass_pos_of_member tops slope precision cutoff weight hw upper c.val x
          (g.sourceBlockTop_mem_child tops slope precision cutoff lower upper parent c)
      have hs : (∑ t ∈ continuing.filter (fun t => g.index upper (slope t) = c.val),
          weight t x/g.mass tops slope precision cutoff weight upper (g.index upper (slope t)) x*
            F (g.index upper (slope t))) =
          (∑ t ∈ continuing.filter (fun t => g.index upper (slope t) = c.val), weight t x)/
            g.mass tops slope precision cutoff weight upper c.val x*F c.val := by
        rw [Finset.sum_div,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      rw [hs,g.sourceBlock_continuing_fiber tops slope precision cutoff hp lower upper hle
        parent c.val c.property]
      change F c.val = g.mass tops slope precision cutoff weight upper c.val x/
        g.mass tops slope precision cutoff weight upper c.val x*F c.val
      rw [div_self hm.ne',one_mul]
    _ = _ := hf

theorem sourceBlock_disintegrate_denominator {κ : Type} [Fintype κ]
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (x : X)
    (A : ℤ → EuclideanSpace ℂ κ) (α p : ℝ) :
    sourceNodeDenominator (g.mass tops slope precision cutoff weight lower parent x)
      (fun c : g.sourceBlockCells tops slope precision cutoff lower upper parent =>
        g.mass tops slope precision cutoff weight upper c.val x) (fun c => A c.val) α p =
    ∑ t ∈ g.cellTops tops slope precision cutoff lower parent, weight t x*
      (if g.eligible cutoff (precision t) upper then
        vertexAmount (g.mass tops slope precision cutoff weight upper (g.index upper (slope t)) x)
          (A (g.index upper (slope t))) α p/
            g.mass tops slope precision cutoff weight upper (g.index upper (slope t)) x
       else 1) := by
  rw [g.sourceBlock_denominator_conservation tops slope precision cutoff weight hp
    lower upper hle parent x (fun c => A c.val) α p,
    g.sourceBlock_disintegrate_children tops slope precision cutoff weight hp hw lower upper hle
      parent x (fun c => vertexAmount (g.mass tops slope precision cutoff weight upper c x) (A c) α p)]
  simp only [Finset.sum_filter,mul_ite,mul_one]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> ring

end LipschitzHilbert.AngularGrid

end

end OAI
