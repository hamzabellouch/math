import OAI.Analysis.LipschitzHilbert.Trees.SourceNodeRatio
import OAI.Analysis.LipschitzHilbert.Phase.AngularConservation

namespace OAI

/-! Exact conservation on one source block, including the top weights
that stop before its upper endpoint. This is the row decomposition of
the original node denominator used by the finite path flow. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem sourceBlock_continuing_fiber (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent cell : ℤ)
    (hc : cell ∈ g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    ((g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => g.eligible cutoff (precision t) upper)).filter
        (fun t => g.index upper (slope t) = cell) =
      g.cellTops tops slope precision cutoff upper cell := by
  have hrep := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨cell,hc⟩
  ext t
  constructor
  · intro ht
    obtain ⟨hcont,hindex⟩ := Finset.mem_filter.mp ht
    obtain ⟨hparent,he⟩ := Finset.mem_filter.mp hcont
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨((g.mem_cellTops _ _ _ _ _ _ _).mp hparent).1,hindex,he⟩
  · intro ht
    have htop := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
    have hlo := g.eligible_of_le (hp t htop.1) hle htop.2.2
    have hindex : g.index lower (slope t) = parent := by
      have hi := g.index_eq_of_le hle (htop.2.1.trans hrep.2.2.2.symm)
      exact hi.trans hrep.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop.1,hindex,hlo⟩,htop.2.2⟩,htop.2.1⟩

theorem sum_sourceBlock_child_mass (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (lower upper : ℕ) (hle : lower ≤ upper)
    (parent : ℤ) (x : X) :
    (∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.mass tops slope precision cutoff weight upper c.val x) =
    ∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => g.eligible cutoff (precision t) upper), weight t x := by
  let continuing := (g.cellTops tops slope precision cutoff lower parent).filter
    (fun t => g.eligible cutoff (precision t) upper)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hf := Finset.sum_fiberwise_of_maps_to (s := continuing) (t := cells)
    (fun t ht => Finset.mem_image_of_mem (fun t => g.index upper (slope t)) ht)
    (fun t => weight t x)
  rw [← Finset.sum_coe_sort] at hf
  calc
    _ = ∑ c : cells, ∑ t ∈ continuing.filter (fun t => g.index upper (slope t) = c.val),
        weight t x := by
      apply Finset.sum_congr rfl
      intro c _
      rw [show continuing.filter (fun t => g.index upper (slope t) = c.val) =
        g.cellTops tops slope precision cutoff upper c.val from
        g.sourceBlock_continuing_fiber tops slope precision cutoff hp lower upper hle parent c.val c.property]
      rfl
    _ = _ := hf

/-- The stopping mass is an actual sum of original top weights. -/
theorem sourceBlock_mass_conservation (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (lower upper : ℕ) (hle : lower ≤ upper)
    (parent : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight lower parent x =
    (∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => ¬g.eligible cutoff (precision t) upper), weight t x)+
    ∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.mass tops slope precision cutoff weight upper c.val x := by
  rw [g.sum_sourceBlock_child_mass tops slope precision cutoff weight hp lower upper hle parent x]
  simpa only [not_not,mass] using (Finset.sum_filter_add_sum_filter_not
    (g.cellTops tops slope precision cutoff lower parent)
    (fun t => ¬g.eligible cutoff (precision t) upper) (fun t => weight t x)).symm

/-- Exact source denominator as continuing child amounts plus stopped
top weights; no mass is lost by grouping several angular levels. -/
theorem sourceBlock_denominator_conservation {κ : Type} [Fintype κ]
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (x : X)
    (A : g.sourceBlockCells tops slope precision cutoff lower upper parent → EuclideanSpace ℂ κ)
    (α p : ℝ) :
    sourceNodeDenominator (g.mass tops slope precision cutoff weight lower parent x)
      (fun c => g.mass tops slope precision cutoff weight upper c.val x) A α p =
    (∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => ¬g.eligible cutoff (precision t) upper), weight t x)+
    ∑ c, vertexAmount (g.mass tops slope precision cutoff weight upper c.val x) (A c) α p := by
  rw [sourceNodeDenominator_stopped_mass]
  have hm := g.sourceBlock_mass_conservation tops slope precision cutoff weight hp
    lower upper hle parent x
  rw [hm]
  ring

end LipschitzHilbert.AngularGrid

end

end OAI
