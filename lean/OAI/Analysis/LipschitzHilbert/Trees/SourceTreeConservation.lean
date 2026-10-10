import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockDisintegration

namespace OAI

/-! Exact finite conservation for the actual angular partitions. Stopping
at a small-mass cell retains its normalized vertex amount; ineligible tops
retain their original weight. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

theorem sourceBlock_sum_continuing (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (F : τ → ℝ) :
    (∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      ∑ t ∈ g.cellTops tops slope precision cutoff upper c.val, F t) =
    ∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => g.eligible cutoff (precision t) upper), F t := by
  let continuing := (g.cellTops tops slope precision cutoff lower parent).filter
    (fun t => g.eligible cutoff (precision t) upper)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hf := Finset.sum_fiberwise_of_maps_to (s := continuing) (t := cells)
    (fun t ht => Finset.mem_image_of_mem (fun t => g.index upper (slope t)) ht) F
  rw [← Finset.sum_coe_sort] at hf
  calc
    _ = ∑ c : cells, ∑ t ∈ continuing.filter (fun t => g.index upper (slope t) = c.val), F t := by
      apply Finset.sum_congr rfl
      intro c _
      rw [g.sourceBlock_continuing_fiber tops slope precision cutoff hp lower upper hle
        parent c.val c.property]
    _ = _ := hf

theorem sourceBlock_weighted_sum (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (lower upper : ℕ) (hle : lower ≤ upper) (parent : ℤ) (w F : τ → ℝ)
    (hstop : ∀ t ∈ g.cellTops tops slope precision cutoff lower parent,
      ¬g.eligible cutoff (precision t) upper → F t = 1) :
    (∑ t ∈ g.cellTops tops slope precision cutoff lower parent, w t*F t) =
    (∑ t ∈ (g.cellTops tops slope precision cutoff lower parent).filter
      (fun t => ¬g.eligible cutoff (precision t) upper), w t)+
    ∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      ∑ t ∈ g.cellTops tops slope precision cutoff upper c.val, w t*F t := by
  rw [g.sourceBlock_sum_continuing tops slope precision cutoff hp lower upper hle parent]
  rw [← Finset.sum_filter_add_sum_filter_not
    (g.cellTops tops slope precision cutoff lower parent)
    (fun t => ¬g.eligible cutoff (precision t) upper) (fun t => w t*F t)]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
    rw [hstop t ht he,mul_one]
  · simp only [not_not]

section Tree
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
  (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ → ℕ)
  (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p : ℝ) (x : X)

def sourceTreeAmount (j : ℕ) (cell : ℤ) : ℝ :=
  vertexAmount (g.mass tops slope precision cutoff weight (level j) cell x) (A j cell) α p

def sourceTreeDenominator (j : ℕ) (cell : ℤ) : ℝ :=
  sourceNodeDenominator (g.mass tops slope precision cutoff weight (level j) cell x)
    (fun c : g.sourceBlockCells tops slope precision cutoff (level j) (level (j+1)) cell =>
      g.mass tops slope precision cutoff weight (level (j+1)) c.val x)
    (fun c => A (j+1) c.val) α p

def sourceTreeExit (j : ℕ) (top : τ) : ℝ :=
  if g.eligible cutoff (precision top) (level j) then
    g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top))/
      g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x
  else 1

def sourceTreeTail (M : ℝ) : ℕ → ℕ → τ → ℝ
  | 0,j,t => g.sourceTreeExit tops slope precision cutoff weight level A α p x j t
  | n+1,j,t =>
    if g.eligible cutoff (precision t) (level j) ∧
        M < g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope t)) x then
      (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
        (g.index (level j) (slope t))/
       g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
        (g.index (level j) (slope t)))*
      sourceTreeTail M n (j+1) t
    else g.sourceTreeExit tops slope precision cutoff weight level A α p x j t

variable {g tops slope precision cutoff weight level A α p x}

theorem sourceTreeTail_ineligible (M : ℝ) (n j : ℕ) (t : τ)
    (he : ¬g.eligible cutoff (precision t) (level j)) :
    g.sourceTreeTail tops slope precision cutoff weight level A α p x M n j t = 1 := by
  cases n <;> simp [sourceTreeTail,sourceTreeExit,he]

theorem sourceTreeExit_sum (hw : ∀ t x, 0 < weight t x) (j : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level j) cell).Nonempty) :
    (∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
      weight t x*g.sourceTreeExit tops slope precision cutoff weight level A α p x j t) =
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell := by
  have hm : 0 < g.mass tops slope precision cutoff weight (level j) cell x := by
    obtain ⟨t,ht⟩ := hne
    exact g.mass_pos_of_member tops slope precision cutoff weight hw (level j) cell x ht
  calc
    _ = ∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell, weight t x*
        (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell/
          g.mass tops slope precision cutoff weight (level j) cell x) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
      simp only [sourceTreeExit,ite_eq_left ht'.2.2,ht'.2.1]
    _ = _ := by
      rw [← Finset.sum_mul]
      change g.mass tops slope precision cutoff weight (level j) cell x*(_/_) = _
      exact mul_div_cancel₀ _ hm.ne'

/-- A finite stopped expansion exactly recovers the original node amount.
No transition or path-probability identity is assumed. -/
theorem sourceTreeTail_sum (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hlevel : Monotone level) (M : ℝ)
    (n j : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level j) cell).Nonempty) :
    (∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
      weight t x*g.sourceTreeTail tops slope precision cutoff weight level A α p x M n j t) =
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell := by
  induction n generalizing j cell with
  | zero => exact sourceTreeExit_sum hw j cell hne
  | succ n ih =>
    have hm : 0 < g.mass tops slope precision cutoff weight (level j) cell x := by
      obtain ⟨t,ht⟩ := hne
      exact g.mass_pos_of_member tops slope precision cutoff weight hw (level j) cell x ht
    by_cases hactive : M < g.mass tops slope precision cutoff weight (level j) cell x
    · have hden : 0 < g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell := by
        unfold sourceTreeDenominator
        apply sourceNodeDenominator_pos hm
        intro c
        exact g.mass_nonnegative tops slope precision cutoff weight
          (fun t x => (hw t x).le) (level (j+1)) c.val x
      calc
        _ = (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell/
            g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell)*
            ∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
              weight t x*g.sourceTreeTail tops slope precision cutoff weight level A α p x M n (j+1) t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
          simp only [sourceTreeTail,ht'.2.1,ht'.2.2,true_and,ite_eq_left hactive]
          ring
        _ = (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j cell/
            g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell)*
            g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j cell := by
          congr 1
          rw [g.sourceBlock_weighted_sum tops slope precision cutoff hp (level j) (level (j+1))
            (hlevel (Nat.le_succ j)) cell (fun t => weight t x)
            (g.sourceTreeTail tops slope precision cutoff weight level A α p x M n (j+1))
            (fun t _ he => sourceTreeTail_ineligible M n (j+1) t he)]
          unfold sourceTreeDenominator
          rw [g.sourceBlock_denominator_conservation tops slope precision cutoff weight hp
            (level j) (level (j+1)) (hlevel (Nat.le_succ j)) cell x]
          congr 1
          apply Finset.sum_congr rfl
          intro c _
          exact ih (j+1) c.val (g.sourceBlockCells_nonempty_child tops slope precision cutoff
            (level j) (level (j+1)) cell c)
        _ = _ := div_mul_cancel₀ _ hden.ne'
    · calc
        _ = ∑ t ∈ g.cellTops tops slope precision cutoff (level j) cell,
            weight t x*g.sourceTreeExit tops slope precision cutoff weight level A α p x j t := by
          apply Finset.sum_congr rfl
          intro t ht
          have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
          simp only [sourceTreeTail,ht'.2.1,hactive,and_false,ite_false]
        _ = _ := sourceTreeExit_sum hw j cell hne

end Tree
end LipschitzHilbert.AngularGrid

end

end OAI
