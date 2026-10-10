import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Delaying one moved coordinate by one color

When a moved coordinate has final color `i`, replacing it by `i.succ` removes
exactly that coordinate from the prefixSet at cut `i`. Every other cut stays
unchanged, and total movement decreases by one.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

/-- Raise the final color of `x` to the color immediately after cut `i`. -/
def delayColor (z : Coloring α s) (x : α) (i : Fin s) : Coloring α s :=
  Function.update z x i.succ

omit [Fintype α] in
@[simp] theorem delayColor_apply_self (z : Coloring α s) (x : α) (i : Fin s) :
    delayColor z x i x = i.succ := by
  simp [delayColor]

omit [Fintype α] in
theorem delayColor_apply_of_ne (z : Coloring α s) (x : α) (i : Fin s)
    (y : α) (hy : y ≠ x) : delayColor z x i y = z y := by
  simp [delayColor, hy]

omit [Fintype α] in
theorem earlier_delayColor (a z : Coloring α s) (x : α) (i : Fin s)
    (hx : (z x).val = i.val) (hmove : (z x).val < (a x).val)
    (hearlier : Earlier a z) : Earlier a (delayColor z x i) := by
  intro y
  by_cases hy : y = x
  · subst y
    rw [delayColor_apply_self]
    change i.val + 1 ≤ (a x).val
    omega
  · rw [delayColor_apply_of_ne z x i y hy]
    exact hearlier y

/-- Delaying a coordinate cannot introduce a newly moved vertex. -/
theorem changes_delayColor_subset (a z : Coloring α s) (x : α) (i : Fin s)
    (hx : (z x).val = i.val) : changes a (delayColor z x i) ⊆ changes a z := by
  intro y hy
  have hlt : delayColor z x i y < a y := (Finset.mem_filter.mp hy).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ y, ?_⟩
  by_cases hyx : y = x
  · subst y
    rw [delayColor_apply_self] at hlt
    change i.val + 1 < (a x).val at hlt
    change (z x).val < (a x).val
    omega
  · rw [delayColor_apply_of_ne z x i y hyx] at hlt
    exact hlt

theorem prefix_delayColor_self (z : Coloring α s) (x : α) (i : Fin s)
    (_hx : (z x).val = i.val) :
    prefixSet (delayColor z x i) i = (prefixSet z i).erase x := by
  ext y
  by_cases hy : y = x
  · subst y
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, delayColor_apply_self]
    simp
  · constructor
    · intro hnew
      have hle : (delayColor z x i y).val ≤ i.val :=
        (Finset.mem_filter.mp hnew).2
      rw [delayColor_apply_of_ne z x i y hy] at hle
      exact Finset.mem_erase.mpr
        ⟨hy, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hle⟩⟩
    · intro hold
      have hmem : y ∈ prefixSet z i := (Finset.mem_erase.mp hold).2
      have hle : (z y).val ≤ i.val := (Finset.mem_filter.mp hmem).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ y, ?_⟩
      rw [delayColor_apply_of_ne z x i y hy]
      exact hle

theorem prefix_delayColor_of_ne (z : Coloring α s) (x : α) (i j : Fin s)
    (hx : (z x).val = i.val) (hji : j ≠ i) :
    prefixSet (delayColor z x i) j = prefixSet z j := by
  ext y
  by_cases hy : y = x
  · subst y
    have hvals : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
      delayColor_apply_self]
    change i.val + 1 ≤ j.val ↔ (z x).val ≤ j.val
    omega
  · simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [delayColor_apply_of_ne z x i y hy]

/-- Exactly one crossing disappears at the affected cut. -/
theorem crossings_delayColor_self (a z : Coloring α s) (x : α) (i : Fin s)
    (hx : (z x).val = i.val) (hmove : (z x).val < (a x).val) :
    crossings a (delayColor z x i) i + 1 = crossings a z i := by
  unfold crossings
  rw [prefix_delayColor_self z x i hx, Finset.erase_sdiff_comm]
  apply Finset.card_erase_add_one
  simp only [Finset.mem_sdiff, prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> omega

theorem crossings_delayColor_of_ne (a z : Coloring α s) (x : α) (i j : Fin s)
    (hx : (z x).val = i.val) (hji : j ≠ i) :
    crossings a (delayColor z x i) j = crossings a z j := by
  unfold crossings
  rw [prefix_delayColor_of_ne z x i j hx hji]

/-- The delay removes precisely one unit of total movement. -/
theorem movement_delayColor_add_one (a z : Coloring α s) (x : α) (i : Fin s)
    (hx : (z x).val = i.val) (hmove : (z x).val < (a x).val) :
    movement a (delayColor z x i) + 1 = movement a z := by
  let f : α → ℕ := fun y => (a y).val - (z y).val
  let g : α → ℕ := fun y => (a y).val - (delayColor z x i y).val
  have hrest : (∑ y ∈ Finset.univ.erase x, g y) =
      ∑ y ∈ Finset.univ.erase x, f y := by
    apply Finset.sum_congr rfl
    intro y hy
    have hne : y ≠ x := (Finset.mem_erase.mp hy).1
    dsimp only [g, f]
    rw [delayColor_apply_of_ne z x i y hne]
  have hpoint : g x + 1 = f x := by
    dsimp only [g, f]
    rw [delayColor_apply_self]
    change (a x).val - (i.val + 1) + 1 = (a x).val - (z x).val
    omega
  change (∑ y, g y) + 1 = ∑ y, f y
  rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ x),
    ← Finset.sum_erase_add Finset.univ f (Finset.mem_univ x), hrest]
  omega

end TalagrandThreshold.Selector

end

end OAI
