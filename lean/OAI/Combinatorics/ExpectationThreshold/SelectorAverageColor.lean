import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitionsLemmas
import OAI.Combinatorics.ExpectationThreshold.ScaleBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Average color from simultaneous capture

An integer color is one plus the number of preceding prefixes it misses.
Summing this finite identity against the actual probability mass gives the
mean-color identity. A captured coloring has the same family member at
every scale, so the geometric sum of its missed masses is at most one.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

/-- Count the prefixes strictly below a color, including the final color. -/
theorem sum_color_tail_indicators {s : ℕ} (c : Color s) :
    (∑ i : Fin s, if i.val < c.val then (1 : ℝ) else 0) = (c.val : ℝ) := by
  have hcs : c.val ≤ s := Nat.le_of_lt_succ c.isLt
  have hfilter : (Finset.range s).filter (fun i => i < c.val) = Finset.range c.val := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hi => ⟨hi.trans_le hcs, hi⟩⟩
  calc
    (∑ i : Fin s, if i.val < c.val then (1 : ℝ) else 0) =
        ∑ i ∈ Finset.range s, if i < c.val then (1 : ℝ) else 0 :=
      Fin.sum_univ_eq_sum_range (fun i => if i < c.val then (1 : ℝ) else 0) s
    _ = (((Finset.range s).filter (fun i => i < c.val)).card : ℝ) :=
      Finset.sum_boole _ _
    _ = (c.val : ℝ) := by rw [hfilter, Finset.card_range]

/-- The finite integer layer-cake identity for the zero-based color index. -/
theorem color_level_eq_one_add_tail {s : ℕ} (c : Color s) :
    (c.val + 1 : ℝ) = 1 + ∑ i : Fin s, if i.val < c.val then (1 : ℝ) else 0 := by
  rw [sum_color_tail_indicators]
  ring

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The mass of colors above a prefixSet is its complementary mass. -/
theorem sum_tail_eq_one_sub_prefix {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s) (i : Fin s) :
    (∑ x, if i.val < (a x).val then mu.weight H x else 0) =
      1 - ∑ x ∈ prefixSet a i, mu.weight H x := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : α => (a x).val ≤ i.val) (mu.weight H)
  rw [mu.total H] at hsplit
  have heq : (∑ x ∈ prefixSet a i, mu.weight H x) +
      (∑ x, if i.val < (a x).val then mu.weight H x else 0) = 1 := by
    simpa only [prefixSet, Finset.sum_filter, not_le] using hsplit
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using heq)

omit [DecidableEq α] in
/-- The actual mean color is one plus the sum of all missed prefixSet masses. -/
theorem meanColor_eq_one_add_sum_tail {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s) :
    meanColor mu H a = 1 +
      ∑ i : Fin s, (1 - ∑ x ∈ prefixSet a i, mu.weight H x) := by
  classical
  unfold meanColor
  simp_rw [color_level_eq_one_add_tail, add_mul, one_mul, Finset.sum_mul,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib, mu.total H, Finset.sum_comm]
  simp_rw [sum_tail_eq_one_sub_prefix mu H a]

/-- The truncation scales have total mass at most one, also when there are no scales. -/
theorem sum_dscale_le_one (s : ℕ) : (∑ i : Fin s, dscale i) ≤ 1 := by
  simpa only [dscale, one_div, inv_pow] using half_geometric_sum_le_one s

omit [DecidableEq α] in
/-- A single member capturing every prefixSet has mean color at most two. -/
theorem meanColor_le_two_of_capture {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s)
    (hcapture : ∀ i : Fin s,
      1 - dscale i ≤ ∑ x ∈ prefixSet a i, mu.weight H x) :
    meanColor mu H a ≤ 2 := by
  rw [meanColor_eq_one_add_sum_tail]
  calc
    1 + ∑ i : Fin s, (1 - ∑ x ∈ prefixSet a i, mu.weight H x) ≤
        1 + ∑ i : Fin s, dscale i := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      linarith [hcapture i]
    _ ≤ 1 + 1 := add_le_add le_rfl (sum_dscale_le_one s)
    _ = 2 := by norm_num

omit [DecidableEq α] in
/-- The same captured member supplies the average-color witness. -/
theorem Captured.exists_meanColor_le_two {F : Family α} {mu : MassFamily F} {s : ℕ}
    {a : Coloring α s} (h : Captured mu a) : ∃ H : ↥F, meanColor mu H a ≤ 2 := by
  obtain ⟨H, hH⟩ := h
  exact ⟨H, meanColor_le_two_of_capture mu H a hH⟩

end TalagrandThreshold.Selector

end OAI
