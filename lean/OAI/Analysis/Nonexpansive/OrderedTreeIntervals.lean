import OAI.Analysis.Nonexpansive.OrderedTree
import Mathlib.Data.Finset.Max

namespace OAI

/-!
# Consecutive descendant blocks in an ordered tree

The ancestor maps are monotone and surjective. Their nonempty fibers are
intervals. Endpoints are natural numbers, so the upper endpoint may equal
the cardinality of the terminal level.
-/

namespace ReflexiveFixedPoints.OrderedTree

variable (T : OrderedTree) {i j : ℕ}

/-- The first terminal-level descendant. -/
noncomputable def descendantFirst (h : i ≤ j) (v : T.Node i) : T.Node j :=
  (T.descendants h v).min' (T.descendants_nonempty h v)

/-- The last terminal-level descendant. -/
noncomputable def descendantLast (h : i ≤ j) (v : T.Node i) : T.Node j :=
  (T.descendants h v).max' (T.descendants_nonempty h v)

/-- Inclusive lower endpoint of the descendant block. -/
noncomputable def descendantLo (h : i ≤ j) (v : T.Node i) : ℕ :=
  (T.descendantFirst h v).val

/-- Exclusive upper endpoint of the descendant block. -/
noncomputable def descendantHi (h : i ≤ j) (v : T.Node i) : ℕ :=
  (T.descendantLast h v).val + 1

@[simp]
theorem ancestorLE_descendantFirst (h : i ≤ j) (v : T.Node i) :
    T.ancestorLE h (T.descendantFirst h v) = v := by
  apply (T.mem_descendants h v _).1
  exact Finset.min'_mem (T.descendants h v) (T.descendants_nonempty h v)

@[simp]
theorem ancestorLE_descendantLast (h : i ≤ j) (v : T.Node i) :
    T.ancestorLE h (T.descendantLast h v) = v := by
  apply (T.mem_descendants h v _).1
  exact Finset.max'_mem (T.descendants h v) (T.descendants_nonempty h v)

theorem descendantFirst_le_of_ancestor_eq (h : i ≤ j) (v : T.Node i)
    (s : T.Node j) (hs : T.ancestorLE h s = v) :
    T.descendantFirst h v ≤ s := by
  exact Finset.min'_le (T.descendants h v) s
    ((T.mem_descendants h v s).2 hs)

theorem le_descendantLast_of_ancestor_eq (h : i ≤ j) (v : T.Node i)
    (s : T.Node j) (hs : T.ancestorLE h s = v) :
    s ≤ T.descendantLast h v := by
  exact Finset.le_max' (T.descendants h v) s
    ((T.mem_descendants h v s).2 hs)

/-- An ancestor fiber is exactly the natural half-open interval between its
first descendant and one past its last descendant. -/
theorem ancestorLE_eq_iff_interval (h : i ≤ j) (v : T.Node i) (s : T.Node j) :
    T.ancestorLE h s = v ↔
      T.descendantLo h v ≤ s.val ∧ s.val < T.descendantHi h v := by
  constructor
  · intro hs
    constructor
    · exact Fin.le_iff_val_le_val.mp
        (T.descendantFirst_le_of_ancestor_eq h v s hs)
    · exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp
        (T.le_descendantLast_of_ancestor_eq h v s hs))
  · rintro ⟨hlo, hhi⟩
    have hfirst : T.descendantFirst h v ≤ s :=
      Fin.le_iff_val_le_val.mpr hlo
    have hlast : s ≤ T.descendantLast h v :=
      Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp hhi)
    apply le_antisymm
    · calc
        T.ancestorLE h s ≤ T.ancestorLE h (T.descendantLast h v) :=
          T.ancestorLE_monotone h hlast
        _ = v := T.ancestorLE_descendantLast h v
    · calc
        v = T.ancestorLE h (T.descendantFirst h v) :=
          (T.ancestorLE_descendantFirst h v).symm
        _ ≤ T.ancestorLE h s := T.ancestorLE_monotone h hfirst

theorem descendantLo_lt_hi (h : i ≤ j) (v : T.Node i) :
    T.descendantLo h v < T.descendantHi h v := by
  have hle := T.descendantFirst_le_of_ancestor_eq h v
    (T.descendantLast h v) (T.ancestorLE_descendantLast h v)
  exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hle)

theorem descendantHi_le_size (h : i ≤ j) (v : T.Node i) :
    T.descendantHi h v ≤ T.size j := by
  exact Nat.succ_le_of_lt (T.descendantLast h v).isLt

theorem descendantLo_lt_size (h : i ≤ j) (v : T.Node i) :
    T.descendantLo h v < T.size j :=
  (T.descendantFirst h v).isLt

/-- Earlier nodes have descendant blocks entirely before later nodes' blocks. -/
theorem descendantHi_le_descendantLo_of_lt (h : i ≤ j)
    (v w : T.Node i) (hvw : v < w) :
    T.descendantHi h v ≤ T.descendantLo h w := by
  have hlastfirst : T.descendantLast h v < T.descendantFirst h w := by
    apply lt_of_not_ge
    intro hle
    have hwv : w ≤ v := by
      calc
        w = T.ancestorLE h (T.descendantFirst h w) :=
          (T.ancestorLE_descendantFirst h w).symm
        _ ≤ T.ancestorLE h (T.descendantLast h v) :=
          T.ancestorLE_monotone h hle
        _ = v := T.ancestorLE_descendantLast h v
    exact (not_le_of_gt hvw) hwv
  exact Nat.succ_le_of_lt (Fin.lt_def.mp hlastfirst)

/-- Every leaf belongs to its own ancestor's block. -/
theorem self_mem_ancestor_interval (h : i ≤ j) (s : T.Node j) :
    T.descendantLo h (T.ancestorLE h s) ≤ s.val ∧
      s.val < T.descendantHi h (T.ancestorLE h s) :=
  (T.ancestorLE_eq_iff_interval h (T.ancestorLE h s) s).1 rfl

/-- The threshold at the start of `v`'s block separates precisely the nodes
whose ancestor lies strictly before `v`. -/
theorem lt_descendantLo_iff_ancestorLE_lt (h : i ≤ j)
    (v : T.Node i) (s : T.Node j) :
    s.val < T.descendantLo h v ↔ T.ancestorLE h s < v := by
  constructor
  · intro hs
    apply lt_of_not_ge
    intro hvs
    rcases eq_or_lt_of_le hvs with heq | hlt
    · have hlo := (T.ancestorLE_eq_iff_interval h v s).1 heq.symm
      exact (not_le_of_gt hs) hlo.1
    · have hsep := T.descendantHi_le_descendantLo_of_lt h v
        (T.ancestorLE h s) hlt
      have hown := T.self_mem_ancestor_interval h s
      have hvles : T.descendantLo h v ≤ s.val :=
        le_trans (Nat.le_of_lt (T.descendantLo_lt_hi h v))
          (le_trans hsep hown.1)
      exact (not_le_of_gt hs) hvles
  · intro hsv
    have hsep := T.descendantHi_le_descendantLo_of_lt h
      (T.ancestorLE h s) v hsv
    exact lt_of_lt_of_le (T.self_mem_ancestor_interval h s).2 hsep

/-- The threshold just after the end of `v`'s block separates exactly the
nodes whose ancestor is at most `v`. -/
theorem lt_descendantHi_iff_ancestorLE_le (h : i ≤ j)
    (v : T.Node i) (s : T.Node j) :
    s.val < T.descendantHi h v ↔ T.ancestorLE h s ≤ v := by
  constructor
  · intro hs
    apply le_of_not_gt
    intro hvs
    have hsep := T.descendantHi_le_descendantLo_of_lt h v
      (T.ancestorLE h s) hvs
    have hown := T.self_mem_ancestor_interval h s
    exact (not_le_of_gt hs) (le_trans hsep hown.1)
  · intro hsv
    rcases eq_or_lt_of_le hsv with heq | hlt
    · exact ((T.ancestorLE_eq_iff_interval h v s).1 heq).2
    · have hlo := (T.lt_descendantLo_iff_ancestorLE_lt h v s).2 hlt
      exact lt_trans hlo (T.descendantLo_lt_hi h v)

end ReflexiveFixedPoints.OrderedTree

end OAI
