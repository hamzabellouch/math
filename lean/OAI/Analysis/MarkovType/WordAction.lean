import OAI.Analysis.MarkovType.PeriodicArcs
import OAI.Analysis.MarkovType.WordReduction
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

noncomputable def wordMap : List Letter → ℝ ≃o ℝ
  | [] => OrderIso.refl ℝ
  | s :: w => (wordMap w).trans (letterOrderIso s)

@[simp] theorem wordMap_nil : wordMap [] = OrderIso.refl ℝ := rfl

@[simp] theorem wordMap_nil_apply (x : ℝ) : wordMap [] x = x := rfl

@[simp] theorem wordMap_nil_symm (x : ℝ) : (wordMap []).symm x = x := rfl

@[simp] theorem wordMap_cons (s : Letter) (w : List Letter) (x : ℝ) :
    wordMap (s :: w) x = letterOrderIso s (wordMap w x) := rfl

@[simp] theorem wordMap_cons_symm (s : Letter) (w : List Letter) (x : ℝ) :
    (wordMap (s :: w)).symm x = (wordMap w).symm ((letterOrderIso s).symm x) :=
  rfl

@[simp] theorem wordMap_singleton (s : Letter) (x : ℝ) :
    wordMap [s] x = letterOrderIso s x := rfl

theorem wordMap_append (u v : List Letter) (x : ℝ) :
    wordMap (u ++ v) x = wordMap u (wordMap v x) := by
  induction u with
  | nil => rfl
  | cons s u ih => simp only [List.cons_append, wordMap_cons, ih]

theorem wordMap_append_equiv (u v : List Letter) :
    wordMap (u ++ v) = (wordMap v).trans (wordMap u) := by
  apply OrderIso.ext
  funext x
  exact wordMap_append u v x

theorem wordMap_append_symm (u v : List Letter) (x : ℝ) :
    (wordMap (u ++ v)).symm x = (wordMap v).symm ((wordMap u).symm x) := by
  rw [wordMap_append_equiv]
  rfl

def inverseWord (w : List Letter) : List Letter := w.reverse.map Letter.inv

@[simp] theorem inverseWord_nil : inverseWord [] = [] := rfl

@[simp] theorem inverseWord_cons (s : Letter) (w : List Letter) :
    inverseWord (s :: w) = inverseWord w ++ [s.inv] := by
  simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]

@[simp] theorem inverseWord_length (w : List Letter) :
    (inverseWord w).length = w.length := by
  simp only [inverseWord, List.length_map, List.length_reverse]

theorem wordMap_inverseWord (w : List Letter) :
    wordMap (inverseWord w) = (wordMap w).symm := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      apply OrderIso.ext
      funext x
      simp only [inverseWord_cons, wordMap_append, wordMap_singleton, ih,
        letterOrderIso_inv, wordMap_cons_symm]

theorem wordMap_cancel (u : List Letter) (s : Letter) (v : List Letter) :
    wordMap (u ++ s :: s.inv :: v) = wordMap (u ++ v) := by
  apply OrderIso.ext
  funext x
  simp only [wordMap_append, wordMap_cons, letterOrderIso_inv,
    OrderIso.apply_symm_apply]

theorem wordMap_reduceWord (w : List Letter) :
    wordMap (reduceWord w) = wordMap w :=
  reduceWord_invariant (F := wordMap) wordMap_cancel w

theorem wordMap_add_int (w : List Letter) (x : ℝ) (j : ℤ) :
    wordMap w (x + (j : ℝ)) = wordMap w x + (j : ℝ) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      simp only [wordMap_cons, ih, letterOrderIso_add_int]

theorem wordMap_symm_add_int (w : List Letter) (x : ℝ) (j : ℤ) :
    (wordMap w).symm (x + (j : ℝ)) = (wordMap w).symm x + (j : ℝ) := by
  rw [← wordMap_inverseWord]
  exact wordMap_add_int (inverseWord w) x j

theorem prefixState_wordMap (w : List Letter) (k : ℕ) (x : ℝ) :
    (wordMap (w.take k)).symm (wordMap w x) = wordMap (w.drop k) x := by
  have h : wordMap w x = wordMap (w.take k) (wordMap (w.drop k) x) := by
    rw [← wordMap_append, List.take_append_drop]
  rw [h, OrderIso.symm_apply_apply]

theorem prefixState_int (w : List Letter) (k : ℕ) (j : ℤ) :
    (wordMap (w.take k)).symm (j : ℝ) =
      wordMap (inverseWord (w.take k)) 0 + (j : ℝ) := by
  rw [← wordMap_inverseWord]
  simpa only [zero_add] using wordMap_add_int (inverseWord (w.take k)) 0 j

theorem prefixState_wordMap_add_int (w : List Letter) (k : ℕ) (x : ℝ) (j : ℤ) :
    (wordMap (w.take k)).symm (wordMap w x + (j : ℝ)) =
      wordMap (w.drop k) x + (j : ℝ) := by
  rw [wordMap_symm_add_int, prefixState_wordMap]

theorem wordMap_displacement_le (w : List Letter) (x : ℝ) :
    abs (wordMap w x - x) ≤ 2 * (w.length : ℝ) := by
  induction w with
  | nil => simp only [wordMap_nil_apply, sub_self, abs_zero, List.length_nil,
      Nat.cast_zero, mul_zero, le_refl]
  | cons s w ih =>
      have hs := letterOrderIso_displacement_lt s (wordMap w x)
      have ht := abs_sub_le (letterOrderIso s (wordMap w x)) (wordMap w x) x
      simp only [wordMap_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

theorem wordMap_displacement_lt {w : List Letter} (hw : w ≠ []) (x : ℝ) :
    abs (wordMap w x - x) < 2 * (w.length : ℝ) := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons s w =>
      have hs := letterOrderIso_displacement_lt s (wordMap w x)
      have ht := abs_sub_le (letterOrderIso s (wordMap w x)) (wordMap w x) x
      have ih := wordMap_displacement_le w x
      simp only [wordMap_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

theorem wordMap_symm_displacement_le (w : List Letter) (x : ℝ) :
    abs ((wordMap w).symm x - x) ≤ 2 * (w.length : ℝ) := by
  rw [← wordMap_inverseWord]
  simpa only [inverseWord_length] using wordMap_displacement_le (inverseWord w) x

end MarkovSuperreflexivity

end OAI
