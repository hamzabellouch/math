import OAI.Analysis.MarkovType.IntegerCocycle
import Mathlib.Data.List.Chain

namespace OAI

namespace MarkovSuperreflexivity

noncomputable section

theorem wordMap_mem_openArc (s : Letter) (w : List Letter)
    (h : ReducedWord (s :: w)) : wordMap (s :: w) 0 ∈ openArc s := by
  induction w generalizing s with
  | nil =>
      simpa only [wordMap_singleton] using letterOrderIso_zero_mem_openArc s
  | cons t w ih =>
      have hh : t ≠ s.inv ∧ ReducedWord (t :: w) := List.isChain_cons_cons.mp h
      rw [wordMap_cons]
      exact letterOrderIso_mem_openArc_of_mem_openArc s t hh.1 (ih t hh.2)

theorem wordMap_mem_arc (s : Letter) (w : List Letter)
    (h : ReducedWord (s :: w)) : wordMap (s :: w) 0 ∈ arc s :=
  openArc_subset_arc s (wordMap_mem_openArc s w h)

theorem wordMap_mem_interior_arc (s : Letter) (w : List Letter)
    (h : ReducedWord (s :: w)) : wordMap (s :: w) 0 ∈ interior (arc s) :=
  openArc_subset_interior_arc s (wordMap_mem_openArc s w h)

theorem wordMap_zero_ne_int {w : List Letter} (h : ReducedWord w) (hne : w ≠ [])
    (j : ℤ) : wordMap w 0 ≠ (j : ℝ) := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons s w =>
      intro heq
      have hm := wordMap_mem_arc s w h
      rw [heq] at hm
      exact not_mem_arc_int s j hm

private theorem wordCocycle_take_of_not_mem (s : Letter) (w : List Letter)
    (hr : ReducedWord (s :: w)) (x : ℝ) (hx : x ∉ arc s) (k : ℕ) :
    wordCocycle ((s :: w).take k) x =
      -(negativeCount ((s :: w).take k) : ℤ) := by
  induction k generalizing s w x with
  | zero => simp
  | succ k ih =>
      simp only [List.take_succ_cons, wordCocycle_cons]
      rw [chi_of_not_mem s x hx]
      cases w with
      | nil =>
          cases hs : s.2 <;> simp [negativeIndicator, negativeCount_cons, hs]
      | cons t w =>
          have hh : t ≠ s.inv ∧ ReducedWord (t :: w) := List.isChain_cons_cons.mp hr
          have hmem : (letterOrderIso s).symm x ∈ arc s.inv :=
            (symm_mem_inv_arc_iff s x).mpr hx
          have hout : (letterOrderIso s).symm x ∉ arc t := by
            intro ht
            exact Set.disjoint_left.mp (disjoint_arc (Ne.symm hh.1)) hmem ht
          rw [ih t w hh.2 ((letterOrderIso s).symm x) hout]
          cases hs : s.2 <;>
            simp [negativeIndicator, negativeCount_cons, hs, Nat.cast_add]

theorem wordCocycle_take_int {r : List Letter} (hr : ReducedWord r)
    (k : ℕ) (j : ℤ) :
    wordCocycle (r.take k) (j : ℝ) = -(negativeCount (r.take k) : ℤ) := by
  cases r with
  | nil => simp
  | cons s w => exact wordCocycle_take_of_not_mem s w hr j (not_mem_arc_int s j) k

private theorem wordCocycle_take_upper_zero {r : List Letter} (hr : ReducedWord r)
    (k : ℕ) :
    wordCocycle (r.take k) (wordMap r 0) = (positiveCount (r.take k) : ℤ) := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
      cases r with
      | nil => simp
      | cons s w =>
          have hw : ReducedWord w := List.IsChain.tail hr
          have hm : wordMap (s :: w) 0 ∈ arc s := wordMap_mem_arc s w hr
          simp only [List.take_succ_cons, wordCocycle_cons]
          rw [chi_of_mem s (wordMap (s :: w) 0) hm, wordMap_cons,
            OrderIso.symm_apply_apply, ih hw]
          cases hs : s.2 <;>
            simp [negativeIndicator, positiveCount_cons, hs, Nat.cast_add] ; omega

theorem wordCocycle_take_upper {r : List Letter} (hr : ReducedWord r)
    (k : ℕ) (j : ℤ) :
    wordCocycle (r.take k) (wordMap r 0 + (j : ℝ)) =
      (positiveCount (r.take k) : ℤ) := by
  rw [wordCocycle_add_int]
  exact wordCocycle_take_upper_zero hr k

theorem wordCocycle_int_of_reduced {r : List Letter} (hr : ReducedWord r) (j : ℤ) :
    wordCocycle r (j : ℝ) = -(negativeCount r : ℤ) := by
  simpa only [List.take_length] using wordCocycle_take_int hr r.length j

theorem wordCocycle_upper_of_reduced {r : List Letter} (hr : ReducedWord r) (j : ℤ) :
    wordCocycle r (wordMap r 0 + (j : ℝ)) = (positiveCount r : ℤ) := by
  simpa only [List.take_length] using wordCocycle_take_upper hr r.length j

theorem wordCocycle_int (w : List Letter) (j : ℤ) :
    wordCocycle w (j : ℝ) = -(negativeCount (reduceWord w) : ℤ) := by
  rw [← wordCocycle_reduceWord w]
  exact wordCocycle_int_of_reduced (reduceWord_reduced w) j

theorem wordCocycle_upper (w : List Letter) (j : ℤ) :
    wordCocycle w (wordMap w 0 + (j : ℝ)) =
      (positiveCount (reduceWord w) : ℤ) := by
  rw [← wordCocycle_reduceWord w, ← wordMap_reduceWord w]
  exact wordCocycle_upper_of_reduced (reduceWord_reduced w) j

theorem wordCocycle_two_levels (w : List Letter) (j : ℤ) :
    wordCocycle w (j : ℝ) = -(negativeCount (reduceWord w) : ℤ) ∧
      wordCocycle w (wordMap w 0 + (j : ℝ)) =
        (positiveCount (reduceWord w) : ℤ) :=
  ⟨wordCocycle_int w j, wordCocycle_upper w j⟩

theorem wordCocycle_original_prefix_levels (w : List Letter) (k : ℕ) (j : ℤ) :
    wordCocycle (w.take k) (j : ℝ) =
        -(negativeCount (reduceWord (w.take k)) : ℤ) ∧
      wordCocycle (w.take k) (wordMap (w.take k) 0 + (j : ℝ)) =
        (positiveCount (reduceWord (w.take k)) : ℤ) :=
  wordCocycle_two_levels (w.take k) j

theorem wordCocycle_level_gap (w : List Letter) :
    (positiveCount (reduceWord w) : ℤ) - (-(negativeCount (reduceWord w) : ℤ)) =
      ((reduceWord w).length : ℤ) := by
  rw [sub_neg_eq_add, ← Nat.cast_add, positiveCount_add_negativeCount]

theorem wordMap_zero_ne_int_of_reduceWord_ne_nil (w : List Letter)
    (hne : reduceWord w ≠ []) (j : ℤ) : wordMap w 0 ≠ (j : ℝ) := by
  rw [← wordMap_reduceWord w]
  exact wordMap_zero_ne_int (reduceWord_reduced w) hne j

theorem wordMap_zero_not_integer_iff (w : List Letter) :
    (∀ j : ℤ, wordMap w 0 ≠ (j : ℝ)) ↔ reduceWord w ≠ [] := by
  constructor
  · intro h hn
    have hz : wordMap w 0 = 0 := by
      rw [← wordMap_reduceWord w, hn, wordMap_nil_apply]
    exact h 0 (by simpa only [Int.cast_zero] using hz)
  · exact fun h j => wordMap_zero_ne_int_of_reduceWord_ne_nil w h j

end

end MarkovSuperreflexivity

end OAI
