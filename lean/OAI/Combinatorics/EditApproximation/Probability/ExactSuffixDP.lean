import OAI.Combinatorics.EditApproximation.Geometry.AlignmentSplitting
import OAI.Combinatorics.EditApproximation.Geometry.Leaves
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! An exact suffix dynamic program for the bounded initial input range.
Each source row is computed once; its cells minimize over target cuts.
The singleton prefix cost is the executable occurrence formula. -/

namespace EditApproximation

open EditDistortion



theorem natListMinimum_le_fallback (fallback : ℕ) (values : List ℕ) :
    natListMinimum fallback values ≤ fallback := by
  induction values with
  | nil => exact le_rfl
  | cons first rest ih => exact (min_le_right _ _).trans ih

theorem natListMinimum_le_member (fallback value : ℕ) (values : List ℕ) (h : value ∈ values) :
    natListMinimum fallback values ≤ value := by
  induction values with
  | nil => simp only [List.not_mem_nil] at h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

theorem natListMinimum_lower (fallback lower : ℕ) (values : List ℕ)
    (hfallback : lower ≤ fallback) (hvalues : ∀ value ∈ values, lower ≤ value) :
    lower ≤ natListMinimum fallback values := by
  induction values with
  | nil => exact hfallback
  | cons first rest ih =>
    exact le_min (hvalues first (List.mem_cons_self))
      (ih (fun value h => hvalues value (List.mem_cons_of_mem _ h)))



theorem exactSuffixDP_length {α : Type*} [DecidableEq α] (source target : List α) :
    (exactSuffixDP source target).length = target.length + 1 := by
  cases source <;> simp only [exactSuffixDP, List.length_ofFn]

theorem ofFn_nat_getD {n j : ℕ} (f : Fin (n + 1) → ℕ) (hj : j ≤ n) :
    (List.ofFn f).getD j 0 = f ⟨j, Nat.lt_succ_of_le hj⟩ := by
  have hlt : j < (List.ofFn f).length := by simpa only [List.length_ofFn] using Nat.lt_succ_of_le hj
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]

theorem edit_nil_left_exact {α : Type*} (target : List α) : edit ([] : List α) target = target.length := by
  have hlo := (cost_length_bounds (s := true) ([] : List α) target).2
  have hup := edit_le_max_length ([] : List α) target
  simp only [List.length_nil, zero_add, max_eq_right (Nat.zero_le _)] at hlo hup
  exact Nat.le_antisymm hup hlo

theorem exactSuffixDP_spec {α : Type*} [DecidableEq α] (source target : List α) :
    ∀ j ≤ target.length, (exactSuffixDP source target).getD j 0 = edit source (target.drop j) := by
  induction source with
  | nil =>
    intro j hj
    rw [exactSuffixDP, ofFn_nat_getD _ hj, edit_nil_left_exact, List.length_drop]
  | cons a rest ih =>
    intro j hj
    rw [exactSuffixDP, ofFn_nat_getD _ hj]
    dsimp only
    have hcandidate (k : ℕ) (hk : k ≤ target.length - j) :
        edit (a :: rest) (target.drop j) ≤
          singletonCost a ((target.drop j).take k) + (exactSuffixDP rest target).getD (j + k) 0 := by
      rw [singletonCost_eq_edit, ih (j + k) (by omega)]
      have h := cost_append_le (s := true) [a] ((target.drop j).take k) rest ((target.drop j).drop k)
      rw [List.take_append_drop] at h
      simpa only [cost, edit, List.singleton_append, List.drop_drop] using h
    apply Nat.le_antisymm
    · obtain ⟨left, right, hsplit, hcost⟩ := edit_append_split [a] rest (target.drop j)
      have hk : left.length ≤ target.length - j := by
        have hlen := congrArg List.length hsplit
        simp only [List.length_drop, List.length_append] at hlen
        omega
      have hleft : (target.drop j).take left.length = left := by
        rw [hsplit]
        simp only [List.take_left]
      have hright : target.drop (j + left.length) = right := by
        rw [← List.drop_drop, hsplit]
        simp only [List.drop_left]
      have hm := natListMinimum_le_member
        (singletonCost a [] + (exactSuffixDP rest target).getD j 0)
        (singletonCost a ((target.drop j).take left.length) +
          (exactSuffixDP rest target).getD (j + left.length) 0)
        ((List.range (target.length - j + 1)).map fun k =>
          singletonCost a ((target.drop j).take k) + (exactSuffixDP rest target).getD (j + k) 0)
        (List.mem_map.mpr ⟨left.length, List.mem_range.mpr (by omega), rfl⟩)
      have hvalue : singletonCost a ((target.drop j).take left.length) +
          (exactSuffixDP rest target).getD (j + left.length) 0 = edit [a] left + edit rest right := by
        rw [hleft, singletonCost_eq_edit, ih (j + left.length) (by omega), hright]
      simpa only [List.singleton_append] using hm.trans_eq (hvalue.trans hcost.symm)
    · apply natListMinimum_lower
      · simpa only [List.take_zero, Nat.add_zero] using hcandidate 0 (Nat.zero_le _)
      · intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨k, hk, rfl⟩
        exact hcandidate k (by have := List.mem_range.mp hk; omega)



theorem exactSuffixAnswer_eq_edit {α : Type*} [DecidableEq α] (source target : List α) :
    exactSuffixAnswer source target = edit source target := by
  simpa only [exactSuffixAnswer, List.drop_zero] using exactSuffixDP_spec source target 0 (Nat.zero_le _)

theorem exactSuffixAnswer_equal {α : Type*} [DecidableEq α] (source target : List α)
    (heq : source = target) : exactSuffixAnswer source target = 0 := by
  rw [exactSuffixAnswer_eq_edit]
  exact (cost_eq_zero_iff (s := true)).mpr heq

theorem exactSuffixAnswer_approximation {α : Type*} [DecidableEq α] (source target : List α)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    edit source target ≤ exactSuffixAnswer source target ∧
      (exactSuffixAnswer source target : ℝ) ≤ (1 + epsilon) * edit source target := by
  rw [exactSuffixAnswer_eq_edit]
  constructor
  · exact le_rfl
  · nlinarith [show (0 : ℝ) ≤ (edit source target : ℝ) from Nat.cast_nonneg _]

end EditApproximation

end OAI
