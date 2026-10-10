import OAI.Combinatorics.EditApproximation.Probability.Amplification
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The executable upper middle order statistic

The seed pass sorts its integer copy outputs and takes index `length/2`.
Strictly more than half the outputs below an upper bound suffice; ties
and repeated values are retained by the list representation.
-/

namespace EditApproximation



theorem upperMedian_lower (values : List ℕ) (hvalues : values ≠ []) (c : ℕ)
    (hlower : ∀ value ∈ values, c ≤ value) : c ≤ upperMedian values := by
  have hlength : 0 < values.length := List.length_pos_iff.mpr hvalues
  have hindex : values.length / 2 < (values.mergeSort (· ≤ ·)).length := by
    rw [List.length_mergeSort]
    omega
  have hmem : (values.mergeSort (· ≤ ·))[values.length / 2] ∈ values :=
    (List.mergeSort_perm values (· ≤ ·)).mem_iff.mp (List.getElem_mem hindex)
  have hmedian : upperMedian values = (values.mergeSort (· ≤ ·))[values.length / 2] := by
    exact (List.getElem_eq_getD 0).symm
  rw [hmedian]
  exact hlower _ hmem

theorem upperMedian_upper (values : List ℕ) (hvalues : values ≠ []) (upper : ℕ)
    (hmajority : values.length / 2 < values.countP (fun value => value ≤ upper)) :
    upperMedian values ≤ upper := by
  let sorted := values.mergeSort (· ≤ ·)
  have hlength : sorted.length = values.length := List.length_mergeSort values
  have hpositive : 0 < values.length := List.length_pos_iff.mpr hvalues
  have hindex : values.length / 2 < sorted.length := by omega
  have hmedian : upperMedian values = sorted[values.length / 2] :=
    (List.getElem_eq_getD 0).symm
  by_contra hnot
  have habove : upper < sorted[values.length / 2] := by omega
  have hdrop : (sorted.drop (values.length / 2)).filter (fun value => value ≤ upper) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro value hvalue
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hvalue
    have hj' : values.length / 2 + j < sorted.length := by
      simp only [List.length_drop] at hj
      omega
    have hge : sorted[values.length / 2] ≤ sorted[values.length / 2 + j] :=
      (List.sortedLE_mergeSort (l := values)).getElem_le_getElem_of_le
        (hi := hindex) (hj := hj')
        (show values.length / 2 ≤ values.length / 2 + j by omega)
    have hget : (sorted.drop (values.length / 2))[j] = sorted[values.length / 2 + j] := by
      simp only [List.getElem_drop]
    rw [hget] at heq
    have haboveValue : upper < value := habove.trans_le (hge.trans_eq heq)
    simpa only [decide_eq_true_eq] using not_le_of_gt haboveValue
  have hdropCount : (sorted.drop (values.length / 2)).countP (fun value => value ≤ upper) = 0 := by
    rw [List.countP_eq_length_filter, hdrop]
    rfl
  have hcount : sorted.countP (fun value => value ≤ upper) ≤ values.length / 2 := by
    have hsplit := List.take_append_drop (values.length / 2) sorted
    rw [← hsplit, List.countP_append, hdropCount, Nat.add_zero]
    exact List.countP_le_length.trans (List.length_take_le _ _)
  have hperm := (List.mergeSort_perm values (· ≤ ·)).countP_eq (fun value => value ≤ upper)
  change sorted.countP (fun value => value ≤ upper) = values.countP (fun value => value ≤ upper) at hperm
  omega

theorem clamped_upperMedian_spec (values : List ℕ) (hvalues : values ≠ [])
    (c upper N : ℕ) (hcN : c ≤ N)
    (hlower : ∀ value ∈ values, c ≤ value)
    (hmajority : values.length / 2 < values.countP (fun value => value ≤ upper)) :
    c ≤ min N (upperMedian values) ∧ min N (upperMedian values) ≤ upper :=
  ⟨le_min hcN (upperMedian_lower values hvalues c hlower),
    (min_le_right _ _).trans (upperMedian_upper values hvalues upper hmajority)⟩

end EditApproximation

end OAI
