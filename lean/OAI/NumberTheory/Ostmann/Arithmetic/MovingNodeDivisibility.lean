import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkPreorder

namespace OAI

/-! # Every nonzero moving history retains its sampled compensation divisibility -/

namespace Ostmann
open scoped Classical

theorem recursiveTransferWeight_node_cutoff_ne_zero {State : Type*}
    (sys : TransferHistorySystem State) (F : State → ℤ → ℂ)
    (E : State → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (x : State) (t : FrequencyTree ℤ n)
    (hw : recursiveTransferWeight sys F E n x t ≠ 0) :
    ∀ z ∈ transferNodeList sys n x t, E z.state z.root z.left z.right ≠ 0 := by
  induction n generalizing x with
  | zero => simp [transferNodeList]
  | succ n ih =>
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hv := recursiveTransferWeight_nonzero_valid sys F E (n + 1) x t hw
    have hroot := (validTransferHistory_reconstructed_iff sys n x t).mp hv
    rw [recursiveTransferWeight_node sys F E n x t P hroot.1] at hw
    have hleft : recursiveTransferWeight sys F E n (sys.leftState x P) t.2.1 ≠ 0 := by
      intro hz
      simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at hw
    have hright : recursiveTransferWeight sys F E n (sys.rightState x P) t.2.2 ≠ 0 := by
      intro hz
      simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at hw
    have hc : E x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ≠ 0 := by
      intro hz
      simp only [hz, Complex.ofReal_zero, zero_mul, ne_eq, not_true_eq_false] at hw
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact hc
    · rcases List.mem_append.mp hz with hz | hz
      · exact ih _ _ hleft z hz
      · exact ih _ _ hright z hz

theorem movingSlotWeight_node_divisible {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (x : MovingSlotState σ)
    (t : FrequencyTree ℤ n)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound E) n x t ≠ 0)
    (j : Fin (2 ^ n - 1)) :
    let z := transferNodeArray (movingSlotSystem value childBound pivotBound) n x t j
    0 < z.state.compensation value ∧
      z.state.compensation value ∣ z.pivot (movingSlotSystem value childBound pivotBound) := by
  let sys := movingSlotSystem value childBound pivotBound
  let z := transferNodeArray sys n x t j
  have hz : z ∈ transferNodeList sys n x t := by
    unfold z transferNodeArray
    rw [List.getD_eq_getElem _ _ (by rw [transferNodeList_length]; exact j.isLt)]
    exact List.getElem_mem _
  have hc := recursiveTransferWeight_node_cutoff_ne_zero sys F
    (movingSlotCutoff value childBound pivotBound E) n x t hw z hz
  by_contra h
  apply hc
  exact ite_eq_right h

end Ostmann

end OAI
