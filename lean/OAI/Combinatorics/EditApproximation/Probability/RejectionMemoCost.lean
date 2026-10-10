import OAI.Combinatorics.EditApproximation.Probability.RejectionSelectedLaw

namespace OAI

/-! Literal rejection trials are charged only for source coordinates
encountered by the shared memo execution. The accepted coordinates may
influence the entire request list; failure counts remain independent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Memo

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
  (range : σ → ℕ) [∀ key, NeZero (range key)]

omit [∀ key, NeZero (range key)] in
 theorem memo_selected_source_bits_le (keys : List (Sum σ κ)) (bits : ℕ)
    (hbits : ∀ key, rejectionBitCount (range key) ≤ bits) :
    (∑ key, (rejectionBitCount (range key) : ℝ) *
      selectionIndicator (Sum.inl key ∈ keys)) ≤ keys.length * bits := by
  let weight : Sum σ κ → ℕ := Sum.elim (fun key => rejectionBitCount (range key)) (fun _ => 0)
  have hs := sum_selected_nat_weights_le keys weight
  rw [Fintype.sum_sum_type] at hs
  simp only [weight, Sum.elim_inl, Sum.elim_inr, Nat.cast_zero, mul_zero,
    Finset.sum_const_zero, add_zero] at hs
  have hb : (keys.map weight).sum ≤ keys.length * bits := by
    clear hs
    induction keys with
    | nil => simp
    | cons key keys ih =>
      have hk : weight key ≤ bits := by cases key <;> simp only [weight, Sum.elim_inl, Sum.elim_inr]; exact hbits _; omega
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
      omega
  calc
    _ = ∑ key, selectionIndicator (Sum.inl key ∈ keys) * (rejectionBitCount (range key) : ℝ) := by
      apply Finset.sum_congr rfl
      intro key _
      ring
    _ ≤ ((keys.map weight).sum : ℕ) := hs
    _ ≤ (keys.length * bits : ℕ) := by exact_mod_cast hb
    _ = _ := by push_cast; rfl

 theorem memo_rejectionBits_expected_le
    (freshKeys : (∀ key, Fin (range key)) → List (Sum σ κ))
    (requests bits : ℕ)
    (hrequests : ∀ accepted, (freshKeys accepted).length ≤ requests)
    (hbits : ∀ key, rejectionBitCount (range key) ≤ bits) :
    (∫ execution, rejectionSelectedBits range
      (fun key accepted => Sum.inl key ∈ freshKeys accepted) execution
      ∂rejectionRuntimeArrayLaw range) ≤ 2 * (requests * bits : ℕ) := by
  apply rejectionSelectedBits_expected_le
  intro accepted
  exact (memo_selected_source_bits_le range (freshKeys accepted) bits hbits).trans
    (by exact_mod_cast Nat.mul_le_mul_right bits (hrequests accepted))

theorem memo_rejectionBits_expected_le_real
    (freshKeys : (∀ key, Fin (range key)) → List (Sum σ κ))
    (budget : ℝ) (bits : ℕ)
    (hrequests : ∀ accepted, ((freshKeys accepted).length : ℝ) ≤ budget)
    (hbits : ∀ key, rejectionBitCount (range key) ≤ bits) :
    (∫ execution, rejectionSelectedBits range
      (fun key accepted => Sum.inl key ∈ freshKeys accepted) execution
      ∂rejectionRuntimeArrayLaw range) ≤ 2 * (budget * bits) := by
  apply rejectionSelectedBits_expected_le
  intro accepted
  exact (memo_selected_source_bits_le range (freshKeys accepted) bits hbits).trans
    (mul_le_mul_of_nonneg_right (hrequests accepted) (Nat.cast_nonneg _))

end Memo

end EditApproximation

end OAI
