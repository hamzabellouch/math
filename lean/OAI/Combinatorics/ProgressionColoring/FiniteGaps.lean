import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

namespace OAI

/-!
# The minimum positive gap in a finite set of indices

A set of `n` ordered indices whose distinct elements are separated by at least
`h` occupies a span of at least `h * (n - 1)`. Taking the least positive gap
therefore supplies a closest-return pair with this packing bound.
-/

namespace QuantitativeVanDerWaerden

/-- Pairwise separation forces a lower bound on the span of a finite set.
The proof adds the largest index and accounts for its gap from the preceding
largest index. -/
theorem gap_mul_card_sub_one_le_span (J : Finset ℕ) (hJ : J.Nonempty) (h : ℕ)
    (hgap : ∀ i ∈ J, ∀ j ∈ J, i < j → h ≤ j - i) :
    h * (J.card - 1) ≤ J.max' hJ - J.min' hJ := by
  have aux : ∀ s : Finset ℕ, ∀ hs : s.Nonempty,
      (∀ i ∈ s, ∀ j ∈ s, i < j → h ≤ j - i) →
      h * (s.card - 1) ≤ s.max' hs - s.min' hs := by
    intro s
    induction s using Finset.induction_on_max with
    | empty =>
        intro hs
        simp at hs
    | insert a s ha ih =>
        intro hins hsep
        rcases s.eq_empty_or_nonempty with rfl | hs
        · simp
        · have hane : a ∉ s := by
            intro hamem
            exact (ha a hamem).false
          have hmax : s.max' hs < a := ha _ (s.max'_mem hs)
          have hmin : s.min' hs < a := ha _ (s.min'_mem hs)
          have hminmax : s.min' hs ≤ s.max' hs :=
            s.min'_le _ (s.max'_mem hs)
          have hprev := ih hs (fun i hi j hj hij =>
            hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
          have hlast : h ≤ a - s.max' hs :=
            hsep _ (Finset.mem_insert_of_mem (s.max'_mem hs))
              a (Finset.mem_insert_self a s) hmax
          have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
          have hmul : h * s.card = h * (s.card - 1) + h := by
            calc
              h * s.card = h * ((s.card - 1) + 1) :=
                congrArg (fun n : ℕ => h * n) (Nat.sub_add_cancel hcard).symm
              _ = h * (s.card - 1) + h := by
                simp only [Nat.mul_add, Nat.mul_one]
          rw [Finset.card_insert_of_notMem hane, Nat.add_sub_cancel,
            Finset.max'_insert a s hs, Finset.min'_insert a s hs,
            max_eq_left hmax.le, min_eq_right hmin.le, hmul]
          omega
  exact aux J hJ hgap

/-- Every finite set with at least two elements has an attained minimum
positive gap; its size also obeys the packing bound. -/
theorem exists_min_gap (J : Finset ℕ) (hcard : 2 ≤ J.card) :
    ∃ a ∈ J, ∃ b ∈ J, a < b ∧ 0 < b - a ∧
      (∀ i ∈ J, ∀ j ∈ J, i < j → b - a ≤ j - i) ∧
      (∀ hJ : J.Nonempty,
        (b - a) * (J.card - 1) ≤ J.max' hJ - J.min' hJ) := by
  classical
  have hex : ∃ d : ℕ, ∃ a ∈ J, ∃ b ∈ J, a < b ∧ d = b - a := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < J.card by omega)
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨b - a, a, ha, b, hb, hab, rfl⟩
    · exact ⟨a - b, b, hb, a, ha, hba, rfl⟩
  obtain ⟨a, ha, b, hb, hab, hd⟩ := Nat.find_spec hex
  have hminimum : ∀ i ∈ J, ∀ j ∈ J, i < j → b - a ≤ j - i := by
    intro i hi j hj hij
    rw [← hd]
    exact Nat.find_min' hex ⟨i, hi, j, hj, hij, rfl⟩
  refine ⟨a, ha, b, hb, hab, Nat.sub_pos_of_lt hab, hminimum, ?_⟩
  intro hJ
  exact gap_mul_card_sub_one_le_span J hJ (b - a) hminimum

end QuantitativeVanDerWaerden

end OAI
