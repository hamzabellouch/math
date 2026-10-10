import OAI.NumberTheory.TwoPoint.Bounds.GoodRetainedWordSum
import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability

namespace OAI

/-! Average the good-word forest estimate while retaining the exact padding normalization. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem good_weighted_difference_sum {α : Type*} [Fintype α]
    {J k S : ℕ} {Code : Type*} [Fintype Code]
    (μ : FiniteLaw α) (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
    (decode : Code → Fin J → Fin (2 * k) → Fin (2 * k) → Bool)
    (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K A T : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ) (origin : α → ℤ)
    (weight delta : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) → α → ℝ)
    (hL : 0 < L) (hK : 0 ≤ K) (hA : 1 ≤ A) (hT : 0 ≤ T) (hu : ∀ q, 0 ≤ u q)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hpad : ∀ a ∈ F, ∀ x, weight a x ≤
      retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2)
    (hdelta : ∀ a ∈ F, ∀ x, |delta a x| ≤ T)
    (hcover : ∀ a ∈ F, ∀ x, weight a x ≠ 0 → delta a x ≠ 0 →
      ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 *
      μ.average (fun x => weight a x * |delta a x|)) ≤
      T * ((Fintype.card Code : ℝ) * K ^ (2 * k) * A ^ (J * k + S)) := by
  have hpoint (x : α) :
      (∑ a ∈ F, columnReciprocalWeight a.1 * (weight a x * |delta a x|)) ≤
      T * ((Fintype.card Code : ℝ) * K ^ (2 * k) * A ^ (J * k + S)) := by
    let Fx := F.filter (fun a => weight a x ≠ 0 ∧ delta a x ≠ 0)
    have heq : (∑ a ∈ F, columnReciprocalWeight a.1 * (weight a x * |delta a x|)) =
        ∑ a ∈ Fx, columnReciprocalWeight a.1 * (weight a x * |delta a x|) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a _
      split_ifs with ha
      · rfl
      · rcases not_and_or.mp ha with hw | hd
        · simp only [not_not] at hw
          rw [hw, zero_mul, mul_zero]
        · simp only [not_not] at hd
          rw [hd, abs_zero, mul_zero, mul_zero]
    rw [heq]
    calc
      _ ≤ ∑ a ∈ Fx, T * (columnReciprocalWeight a.1 *
          retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) := by
        apply sum_le_sum
        intro a ha
        have haF := (mem_filter.mp ha).1
        have hb := mul_le_mul (hpad a haF x) (hdelta a haF x)
          (abs_nonneg _) (le_trans (hw a haF x) (hpad a haF x))
        calc
          _ ≤ columnReciprocalWeight a.1 *
              (retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2 * T) :=
            mul_le_mul_of_nonneg_left hb (columnReciprocalWeight_nonneg _)
          _ = _ := by ring
      _ = T * ∑ a ∈ Fx, columnReciprocalWeight a.1 *
          retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2 :=
        (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (good_retained_word_sum P Q Fx decode u eligible g L K A extra next (origin x)
          hL hK hA hu hmass (fun a ha => hsingle a (mem_filter.mp ha).1)
          (fun a ha => hcover a (mem_filter.mp ha).1 x
            (mem_filter.mp ha).2.1 (mem_filter.mp ha).2.2)) hT
  calc
    _ = μ.average (fun x => ∑ a ∈ F,
        columnReciprocalWeight a.1 * (weight a x * |delta a x|)) := by
      simp only [FiniteLaw.average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ _ := (μ.average_mono hpoint).trans_eq (μ.average_const _)

end TwoPointCorrelations

end OAI
