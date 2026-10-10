import OAI.NumberTheory.TwoPoint.Walks.GoodWordWeightedSum

namespace OAI

/-! The good-word bound with the actual, normalized, retained padding weights. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma paddingWordWeight_nonneg (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) (hweight : ∀ i n q, 0 ≤ weight i n q)
    {m : ℕ} (i : ℕ) (n : ℤ) (q : Fin m → Q) :
    0 ≤ paddingWordWeight Q weight next i n q := by
  induction m generalizing i n with
  | zero => exact zero_le_one
  | succ m ih =>
      exact mul_nonneg (hweight _ _ _) (ih _ _ (Fin.tail q))

noncomputable def retainedColumnPaddingWeight {J k : ℕ} {P : Fin J → Finset ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
    (n : ℤ) (w : ColumnPrimeAssignment J (2 * k) P) (q : Fin (2 * k) → Q) : ℝ :=
  paddingWordWeight Q
    (fun i n q => retainedPaddingAtom Q u (eligible w i) g L K (extra w i) n q)
    (next w) 0 n q

/-- The bound holds uniformly for prime-dependent eligibility, walk shifts,
and cutoffs, retaining the exact departure normalization at each step. -/
theorem good_retained_word_sum {J k S : ℕ} {Code : Type*} [Fintype Code]
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
    (decode : Code → Fin J → Fin (2 * k) → Fin (2 * k) → Bool)
    (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K A : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ) (n : ℤ)
    (hL : 0 < L) (hK : 0 ≤ K) (hA : 1 ≤ A) (hu : ∀ q, 0 ≤ u q)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hcover : ∀ a ∈ F, ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 *
      retainedColumnPaddingWeight Q u eligible g L K extra next n a.1 a.2) ≤
        (Fintype.card Code : ℝ) * K ^ (2 * k) * A ^ (J * k + S) := by
  apply covered_good_column_padding_sum P F decode
    (retainedColumnPaddingWeight Q u eligible g L K extra next n) A (K ^ (2 * k))
    hA (pow_nonneg hK _) hmass ?_ ?_ hsingle hcover
  · intro w q
    apply paddingWordWeight_nonneg
    intro i n q
    exact retainedPaddingAtom_nonneg Q u (eligible w i) g L K (extra w i) n q hL.le (hu q)
  · intro w
    exact retained_padding_word_sum_le Q u (eligible w) g L K (extra w) (next w)
      hL hK (fun q _ => hu q) (2 * k) 0 n

/-- The complete good-word prime/padding sum at the manuscript's forest
code scale, before signs, designations and external matrix dimensions. -/
theorem eventually_good_retained_word_sum :
    ∀ᶠ L : ℝ in atTop, ∀ J k S : ℕ, ∀ P : Fin J → Finset ℕ, ∀ Q : Finset ℕ,
      ∀ F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)),
      ∀ (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
      (g : ℤ → ℝ) (K W : ℝ)
      (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
      (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ) (n : ℤ),
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ k → 0 ≤ K → 1 ≤ W →
      (∀ q, 0 ≤ u q) → (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S) →
      (∀ a ∈ F, ∃ c : BudgetColumnArrayCode J (4 * k) L,
        ∀ j i l, decodeBudgetColumnArray (show 2 * k ≤ 4 * k by omega) c j i l =
          decide (a.1 j i = a.1 j l)) →
      (∑ a ∈ F, columnReciprocalWeight a.1 *
        retainedColumnPaddingWeight Q u eligible g L K extra next n a.1 a.2) ≤
          Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_budget_column_array_card] with L hL hc
  intro J k S P Q F u eligible g K W extra next n hklo hkhi hk hK hW hu hmass hsingle hcover
  apply (good_retained_word_sum P Q F
    (decodeBudgetColumnArray (show 2 * k ≤ 4 * k by omega))
    u eligible g L K (2 * W) extra next n (by linarith) hK (by linarith)
    hu hmass hsingle hcover).trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right
      (hc k J (4 * k) hklo hkhi (by omega) le_rfl) (pow_nonneg hK _)
  · positivity

end TwoPointCorrelations

end OAI
