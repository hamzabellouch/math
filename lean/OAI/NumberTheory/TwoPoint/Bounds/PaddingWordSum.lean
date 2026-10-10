import OAI.NumberTheory.TwoPoint.Walks.ClosedWalkNormalization
import OAI.NumberTheory.TwoPoint.Bounds.PaddingSum

namespace OAI

/-! The recursive padding bound is the full sum over actual padding words. -/

namespace TwoPointCorrelations

open Finset

noncomputable def paddingWordWeight (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) : {m : ℕ} → ℕ → ℤ → (Fin m → Q) → ℝ
  | 0, _, _, _ => 1
  | _m + 1, i, n, q => weight i n (q 0).val *
      paddingWordWeight Q weight next (i + 1) (next i n (q 0).val) (Fin.tail q)

theorem paddingMass_eq_sum_words (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) (m i : ℕ) (n : ℤ) :
    paddingMass Q weight next m i n = ∑ q : Fin m → Q, paddingWordWeight Q weight next i n q := by
  classical
  induction m generalizing i n with
  | zero => simp [paddingMass, paddingWordWeight]
  | succ m ih =>
      rw [paddingMass, sum_fin_cons, ← sum_coe_sort Q]
      apply sum_congr rfl
      intro q _
      rw [ih, mul_sum]
      apply sum_congr rfl
      intro tail _
      simp only [paddingWordWeight, Fin.cons_zero, Fin.tail_cons]

/-- Literal finite path sum, retaining the departure density cutoff at
every visited site, uniformly in all earlier padding choices. -/
theorem retained_padding_word_sum_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℕ → ℤ → Prop) (next : ℕ → ℤ → ℕ → ℤ)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q)
    (m i : ℕ) (n : ℤ) :
    (∑ q : Fin m → Q, paddingWordWeight Q
      (fun i n q => retainedPaddingAtom Q u (eligible i) g L K (extra i) n q)
      next i n q) ≤ K ^ m := by
  rw [← paddingMass_eq_sum_words]
  apply paddingMass_le Q _ next K hK
  · intro i n q hq
    exact retainedPaddingAtom_nonneg Q u (eligible i) g L K (extra i) n q hL.le (hu q hq)
  · intro i n
    exact retainedPaddingAtom_sum_le Q u (eligible i) g L K (extra i) n hL hK

end TwoPointCorrelations

end OAI
