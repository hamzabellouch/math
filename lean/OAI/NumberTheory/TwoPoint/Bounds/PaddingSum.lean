import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

/-!
# Summing padding choices in one fixed residue environment

This is the backwards induction of manuscript Lemma `q:padding-sum`.
A state is the current integer site. The transitions may depend on the current
padding choice and all earlier choices through that site. No independence of
translated residue coordinates is assumed.
-/

open scoped BigOperators

namespace TwoPointCorrelations

/-- The finite sum over successive padding choices, with `i` the step index. -/
def paddingMass (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) : ℕ → ℕ → ℤ → ℝ
  | 0, _, _ => 1
  | m + 1, i, n => ∑ q ∈ Q, weight i n q * paddingMass Q weight next m (i + 1) (next i n q)

/-- A row bound at every site controls the full path sum, despite the dependence
of later sites on earlier padding choices. -/
theorem paddingMass_le (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hweight : ∀ i n q, q ∈ Q → 0 ≤ weight i n q)
    (hrow : ∀ i n, ∑ q ∈ Q, weight i n q ≤ K)
    (m i : ℕ) (n : ℤ) : paddingMass Q weight next m i n ≤ K ^ m := by
  induction m generalizing i n with
  | zero => simp [paddingMass]
  | succ m ih =>
    calc
      paddingMass Q weight next (m + 1) i n =
          ∑ q ∈ Q, weight i n q * paddingMass Q weight next m (i + 1) (next i n q) := rfl
      _ ≤ ∑ q ∈ Q, weight i n q * K ^ m := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (ih _ _) (hweight i n q hq)
      _ = (∑ q ∈ Q, weight i n q) * K ^ m := by rw [Finset.sum_mul]
      _ ≤ K * K ^ m := mul_le_mul_of_nonneg_right (hrow i n) (pow_nonneg hK _)
      _ = K ^ (m + 1) := by ring

/-- The departure cutoff retains a row only when its total mass is at most `K`. -/
noncomputable def cutPaddingWeight (Q : Finset ℕ) (raw : ℕ → ℤ → ℕ → ℝ)
    (K : ℝ) (i : ℕ) (n : ℤ) (q : ℕ) : ℝ :=
  if (∑ r ∈ Q, raw i n r) ≤ K then raw i n q else 0

theorem cutPaddingWeight_nonneg (Q : Finset ℕ) (raw : ℕ → ℤ → ℕ → ℝ)
    (K : ℝ) (hraw : ∀ i n q, q ∈ Q → 0 ≤ raw i n q)
    (i : ℕ) (n : ℤ) (q : ℕ) (hq : q ∈ Q) :
    0 ≤ cutPaddingWeight Q raw K i n q := by
  unfold cutPaddingWeight
  split_ifs
  · exact hraw i n q hq
  · exact le_rfl

theorem cutPaddingWeight_row (Q : Finset ℕ) (raw : ℕ → ℤ → ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (i : ℕ) (n : ℤ) :
    ∑ q ∈ Q, cutPaddingWeight Q raw K i n q ≤ K := by
  by_cases h : (∑ r ∈ Q, raw i n r) ≤ K
  · simp [cutPaddingWeight, h]
  · simp [cutPaddingWeight, h, hK]

/-- Manuscript padding bound, after the departure cutoff. The choice
`next i n q = n + εᵢ h q dᵢ` is allowed, as is a different residue at every site. -/
theorem cut_paddingMass_le (Q : Finset ℕ) (raw : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hraw : ∀ i n q, q ∈ Q → 0 ≤ raw i n q)
    (m i : ℕ) (n : ℤ) :
    paddingMass Q (cutPaddingWeight Q raw K) next m i n ≤ K ^ m := by
  exact paddingMass_le Q _ next K hK (cutPaddingWeight_nonneg Q raw K hraw)
    (cutPaddingWeight_row Q raw K hK) m i n

end TwoPointCorrelations

end OAI
