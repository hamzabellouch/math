import OAI.Combinatorics.ExpectationThreshold.TupleCoefficients
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# A finite geometric bound for nonzero tuples

Every finite family of tuples lies in a finite coordinate box. Factoring
the sum over this box reduces the estimate to ordinary finite geometric
sums. Adding the zero tuple contributes exactly one, so removing it gives
the selector's budget of strictly less than `1 / 20`.
-/

namespace TalagrandThreshold

open scoped BigOperators

private theorem finite_geom_sum_mul_one_sub (c : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, c ^ k) * (1 - c) = 1 - c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih]

private theorem finite_geom_sum_le_inverse {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, c ^ k) ≤ (1 - c)⁻¹ := by
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hc1)).mpr
  rw [finite_geom_sum_mul_one_sub]
  exact sub_le_self 1 (pow_nonneg hc0 n)

/-- A finite tuple family is bounded by the product of geometric bounds. -/
theorem finite_tuple_sum_le_inverse_product {ι : Type*} [Fintype ι]
    (T : Finset (ι → ℕ)) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) :
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ ∏ i, (1 - c i)⁻¹ := by
  classical
  let m : ι → ℕ := fun i => T.sup (fun t => t i) + 1
  let B : Finset (ι → ℕ) := Fintype.piFinset (fun i => Finset.range (m i))
  have hTB : T ⊆ B := by
    intro t ht
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun u => u i) ht)
  calc
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤
        ∑ t ∈ B, ∏ i, (c i) ^ (t i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTB
        (fun t _ _ => Finset.prod_nonneg fun i _ => pow_nonneg (hc0 i) (t i))
    _ = ∏ i, ∑ k ∈ Finset.range (m i), (c i) ^ k :=
      (Finset.prod_univ_sum (fun i => Finset.range (m i))
        (fun i k => (c i) ^ k)).symm
    _ ≤ ∏ i, (1 - c i)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg fun k _ => pow_nonneg (hc0 i) k
      · intro i _
        exact finite_geom_sum_le_inverse (hc0 i) (hc1 i) (m i)

/-- The sum of coefficients controls every finite tuple family. -/
theorem finite_tuple_sum_le_inverse_one_sub_sum {ι : Type*} [Fintype ι]
    (T : Finset (ι → ℕ)) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1)
    (hsum : (∑ i, c i) < 1) :
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ (1 - ∑ i, c i)⁻¹ := by
  calc
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ ∏ i, (1 - c i)⁻¹ :=
      finite_tuple_sum_le_inverse_product T c hc0 hc1
    _ = (∏ i, (1 - c i))⁻¹ := Finset.prod_inv_distrib _
    _ ≤ (1 - ∑ i, c i)⁻¹ :=
      inv_anti₀ (sub_pos.mpr hsum)
        (one_sub_sum_le_prod_one_sub c hc0 (fun i => (hc1 i).le))

/-- The actual selector coefficients give a strict budget for every finite
family of nonzero tuples, without an infinite-series argument. -/
theorem tuple_geometric_sum_lt_one_twentieth {s : ℕ}
    (T : Finset (Fin s → ℕ)) (hT : ∀ t ∈ T, t ≠ 0) :
    (∑ t ∈ T, ∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (t i)) < 1 / 20 := by
  classical
  let c : Fin s → ℝ := fun i => tupleCoefficient i.val
  have hc0 : ∀ i, 0 ≤ c i := fun i => tupleCoefficient_nonneg i.val
  have hc1 : ∀ i, c i < 1 := fun i => tupleCoefficient_lt_one i.val
  have hrho : (∑ i, c i) < (1 / 21 : ℝ) := sum_tupleCoefficient_lt s
  have hsum : (∑ i, c i) < 1 := hrho.trans (by norm_num)
  have hz : (0 : Fin s → ℕ) ∉ T := fun hz => hT 0 hz rfl
  have hall := finite_tuple_sum_le_inverse_one_sub_sum (insert 0 T) c hc0 hc1 hsum
  have htotal : 1 + (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ (1 - ∑ i, c i)⁻¹ := by
    simpa only [Finset.sum_insert hz, Pi.zero_apply, pow_zero, Finset.prod_const_one]
      using hall
  have hden : (20 / 21 : ℝ) < 1 - ∑ i, c i := by linarith
  have hinv : (1 - ∑ i, c i)⁻¹ < (21 / 20 : ℝ) := by
    have h := (inv_lt_inv₀ (sub_pos.mpr hsum)
      (by norm_num : (0 : ℝ) < 20 / 21)).mpr hden
    norm_num at h
    exact h
  change (∑ t ∈ T, ∏ i, (c i) ^ (t i)) < 1 / 20
  linarith

theorem tuple_geometric_sum_le_one_twentieth {s : ℕ}
    (T : Finset (Fin s → ℕ)) (hT : ∀ t ∈ T, t ≠ 0) :
    (∑ t ∈ T, ∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (t i)) ≤ 1 / 20 :=
  (tuple_geometric_sum_lt_one_twentieth T hT).le

/-- A positive total degree is the form supplied by a nonempty changed set. -/
theorem tuple_geometric_sum_lt_one_twentieth_of_pos_total {s : ℕ}
    (T : Finset (Fin s → ℕ)) (hT : ∀ t ∈ T, 0 < ∑ i, t i) :
    (∑ t ∈ T, ∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (t i)) < 1 / 20 := by
  apply tuple_geometric_sum_lt_one_twentieth T
  intro t ht hz
  have hpos := hT t ht
  simp [hz] at hpos

end TalagrandThreshold

end OAI
