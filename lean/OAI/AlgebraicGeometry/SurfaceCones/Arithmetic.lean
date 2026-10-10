import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace OAI


/-!
# Finite-layer and weighted-variance inequalities

These inequalities supply the scalar calculations for completed surface cones
in *A Complete Local Domain without a Small Cohen–Macaulay Module* (OpenAI, 2026).
-/

namespace SmallCM.Arithmetic

/-- The elementary finite-layer inequality in the proof of `lem:lattice`. -/
theorem layer_square_le (N : ℤ) (r : ℕ → ℤ) (n : ℕ)
    (hr : ∀ j < n, 0 ≤ r j) (hN : ∀ j < n, r j ≤ N) :
    (∑ j ∈ Finset.range n, r j) ^ 2 ≤
      N * ∑ j ∈ Finset.range n, (2 * (j : ℤ) + 1) * r j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrn : 0 ≤ r n := hr n (Nat.lt_succ_self n)
    have hNn : r n ≤ N := hN n (Nat.lt_succ_self n)
    have hprev := ih (fun j hj => hr j (Nat.lt_succ_of_lt hj))
      (fun j hj => hN j (Nat.lt_succ_of_lt hj))
    have hsum : ∑ j ∈ Finset.range n, r j ≤ (n : ℤ) * N := by
      calc
        _ ≤ ∑ _j ∈ Finset.range n, N :=
          Finset.sum_le_sum (fun j hj => hN j (Nat.lt_succ_of_lt
            (Finset.mem_range.mp hj)))
        _ = _ := by simp
    simp only [Finset.sum_range_succ]
    nlinarith [mul_nonneg hrn (sub_nonneg.mpr hNn),
      mul_nonneg hrn (sub_nonneg.mpr hsum)]

/-- The scalar consequence of the rank bounds and first-degree bounds for
quotient layers. -/
theorem layer_determinant_numerator_nonneg (N : ℤ) (hN : 0 ≤ N)
    (r c : ℕ → ℤ) (n : ℕ)
    (hr : ∀ j < n, 0 ≤ r j) (hrN : ∀ j < n, r j ≤ N)
    (hc : ∀ j < n, (j : ℤ) * r j ≤ c j) :
    0 ≤ N * (∑ j ∈ Finset.range n, (2 * c j + r j)) -
      (∑ j ∈ Finset.range n, r j) ^ 2 := by
  have hs : (∑ j ∈ Finset.range n, (2 * (j : ℤ) + 1) * r j) ≤
      ∑ j ∈ Finset.range n, (2 * c j + r j) := by
    apply Finset.sum_le_sum
    intro j hj
    have h := hc j (Finset.mem_range.mp hj)
    nlinarith
  exact sub_nonneg.mpr ((layer_square_le N r n hr hrN).trans
    (mul_le_mul_of_nonneg_left hs hN))

/-- Expanding weighted square distances, without a normalization hypothesis. -/
theorem weighted_square_expansion {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (a : ℝ) :
    (∑ i ∈ s, w i * (x i - a) ^ 2) =
      (∑ i ∈ s, w i * x i ^ 2) -
      2 * a * (∑ i ∈ s, w i * x i) + a ^ 2 * (∑ i ∈ s, w i) := by
  calc
    _ = ∑ i ∈ s, ((w i * x i ^ 2 - 2 * a * (w i * x i)) + a ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The weighted variance bound for an interval of length one, used after the
slope-balancing step. -/
theorem weighted_variance_le_quarter {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (a : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1)
    (hl : ∀ i ∈ s, a ≤ x i) (hu : ∀ i ∈ s, x i ≤ a + 1) :
    (∑ i ∈ s, w i * (x i - (∑ j ∈ s, w j * x j)) ^ 2) ≤ 1 / 4 := by
  let μ := ∑ i ∈ s, w i * x i
  have hmin : (∑ i ∈ s, w i * (x i - μ) ^ 2) ≤
      ∑ i ∈ s, w i * (x i - (a + 1 / 2)) ^ 2 := by
    rw [weighted_square_expansion, weighted_square_expansion, hsum]
    change (∑ i ∈ s, w i * x i ^ 2) - 2 * μ * μ + μ ^ 2 * 1 ≤
      (∑ i ∈ s, w i * x i ^ 2) - 2 * (a + 1 / 2) * μ + (a + 1 / 2) ^ 2 * 1
    nlinarith [sq_nonneg (μ - (a + 1 / 2))]
  refine hmin.trans ?_
  calc
    _ ≤ ∑ i ∈ s, w i * (1 / 4) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left ?_ (hw i hi)
      have h := mul_nonneg (sub_nonneg.mpr (hl i hi)) (sub_nonneg.mpr (hu i hi))
      nlinarith
    _ = 1 / 4 := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The finite weighted-mixture identity for normalized ranks and Chern characters. -/
theorem mixture_identity {ι : Type*} (s : Finset ι) (w m q : ι → ℝ)
    (hsum : ∑ i ∈ s, w i = 1) :
    2 * (∑ i ∈ s, w i * q i) - (∑ i ∈ s, w i * m i) ^ 2 =
      (∑ i ∈ s, w i * (2 * q i - m i ^ 2)) +
      (∑ i ∈ s, w i * (m i - (∑ j ∈ s, w j * m j)) ^ 2) := by
  have he : (∑ i ∈ s, w i * (2 * q i - m i ^ 2)) =
      2 * (∑ i ∈ s, w i * q i) - ∑ i ∈ s, w i * m i ^ 2 := by
    calc
      _ = ∑ i ∈ s, (2 * (w i * q i) - w i * m i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [he, weighted_square_expansion, hsum]
  ring

/-- The numerical inequality for the exponent-seven polarization. -/
theorem exponent_seven :
    (5 : ℤ) * 7 ^ 3 = 1715 ∧
    (7 : ℤ) ^ 3 * (7 ^ 2 - 10) = 13377 ∧
    (6 : ℤ) * 1715 < 13377 := by
  norm_num

end SmallCM.Arithmetic

end OAI
