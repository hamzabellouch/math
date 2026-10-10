import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem pow_le_geometric_threshold_layers {A x : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hxA : x ≤ A) (q L : ℕ) :
    x ^ q ≤ (A * (1 / 2 : ℝ) ^ L) ^ q +
      ∑ k ∈ Finset.range L,
        if A * (1 / 2 : ℝ) ^ (k + 1) < x then
          (A * (1 / 2 : ℝ) ^ k) ^ q else 0 := by
  induction L with
  | zero =>
      simpa using pow_le_pow_left₀ hx hxA q
  | succ L ih =>
      have htail : 0 ≤ (A * (1 / 2 : ℝ) ^ (L + 1)) ^ q :=
        pow_nonneg (mul_nonneg hA (pow_nonneg (by norm_num) _)) _
      have hsum : 0 ≤ ∑ k ∈ Finset.range L,
          if A * (1 / 2 : ℝ) ^ (k + 1) < x then
            (A * (1 / 2 : ℝ) ^ k) ^ q else 0 := by
        apply Finset.sum_nonneg
        intro k hk
        split
        · exact pow_nonneg (mul_nonneg hA (pow_nonneg (by norm_num) _)) _
        · exact le_rfl
      rw [Finset.sum_range_succ]
      by_cases hnew : A * (1 / 2 : ℝ) ^ (L + 1) < x
      · rw [ite_eq_left hnew]
        linarith
      · rw [ite_eq_right hnew]
        have hbound := pow_le_pow_left₀ hx (le_of_not_gt hnew) q
        linarith

theorem nat_mul_half_pow_mul_le_one (n : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    (n : ℝ) * (1 / 2 : ℝ) ^ (n * q) ≤ 1 := by
  have hbase : ∀ m : ℕ, (m : ℝ) * (1 / 2 : ℝ) ^ m ≤ 1 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        have hpow : (1 / 2 : ℝ) ^ m ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        rw [Nat.cast_succ, pow_succ]
        nlinarith
  have hexp : n ≤ n * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hq
  have hdec : (1 / 2 : ℝ) ^ (n * q) ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  exact (mul_le_mul_of_nonneg_left hdec (Nat.cast_nonneg n)).trans (hbase n)

theorem sum_pow_le_of_geometric_threshold_count {n M q : ℕ}
    (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A)
    (hratio : (M : ℝ) * (1 / 2 : ℝ) ^ q < 1)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (hupper : ∀ i, r i ≤ A)
    (hcount : ∀ k : ℕ,
      (Finset.univ.filter (fun i => A * (1 / 2 : ℝ) ^ k < r i)).card ≤ M ^ k) :
    ∑ i, r i ^ q ≤
      A ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q)) := by
  classical
  let ρ : ℝ := (M : ℝ) * (1 / 2 : ℝ) ^ q
  have hρ0 : 0 ≤ ρ := mul_nonneg (Nat.cast_nonneg M) (pow_nonneg (by norm_num) q)
  have hρ1 : ρ < 1 := hratio
  have hAq : 0 ≤ A ^ q := pow_nonneg hA q
  have hlayer (k : ℕ) :
      (∑ i, if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
        (A * (1 / 2 : ℝ) ^ k) ^ q else 0) ≤
        A ^ q * (M : ℝ) * ρ ^ k := by
    have hk0 : 0 ≤ (A * (1 / 2 : ℝ) ^ k) ^ q :=
      pow_nonneg (mul_nonneg hA (pow_nonneg (by norm_num) k)) q
    calc
      (∑ i, if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
          (A * (1 / 2 : ℝ) ^ k) ^ q else 0) =
          ((Finset.univ.filter (fun i =>
            A * (1 / 2 : ℝ) ^ (k + 1) < r i)).card : ℝ) *
              (A * (1 / 2 : ℝ) ^ k) ^ q := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((M ^ (k + 1) : ℕ) : ℝ) * (A * (1 / 2 : ℝ) ^ k) ^ q :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcount (k + 1))) hk0
      _ = A ^ q * (M : ℝ) * ρ ^ k := by
        dsimp [ρ]
        simp only [Nat.cast_pow, Nat.cast_mul, mul_pow, pow_succ, ← pow_mul, Nat.mul_comm k q]
        ring
  have htail : (n : ℝ) * (A * (1 / 2 : ℝ) ^ n) ^ q ≤ A ^ q := by
    calc
      (n : ℝ) * (A * (1 / 2 : ℝ) ^ n) ^ q =
          A ^ q * ((n : ℝ) * (1 / 2 : ℝ) ^ (n * q)) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ A ^ q * 1 :=
        mul_le_mul_of_nonneg_left (nat_mul_half_pow_mul_le_one n hq) hAq
      _ = A ^ q := mul_one _
  have hgeom : (∑ k ∈ Finset.range n, ρ ^ k) ≤ 1 / (1 - ρ) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one hρ0 hρ1 (m := 0) (n := n))
  calc
    (∑ i, r i ^ q) ≤
        ∑ i : Fin n, ((A * (1 / 2 : ℝ) ^ n) ^ q +
          ∑ k ∈ Finset.range n,
            if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
              (A * (1 / 2 : ℝ) ^ k) ^ q else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_geometric_threshold_layers hA (hr i) (hupper i) q n
    _ = (n : ℝ) * (A * (1 / 2 : ℝ) ^ n) ^ q +
        ∑ k ∈ Finset.range n, ∑ i : Fin n,
          if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
            (A * (1 / 2 : ℝ) ^ k) ^ q else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ A ^ q + ∑ k ∈ Finset.range n, A ^ q * (M : ℝ) * ρ ^ k :=
      add_le_add htail (Finset.sum_le_sum (fun k hk => hlayer k))
    _ = A ^ q + (A ^ q * (M : ℝ)) * ∑ k ∈ Finset.range n, ρ ^ k := by
      rw [Finset.mul_sum]
    _ ≤ A ^ q + (A ^ q * (M : ℝ)) * (1 / (1 - ρ)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hgeom (mul_nonneg hAq (Nat.cast_nonneg M)))
    _ = A ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q)) := by
      dsimp [ρ]
      ring

end MarkovSuperreflexivity

end OAI
