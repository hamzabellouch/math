import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem sum_half_pow_Ico_eq (a b : ℕ) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ico a b, (1 / 2 : ℝ) ^ m) =
      2 * ((1 / 2 : ℝ) ^ a - (1 / 2 : ℝ) ^ b) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ,
        Nat.Ico_succ_right_eq_insert_Ico (Nat.le_add_right a n),
        Finset.sum_insert (by simp), ih, pow_succ]
      ring

theorem sum_half_pow_Ico_le (a b : ℕ) :
    (∑ m ∈ Finset.Ico a b, (1 / 2 : ℝ) ^ m) ≤ 2 * (1 / 2 : ℝ) ^ a := by
  by_cases hab : a ≤ b
  · rw [sum_half_pow_Ico_eq a b hab]
    have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ b := pow_nonneg (by norm_num) b
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hnonneg) (by norm_num)
  · rw [Finset.Ico_eq_empty_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hab)), Finset.sum_empty]
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) a)

theorem sum_half_pow_le_cutoff (T : Finset ℕ) (R : ℕ)
    (hT : ∀ m ∈ T, R < m) :
    (∑ m ∈ T, (1 / 2 : ℝ) ^ m) ≤ (1 / 2 : ℝ) ^ R := by
  have hsub : T ⊆ Finset.Ico (R + 1) (T.sup id + 1) := by
    intro m hm
    exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt (hT m hm),
      Nat.lt_succ_of_le (show m ≤ T.sup id from Finset.le_sup (f := id) hm)⟩
  calc
    (∑ m ∈ T, (1 / 2 : ℝ) ^ m) ≤
        ∑ m ∈ Finset.Ico (R + 1) (T.sup id + 1), (1 / 2 : ℝ) ^ m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => pow_nonneg (by norm_num) m)
    _ ≤ 2 * (1 / 2 : ℝ) ^ (R + 1) := sum_half_pow_Ico_le _ _
    _ = (1 / 2 : ℝ) ^ R := by
      rw [pow_succ]
      ring

theorem sum_indexed_powers_le_cutoff (T : Finset ℕ) (R : ℕ)
    (f : ℕ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hf0 : ∀ m ∈ T, 0 ≤ f m)
    (hfhalf : ∀ m ∈ T, f m ≤ 1 / 2)
    (hcutoff : ∀ m ∈ T, m ≤ R → f m ≤ u) :
    (∑ m ∈ T, (f m) ^ m) ≤ (R : ℝ) * u + (1 / 2 : ℝ) ^ R := by
  have hsub : T.filter (fun m => m ≤ R) ⊆ Finset.Icc 1 R := by
    intro m hm
    obtain ⟨hmT, hmR⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨hpositive m hmT, hmR⟩
  have hcard : (T.filter (fun m => m ≤ R)).card ≤ R := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hinitial : (∑ m ∈ T.filter (fun m => m ≤ R), (f m) ^ m) ≤ (R : ℝ) * u := by
    calc
      _ ≤ ∑ m ∈ T.filter (fun m => m ≤ R), u := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hmT, hmR⟩ := Finset.mem_filter.mp hm
        have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (hpositive m hmT)
        have hfone : f m ≤ 1 := (hfhalf m hmT).trans (by norm_num)
        exact (pow_le_of_le_one (hf0 m hmT) hfone hmpos.ne').trans
          (hcutoff m hmT hmR)
      _ = ((T.filter (fun m => m ≤ R)).card : ℝ) * u := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R : ℝ) * u := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hu
  have htail : (∑ m ∈ T.filter (fun m => ¬m ≤ R), (f m) ^ m) ≤
      (1 / 2 : ℝ) ^ R := by
    calc
      _ ≤ ∑ m ∈ T.filter (fun m => ¬m ≤ R), (1 / 2 : ℝ) ^ m := by
        apply Finset.sum_le_sum
        intro m hm
        have hmT := (Finset.mem_filter.mp hm).1
        exact pow_le_pow_left₀ (hf0 m hmT) (hfhalf m hmT) m
      _ ≤ (1 / 2 : ℝ) ^ R :=
        sum_half_pow_le_cutoff _ R (fun m hm =>
          Nat.lt_of_not_ge (Finset.mem_filter.mp hm).2)
  calc
    (∑ m ∈ T, (f m) ^ m) =
        (∑ m ∈ T.filter (fun m => m ≤ R), (f m) ^ m) +
          ∑ m ∈ T.filter (fun m => ¬m ≤ R), (f m) ^ m :=
      (Finset.sum_filter_add_sum_filter_not T (fun m => m ≤ R) (fun m => (f m) ^ m)).symm
    _ ≤ (R : ℝ) * u + (1 / 2 : ℝ) ^ R := add_le_add hinitial htail

theorem small_certificate_sum_le (T : Finset ℕ) (K R : ℕ) (A C q : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 < q)
    (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hrange : ∀ m ∈ T, 2 * C * (m : ℝ) / q ≤ 1 / 2)
    (hsmall : A * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2) :
    (∑ m ∈ T, (A * (2 * C * (m : ℝ) / q) ^ (K - 3)) ^ m) ≤
      (R : ℝ) * A * (2 * C * (R : ℝ) / q) ^ (K - 3) + (1 / 2 : ℝ) ^ R := by
  have hbase0 (m : ℕ) : 0 ≤ 2 * C * (m : ℝ) / q :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (Nat.cast_nonneg m)) hq.le
  have hnonneg (m : ℕ) : 0 ≤ A * (2 * C * (m : ℝ) / q) ^ (K - 3) :=
    mul_nonneg hA (pow_nonneg (hbase0 m) _)
  have hhalf (m : ℕ) (hm : m ∈ T) :
      A * (2 * C * (m : ℝ) / q) ^ (K - 3) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hbase0 m) (hrange m hm) (K - 3)) hA).trans hsmall
  have hcutoff (m : ℕ) (_hm : m ∈ T) (hmR : m ≤ R) :
      A * (2 * C * (m : ℝ) / q) ^ (K - 3) ≤
        A * (2 * C * (R : ℝ) / q) ^ (K - 3) := by
    apply mul_le_mul_of_nonneg_left _ hA
    apply pow_le_pow_left₀ (hbase0 m) _ (K - 3)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmR) (mul_nonneg (by norm_num) hC)) hq.le
  simpa only [mul_assoc] using
    sum_indexed_powers_le_cutoff T R
      (fun m : ℕ => A * (2 * C * (m : ℝ) / q) ^ (K - 3))
      (A * (2 * C * (R : ℝ) / q) ^ (K - 3))
      (hnonneg R) hpositive (fun m _ => hnonneg m) hhalf hcutoff

end RyserCoveringCounterexample.Selection

end OAI
