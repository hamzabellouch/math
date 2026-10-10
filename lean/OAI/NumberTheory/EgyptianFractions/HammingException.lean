import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The Hamming-distance generating polynomial of a Boolean cube. -/
theorem sum_pow_hammingDist {m : ℕ} (x : Fin m → Bool) (t : ℝ) :
    (∑ y : Fin m → Bool, t ^ hammingDist x y) = (1 + t) ^ m := by
  have hweight (y : Fin m → Bool) :
      t ^ hammingDist x y = ∏ i : Fin m, if x i ≠ y i then t else 1 := by
    rw [hammingDist, ← Finset.prod_filter]
    simp
  simp_rw [hweight]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if x i ≠ b then t else 1)]
  have hcoordinate (i : Fin m) :
      (∑ b : Bool, if x i ≠ b then t else 1) = 1 + t := by
    cases x i <;> simp [add_comm]
  simp_rw [hcoordinate]
  simp

/-- The exact exponential moment for uniformly counted pairs of Boolean strings. -/
theorem sum_pairs_pow_hammingDist (m : ℕ) (t : ℝ) :
    (∑ xy : (Fin m → Bool) × (Fin m → Bool), t ^ hammingDist xy.1 xy.2) =
      (2 * (1 + t)) ^ m := by
  rw [Fintype.sum_prod_type (fun xy : (Fin m → Bool) × (Fin m → Bool) => t ^ hammingDist xy.1 xy.2)]
  simp_rw [sum_pow_hammingDist]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_pow]


/-- A numerical Chernoff estimate with the constants used in the manuscript. -/
theorem hamming_chernoff_factor (m : ℕ) :
    (2 : ℝ) ^ ((m : ℝ) / 4) * (3 / 4 : ℝ) ^ m ≤
      Real.exp (-(m : ℝ) / 16) := by
  have hpow : (3 / 4 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (3 / 4)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog2 : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog34 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- Fewer than one quarter differing coordinates is an exponentially small
fraction of all ordered pairs of Boolean strings. -/
theorem hamming_exception_count (m : ℕ) :
    ((Finset.univ.filter (fun xy : (Fin m → Bool) × (Fin m → Bool) =>
      (hammingDist xy.1 xy.2 : ℝ) < (m : ℝ) / 4)).card : ℝ) ≤
      (4 : ℝ) ^ m * Real.exp (-(m : ℝ) / 16) := by
  classical
  let E := Finset.univ.filter (fun xy : (Fin m → Bool) × (Fin m → Bool) =>
    (hammingDist xy.1 xy.2 : ℝ) < (m : ℝ) / 4)
  let C : ℝ := (2 : ℝ) ^ ((m : ℝ) / 4)
  have hweight (xy : (Fin m → Bool) × (Fin m → Bool)) (hxy : xy ∈ E) :
      (1 : ℝ) ≤ C * (1 / 2 : ℝ) ^ hammingDist xy.1 xy.2 := by
    have hd := (Finset.mem_filter.mp hxy).2
    have hp : (2 : ℝ) ^ hammingDist xy.1 xy.2 ≤ C := by
      exact (Real.rpow_natCast 2 _).symm ▸
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hd.le
    rw [one_div_pow, mul_one_div]
    exact (le_div_iff₀ (by positivity)).2 (by simpa using hp)
  have hcount : (E.card : ℝ) ≤ C * (3 : ℝ) ^ m := by
    calc
      (E.card : ℝ) = ∑ xy ∈ E, (1 : ℝ) := by simp
      _ ≤ ∑ xy ∈ E, C * (1 / 2 : ℝ) ^ hammingDist xy.1 xy.2 :=
        Finset.sum_le_sum hweight
      _ ≤ ∑ xy : (Fin m → Bool) × (Fin m → Bool),
          C * (1 / 2 : ℝ) ^ hammingDist xy.1 xy.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        intro xy hxy hnot
        positivity
      _ = C * (3 : ℝ) ^ m := by
        rw [← Finset.mul_sum, sum_pairs_pow_hammingDist]
        norm_num
  have hmain : C * (3 : ℝ) ^ m ≤ (4 : ℝ) ^ m * Real.exp (-(m : ℝ) / 16) := by
    calc
      C * (3 : ℝ) ^ m = (4 : ℝ) ^ m * (C * (3 / 4 : ℝ) ^ m) := by
        rw [← mul_assoc, mul_comm ((4 : ℝ) ^ m) C, mul_assoc, ← mul_pow]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (hamming_chernoff_factor m) (by positivity)
  exact hcount.trans hmain

end Problem337

end

end OAI
