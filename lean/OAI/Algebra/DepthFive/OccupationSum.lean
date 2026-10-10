import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

private def fallingFactorialSeries (d : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun j => (j.descFactorial d : ℝ)

private lemma fallingFactorialSeries_eq (d : ℕ) :
    fallingFactorialSeries d = PowerSeries.C (d.factorial : ℝ) *
      (PowerSeries.X ^ d * (PowerSeries.mk 1 : PowerSeries ℝ) ^ (d + 1)) := by
  ext j
  rw [fallingFactorialSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.mk_one_pow_eq_mk_choose_add]
  by_cases h : d ≤ j
  · rw [ite_eq_left h, PowerSeries.coeff_mk, Nat.add_sub_of_le h,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  · rw [ite_eq_right h, mul_zero, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

private lemma fallingFactorialSeries_prod {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    (∏ i, fallingFactorialSeries (d i)) =
      PowerSeries.C (∏ i, (d i).factorial : ℝ) *
        (PowerSeries.X ^ (∑ i, d i) *
          (PowerSeries.mk 1 : PowerSeries ℝ) ^ ((∑ i, d i) + Fintype.card ι)) := by
  simp only [fallingFactorialSeries_eq, Finset.prod_mul_distrib,
    ← map_prod, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- Exact weighted weak-composition sum, with the impossible-degree case
explicitly zero. This is the coefficient-extraction form of the occupation
factorial moment identity. -/
theorem occupation_factorial_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ι → ℕ) (t : ℕ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      ∏ i, ((M i).descFactorial (d i) : ℝ)) =
      (∏ i, (d i).factorial : ℝ) *
        if (∑ i, d i) ≤ t then
          ((t + Fintype.card ι - 1).choose (t - ∑ i, d i) : ℝ) else 0 := by
  classical
  have hr : 0 < Fintype.card ι := Fintype.card_pos
  let H := ∑ i, d i
  have heq : H + Fintype.card ι = (H + Fintype.card ι - 1) + 1 := by omega
  have hcoeff := PowerSeries.coeff_prod (fun i => fallingFactorialSeries (d i)) t Finset.univ
  simp only [fallingFactorialSeries, PowerSeries.coeff_mk] at hcoeff
  rw [← hcoeff]
  change PowerSeries.coeff t (∏ i, fallingFactorialSeries (d i)) = _
  rw [fallingFactorialSeries_prod]
  change PowerSeries.coeff t (PowerSeries.C (∏ i, (d i).factorial : ℝ) *
    (PowerSeries.X ^ H * (PowerSeries.mk 1 : PowerSeries ℝ) ^
      (H + Fintype.card ι))) = _
  rw [heq, PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  by_cases hH : H ≤ t
  · rw [ite_eq_left hH, PowerSeries.coeff_mk, ite_eq_left hH]
    have harr : H + Fintype.card ι - 1 + (t - H) = t + Fintype.card ι - 1 := by
      omega
    rw [harr]
    congr 2
    apply Nat.choose_symm_of_eq_add
    dsimp [H] at *
    omega
  · rw [ite_eq_right hH, ite_eq_right hH]

/-- Stars-and-bars count for the same finite weak-composition index set. -/
theorem occupation_composition_card {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (t : ℕ) :
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card =
      (t + Fintype.card ι - 1).choose t := by
  classical
  have h := occupation_factorial_sum (ι := ι) (fun _ => 0) t
  simp at h
  exact_mod_cast h

lemma occupation_choose_ratio (t r H : ℕ) (hr : 0 < r) (hH : H ≤ t) :
    ((t + r - 1).choose (t - H) : ℝ) / ((t + r - 1).choose t : ℝ) =
      (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) := by
  have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by positivity
  have hdesc : (t.descFactorial H : ℝ) =
      (t.factorial : ℝ) / ((t - H).factorial : ℝ) := by
    apply (eq_div_iff (hfac _)).2
    exact_mod_cast (by simpa only [Nat.mul_comm] using
      Nat.factorial_mul_descFactorial hH)
  have hasc : (r.ascFactorial H : ℝ) =
      ((r + H - 1).factorial : ℝ) / ((r - 1).factorial : ℝ) := by
    apply (eq_div_iff (hfac _)).2
    exact_mod_cast (by simpa only [Nat.mul_comm] using
      Nat.factorial_mul_ascFactorial' r H hr)
  rw [Nat.cast_choose ℝ (by omega : t - H ≤ t + r - 1),
    Nat.cast_choose ℝ (by omega : t ≤ t + r - 1), hdesc, hasc]
  rw [show t + r - 1 - (t - H) = r + H - 1 by omega,
    show t + r - 1 - t = r - 1 by omega]
  field_simp

/-- The normalized factorial moment of the uniform distribution on weak
compositions. The result includes total orders above `t`, where both sides
vanish. -/
theorem occupation_factorial_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (d : ι → ℕ) (t : ℕ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      ∏ i, ((M i).descFactorial (d i) : ℝ)) /
        (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card =
      (t.descFactorial (∑ i, d i) : ℝ) /
        ((Fintype.card ι).ascFactorial (∑ i, d i) : ℝ) *
          (∏ i, (d i).factorial : ℝ) := by
  rw [occupation_factorial_sum, occupation_composition_card]
  by_cases hH : (∑ i, d i) ≤ t
  · rw [ite_eq_left hH]
    rw [mul_div_assoc, occupation_choose_ratio t (Fintype.card ι) _
      Fintype.card_pos hH]
    ring
  · rw [ite_eq_right hH, mul_zero, zero_div,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero,
      zero_div, zero_mul]

end Problem335

end

end OAI
