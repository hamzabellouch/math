import OAI.NumberTheory.TwoPointCorrelations.MRTFrequencyExponents
import Mathlib.Analysis.PSeries

namespace OAI

/-! The logarithmic bin resolution used in the multiscale partition.
Its balance with the first prime threshold is exact. -/

namespace TwoPointCorrelations

open Finset

noncomputable def mrtBaseResolution (P Q η : ℝ) : ℝ :=
  Real.exp ((1 / 6 - η) * Real.log P - (1 / 3) * Real.log (Real.log Q))

noncomputable def mrtResolution (P Q η : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ 2 * mrtBaseResolution P Q η

lemma mrtBaseResolution_pos (P Q η : ℝ) : 0 < mrtBaseResolution P Q η :=
  Real.exp_pos _

lemma mrtResolution_one (P Q η : ℝ) : mrtResolution P Q η 1 = mrtBaseResolution P Q η := by
  simp [mrtResolution]

lemma mrtResolution_pos (P Q η : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    0 < mrtResolution P Q η j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  exact mul_pos (sq_pos_of_pos hj0) (mrtBaseResolution_pos P Q η)

lemma mrt_base_resolution_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) : mrtBaseResolution P Q η ≤ P := by
  have hp0 : 0 < P := by linarith
  have hlp := Real.log_nonneg hP
  have hlq := Real.log_nonneg hQ
  have he : (1 / 6 - η) * Real.log P - (1 / 3) * Real.log (Real.log Q) ≤
      Real.log P := by nlinarith [mul_nonneg hη hlp]
  exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_log hp0)

lemma mrt_resolution_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) (j : ℕ) :
    mrtResolution P Q η j ≤ (j : ℝ) ^ 2 * P :=
  mul_le_mul_of_nonneg_left (mrt_base_resolution_le hP hQ hη) (sq_nonneg _)

lemma mrt_resolution_log_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) (j : ℕ) (hj : 1 ≤ j) :
    Real.log (mrtResolution P Q η j) ≤ 2 * Real.log (j : ℝ) + Real.log P := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hh := Real.log_le_log (mrtResolution_pos P Q η hj)
    (mrt_resolution_le hP hQ hη j)
  rwa [Real.log_mul (pow_ne_zero _ hj0.ne') (by linarith : P ≠ 0),
    Real.log_pow, Nat.cast_ofNat] at hh

lemma mrt_base_resolution_balance (P Q η : ℝ) (hQ : 1 < Q) :
    mrtBaseResolution P Q η ^ 3 * Real.log Q *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) = 1 := by
  have hq : 0 < Real.log Q := Real.log_pos hQ
  unfold mrtBaseResolution
  rw [← Real.exp_nat_mul]
  have he : (3 : ℝ) * ((1 / 6 - η) * Real.log P -
      (1 / 3) * Real.log (Real.log Q)) + Real.log (Real.log Q) +
      (-2 * mrtFrequencyExponent η 0 * Real.log P) = 0 := by
    rw [mrtFrequencyExponent_zero]
    ring
  calc
    _ = Real.exp (3 * ((1 / 6 - η) * Real.log P -
          (1 / 3) * Real.log (Real.log Q))) * Real.exp (Real.log (Real.log Q)) *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) := by
      rw [Real.exp_log hq]
      norm_num
    _ = Real.exp (3 * ((1 / 6 - η) * Real.log P -
          (1 / 3) * Real.log (Real.log Q)) + Real.log (Real.log Q) +
          (-2 * mrtFrequencyExponent η 0 * Real.log P)) := by
      rw [Real.exp_add, Real.exp_add]
    _ = 1 := by rw [he, Real.exp_zero]

lemma mrt_base_resolution_first_cost (P Q η : ℝ) (hQ : 1 < Q) :
    mrtBaseResolution P Q η ^ 2 * Real.log Q *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) =
      (mrtBaseResolution P Q η)⁻¹ := by
  have hh := mrt_base_resolution_balance P Q η hQ
  have hH := mrtBaseResolution_pos P Q η
  rw [← one_div]
  apply (eq_div_iff hH.ne').mpr
  convert hh using 1
  ring

lemma mrt_resolution_inverse_sum (P Q η : ℝ) (J : ℕ) :
    (∑ j ∈ Icc 1 J, (mrtResolution P Q η j)⁻¹) ≤
      2 * (mrtBaseResolution P Q η)⁻¹ := by
  have hs : (∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have he : Icc 1 J = Ioo 0 (J + 1) := by ext j; simp; omega
    rw [he]
    simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1)
  calc
    _ = (∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹) * (mrtBaseResolution P Q η)⁻¹ := by
      simp only [mrtResolution, mul_inv_rev, sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (mrtBaseResolution_pos P Q η).le)

end TwoPointCorrelations

end OAI
