import OAI.Probability.MatroidProphet.Certificates.Execution

namespace OAI

namespace MatroidProphet

open Finset

noncomputable def hazardBandBound (l : ℕ) : ℝ :=
  (((l : ℝ) + 1) * Real.log 2 + 1) / 2 ^ l

noncomputable def hazardTailPotential (l : ℕ) : ℝ :=
  2 * (((l : ℝ) + 2) * Real.log 2 + 1) / 2 ^ l

lemma hazardTailPotential_nonneg (l : ℕ) : 0 ≤ hazardTailPotential l := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ (l : ℝ) + 2 := by positivity
  exact div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hl hlog) (by norm_num))) (pow_nonneg (by norm_num) _)

lemma hazardTailPotential_step (l : ℕ) :
    hazardTailPotential l = hazardBandBound l + hazardTailPotential (l + 1) := by
  unfold hazardTailPotential hazardBandBound
  push_cast
  rw [pow_succ]
  field_simp
  ring

lemma hazardBandBound_sum (start length : ℕ) :
    (∑ k ∈ range length, hazardBandBound (start + k)) +
      hazardTailPotential (start + length) = hazardTailPotential start := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [sum_range_succ]
    have h := hazardTailPotential_step (start + length)
    rw [Nat.add_succ]
    linarith

lemma hazardTailPotential_twelve : hazardTailPotential 12 < (1 : ℝ) / 2 := by
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold hazardTailPotential
  norm_num
  linarith

theorem hazardBandBound_sum_lt_half (length : ℕ) :
    (∑ k ∈ range length, hazardBandBound (12 + k)) < (1 : ℝ) / 2 := by
  have h := hazardBandBound_sum 12 length
  have hn := hazardTailPotential_nonneg (12 + length)
  have hu := hazardTailPotential_twelve
  linarith

theorem squared_exit_mass {ι : Type*} [Fintype ι]
    (mass hazard : ι → ℝ) (eta : ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hhazard : ∀ i, 0 ≤ hazard i) (heta : 0 ≤ eta)
    (htotal : ∑ i, mass i * hazard i = 1)
    (hlow : (∑ i, if hazard i < eta then mass i * hazard i else 0) ≤ (1 : ℝ) / 2) :
    eta / 2 ≤ ∑ i, mass i * (hazard i) ^ 2 := by
  classical
  have hpoint (i : ι) : eta * (mass i * hazard i) ≤
      mass i * (hazard i)^2 + eta * (if hazard i < eta then mass i * hazard i else 0) := by
    by_cases h : hazard i < eta
    · rw [ite_eq_left h]
      have hn := mul_nonneg (hmass i) (sq_nonneg (hazard i))
      linarith
    · rw [ite_eq_right h]
      have hh : eta ≤ hazard i := le_of_not_gt h
      have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg (hmass i) (hhazard i))
      nlinarith
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hpoint i)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, htotal] at hsum
  have hl := mul_le_mul_of_nonneg_left hlow heta
  nlinarith

theorem exit_band_bound {ι : Type*} [Fintype ι]
    (mass hazard : ι → ℝ) (upper budget : ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hupper : 0 ≤ upper)
    (hhazard : ∀ i, hazard i ≤ upper)
    (hsuccess : (∑ i, mass i * (1 - hazard i)) ≤ budget)
    (hexit : (∑ i, mass i * hazard i) ≤ 1) :
    (∑ i, mass i * hazard i) ≤ upper * (budget + 1) := by
  have htotal : (∑ i, mass i) =
      (∑ i, mass i * (1 - hazard i)) + ∑ i, mass i * hazard i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  have ht : (∑ i, mass i) ≤ budget + 1 := by linarith
  have hb : (∑ i, mass i * hazard i) ≤ upper * ∑ i, mass i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hhazard i) (hmass i)
  exact hb.trans (mul_le_mul_of_nonneg_left ht hupper)

lemma hazardBandBound_eq_certificate_bound (l : ℕ) :
    2 * (((2 : ℝ) ^ (l + 1))⁻¹) *
      (Real.log (1 / (((2 : ℝ) ^ (l + 1))⁻¹)) + 1) = hazardBandBound l := by
  rw [one_div, inv_inv, Real.log_pow]
  unfold hazardBandBound
  push_cast
  rw [pow_succ]
  field_simp

end MatroidProphet

end OAI
