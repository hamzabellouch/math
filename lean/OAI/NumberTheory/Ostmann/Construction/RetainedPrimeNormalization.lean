import OAI.NumberTheory.Ostmann.Arithmetic.BulkDeletionCost

namespace OAI

/-! # Normalizers after the actual finite prime exclusions -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem retained_prime_mass_lower (S D : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hmass : a ≤ ∑ p ∈ S, (p : ℝ)⁻¹)
    (hdeleted : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ a / 2) :
    a / 2 ≤ (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
      0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
      (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ ≤ 2 / a := by
  have hsplit := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  have hlower : a / 2 ≤ ∑ p ∈ S \ D, (p : ℝ)⁻¹ := by linarith
  refine ⟨hlower, lt_of_lt_of_le (by positivity) hlower, ?_⟩
  have hi := inv_anti₀ (show 0 < a / 2 by positivity) hlower
  apply hi.trans_eq
  field_simp

theorem retained_prime_normalizer_rate (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (S D : Finset ℕ) (T : ℝ),
      Real.exp (-C * L) ≤ (∑ p ∈ S, (p : ℝ)⁻¹) →
      (D.card : ℝ) ≤ Real.exp (C * L) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ p ∈ S, Real.exp T ≤ (p : ℝ)) →
      0 < (∑ p ∈ S \ D, (p : ℝ)⁻¹) ∧
        (∑ p ∈ S \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp ((C + 1) * L) := by
  filter_upwards [arithmetic_exponent_absorption 0 (39 / 10000) 0 (2 * C) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro S D T hmass hcard hT hlow
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hsmall : 2 * C * L - T ≤ -1 := by
    simp only [zero_mul, Real.exp_zero, mul_one, pow_one] at hrate
    nlinarith [mul_nonneg hC0 hL0]
  have he : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) htwo
  have hdel : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ Real.exp (-C * L) / 2 := by
    calc
      _ ≤ (D.card : ℝ) * Real.exp (-T) := bulk_deleted_reciprocal_mass_le S D T hlow
      _ ≤ Real.exp (C * L) * Real.exp (-T) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (-C * L) * Real.exp (2 * C * L - T) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-C * L) * (1 / 2) :=
        mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hsmall).trans he) (Real.exp_nonneg _)
      _ = _ := by ring
  have hm := retained_prime_mass_lower S D (Real.exp (-C * L)) (Real.exp_pos _) hmass hdel
  refine ⟨hm.2.1, hm.2.2.trans ?_⟩
  have htwo : (2 : ℝ) ≤ Real.exp L := by
    apply le_trans _ (Real.exp_le_exp.mpr hL)
    linarith [Real.add_one_le_exp 1]
  calc
    2 / Real.exp (-C * L) = 2 * Real.exp (C * L) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ Real.exp L * Real.exp (C * L) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp ((C + 1) * L) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
