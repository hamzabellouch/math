import OAI.NumberTheory.JointDickman.Arithmetic.PrimeNormalizer

namespace OAI

/-!
# Uniform upper bounds for prime-interval normalizers

The reciprocal-prime Mertens remainder gives one constant for all real
cutoffs. This is the analytic input to the small-product tail estimate.
-/

namespace JointDickman

open Finset

theorem primeNormalizer_upper
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (X Y z : ℝ), 2 ≤ X → X ≤ Y → 0 ≤ z → z ≤ 1 →
      primeNormalizer (largePrimeSet Y X) z ≤ A * (Real.log X / Real.log Y) ^ z := by
  obtain ⟨C, hC, hinterval⟩ := prime_interval_mertens_error hM
  refine ⟨Real.exp (2 + 2 * C / Real.log 2), Real.exp_pos _, ?_⟩
  intro X Y z hX hXY hz hz1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hQ : ∀ p ∈ largePrimeSet Y X, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet Y X, 1 < p :=
    fun p hp => (hQ p hp).one_lt
  have hlocal := prime_log_product_error (largePrimeSet Y X) hQ hz hz1 (by decide : (1 : ℕ) ≠ 0) hcut
  have hsum := hinterval X Y hX hXY
  have hlogratio : Real.log (Real.log Y / Real.log X) = Real.log (Real.log Y) - Real.log (Real.log X) :=
    Real.log_div hlogY.ne' hlogX.ne'
  have hdivX : C / Real.log X ≤ C / Real.log 2 :=
    div_le_div_of_nonneg_left hC hlog2 (Real.log_le_log (by norm_num) hX)
  have hdivY : C / Real.log Y ≤ C / Real.log 2 :=
    div_le_div_of_nonneg_left hC hlog2 (Real.log_le_log (by norm_num) (hX.trans hXY))
  have hsumlow := (abs_le.mp hsum).1
  have hlocalup := (abs_le.mp hlocal).2
  have hzsq : z ^ 2 ≤ 1 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsumlow hz
  have hsumerr : z * (C / Real.log Y + C / Real.log X) ≤ 2 * C / Real.log 2 := by
    calc
      _ ≤ 1 * (C / Real.log Y + C / Real.log X) :=
        mul_le_mul_of_nonneg_right hz1 (by positivity)
      _ = C / Real.log Y + C / Real.log X := one_mul _
      _ ≤ C / Real.log 2 + C / Real.log 2 := add_le_add hdivY hdivX
      _ = _ := by ring
  have hlogbound : Real.log (primeNormalizer (largePrimeSet Y X) z) ≤
      2 + 2 * C / Real.log 2 - z * Real.log (Real.log Y / Real.log X) := by
    change Real.log (primeNormalizer (largePrimeSet Y X) z) +
      z * (∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) ≤ 2 * z ^ 2 / (1 : ℕ) at hlocalup
    rw [hlogratio]
    norm_num only [Nat.cast_one, div_one] at hlocalup
    nlinarith
  have hpositive : 0 < primeNormalizer (largePrimeSet Y X) z := by
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
    have hfrac : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (hz1.trans_lt hp1)
    linarith
  calc
    _ = Real.exp (Real.log (primeNormalizer (largePrimeSet Y X) z)) := (Real.exp_log hpositive).symm
    _ ≤ Real.exp (2 + 2 * C / Real.log 2 - z * Real.log (Real.log Y / Real.log X)) :=
      Real.exp_le_exp.mpr hlogbound
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos (div_pos hlogX hlogY),
        Real.log_div hlogX.ne' hlogY.ne', Real.log_div hlogY.ne' hlogX.ne']
      congr 2
      ring

end JointDickman

end OAI
