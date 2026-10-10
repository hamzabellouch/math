import Mathlib

namespace OAI

open Polynomial

namespace Problem367

section Algebra
variable {A : Type*} [Ring A]

theorem power_recurrence_of_quadratic {B Z : A}
    (h : Z ^ 2 = 2 * B * Z - 1) (n : ℕ) :
    Z ^ (n + 2) = 2 * B * Z ^ (n + 1) - Z ^ n := by
  calc
    Z ^ (n + 2) = Z ^ 2 * Z ^ n := by rw [← pow_add]; congr 1; omega
    _ = (2 * B * Z - 1) * Z ^ n := by rw [h]
    _ = 2 * B * Z ^ (n + 1) - Z ^ n := by
      rw [sub_mul, one_mul, mul_assoc, ← pow_succ']

variable [Algebra ℝ A]

theorem pow_eq_chebyshev_of_quadratic {B Z : A}
    (h : Z ^ 2 = 2 * B * Z - 1) (n : ℕ) :
    Z ^ (n + 1) =
      aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ)) * Z -
        aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa [map_ofNat] using h
  | more n ih0 ih1 =>
    rw [show n + 2 + 1 = (n + 1) + 2 by omega,
      power_recurrence_of_quadratic h, ih1, ih0]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_sub_cancel_right]
    rw [Polynomial.Chebyshev.U_add_two]
    have hind : (n : ℤ) + 2 - 1 = (n : ℤ) + 1 := by omega
    rw [hind]
    simp only [Polynomial.Chebyshev.U_add_one]
    simp only [map_sub, map_mul, map_ofNat, aeval_X]
    noncomm_ring

end Algebra

theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) :
    |Real.sin ((n : ℝ) * x)| ≤ (n : ℝ) * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      |Real.sin ((n : ℝ) * x) * Real.cos x +
          Real.cos ((n : ℝ) * x) * Real.sin x|
          ≤ |Real.sin ((n : ℝ) * x) * Real.cos x| +
            |Real.cos ((n : ℝ) * x) * Real.sin x| := abs_add_le _ _
      _ = |Real.sin ((n : ℝ) * x)| * |Real.cos x| +
          |Real.cos ((n : ℝ) * x)| * |Real.sin x| := by rw [abs_mul, abs_mul]
      _ ≤ ((n : ℝ) * |Real.sin x|) * 1 + 1 * |Real.sin x| := by
        apply add_le_add
        · exact mul_le_mul ih (Real.abs_cos_le_one x) (abs_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = ((n : ℝ) + 1) * |Real.sin x| := by ring

theorem chebyshev_U_abs_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x| ≤ (n : ℝ) + 1 := by
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  rcases eq_or_lt_of_le hx.1 with hleft | hleft
  · subst x
    simp [abs_mul, abs_pow, abs_of_nonneg hn]
  rcases eq_or_lt_of_le hx.2 with hright | hright
  · subst x
    simp [abs_of_nonneg hn]
  have hsin : 0 < Real.sin (Real.arccos x) :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hright) (Real.arccos_lt_pi.mpr hleft)
  have htrig := Polynomial.Chebyshev.U_real_cos (Real.arccos x) (n : ℤ)
  rw [Real.cos_arccos hx.1 hx.2] at htrig
  have hbound := abs_sin_nat_mul_le (n + 1) (Real.arccos x)
  have habs := congrArg abs htrig
  simp only [abs_mul, abs_of_pos hsin, Int.cast_natCast] at habs
  apply (mul_le_mul_iff_left₀ hsin).mp
  rw [habs]
  simpa [Nat.cast_add, Nat.cast_one, abs_of_pos hsin] using hbound

theorem chebyshev_T_abs_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x| ≤ 1 := by
  have htrig := Polynomial.Chebyshev.T_real_cos (Real.arccos x) (n : ℤ)
  rw [Real.cos_arccos hx.1 hx.2] at htrig
  rw [htrig]
  exact Real.abs_cos_le_one _

section NormedRecurrence
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem norm_pow_le_of_chebyshev_bound {B Z : A}
    (h : Z ^ 2 = 2 * B * Z - 1)
    (hU : ∀ n : ℕ, ‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) : ‖Z ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * ‖Z‖ + n := by
  have hprev : ‖aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1))‖ ≤ (n : ℝ) := by
    cases n with
    | zero => simp
    | succ n => simpa using hU n
  rw [pow_eq_chebyshev_of_quadratic h]
  calc
    ‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ)) * Z -
        aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1))‖
        ≤ ‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ)) * Z‖ +
          ‖aeval B (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1))‖ := norm_sub_le _ _
    _ ≤ (‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ * ‖Z‖) + n :=
      add_le_add (norm_mul_le _ _) hprev
    _ ≤ ((n : ℝ) + 1) * ‖Z‖ + n :=
      add_le_add (mul_le_mul_of_nonneg_right (hU n) (norm_nonneg Z)) le_rfl

end NormedRecurrence

section NormedAlgebra
variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

theorem norm_aeval_chebyshev_U_le (n : ℕ) {B : A}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) :
    ‖aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1 := by
  rw [← cfc_polynomial _ B hB]
  apply norm_cfc_le (by positivity)
  intro x hx
  have hxnorm : |x| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hx).trans hBnorm
  simpa only [Real.norm_eq_abs] using chebyshev_U_abs_le n (abs_le.mp hxnorm)

theorem norm_aeval_chebyshev_T_le (n : ℕ) {B : A}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) :
    ‖aeval B (Polynomial.Chebyshev.T ℝ (n : ℤ))‖ ≤ 1 := by
  rw [← cfc_polynomial _ B hB]
  apply norm_cfc_le zero_le_one
  intro x hx
  have hxnorm : |x| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hx).trans hBnorm
  simpa only [Real.norm_eq_abs] using chebyshev_T_abs_le n (abs_le.mp hxnorm)

theorem norm_pow_le_of_selfAdjoint_quadratic {B Z : A}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1)
    (h : Z ^ 2 = 2 * B * Z - 1) (n : ℕ) :
    ‖Z ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * ‖Z‖ + n := by
  exact norm_pow_le_of_chebyshev_bound h
    (fun n => norm_aeval_chebyshev_U_le n hB hBnorm) n

theorem norm_pow_le_linear_of_selfAdjoint_quadratic {B Z : A}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1)
    (h : Z ^ 2 = 2 * B * Z - 1) (n : ℕ) :
    ‖Z ^ n‖ ≤ (‖Z‖ + 1) * ((n : ℝ) + 1) := by
  cases n with
  | zero => simp
  | succ n =>
    have hn := norm_pow_le_of_selfAdjoint_quadratic hB hBnorm h n
    simp only [Nat.cast_succ]
    nlinarith [norm_nonneg Z]

theorem norm_scaled_pow_le_of_selfAdjoint_quadratic {B Z : A} {q : ℝ}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1)
    (h : Z ^ 2 = 2 * B * Z - 1) (hq : 0 ≤ q) (n : ℕ) :
    ‖(q • Z) ^ n‖ ≤ (‖Z‖ + 1) * ((n : ℝ) + 1) * q ^ n := by
  rw [_root_.smul_pow, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hq]
  calc
    q ^ n * ‖Z ^ n‖ ≤ q ^ n * ((‖Z‖ + 1) * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (norm_pow_le_linear_of_selfAdjoint_quadratic hB hBnorm h n)
        (pow_nonneg hq n)
    _ = (‖Z‖ + 1) * ((n : ℝ) + 1) * q ^ n := by ring

theorem summable_norm_scaled_pow_of_selfAdjoint_quadratic {B Z : A} {q : ℝ}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1)
    (h : Z ^ 2 = 2 * B * Z - 1) (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => ‖(q • Z) ^ n‖) := by
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    simpa only [pow_one, add_mul, one_mul] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm).add
        (summable_geometric_of_norm_lt_one hqnorm)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n =>
    norm_scaled_pow_le_of_selfAdjoint_quadratic hB hBnorm h hq n)
  simpa only [mul_assoc] using hs.mul_left (‖Z‖ + 1)

end NormedAlgebra
end Problem367

end OAI
