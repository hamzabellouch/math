import OAI.NumberTheory.Ostmann.Preliminaries.PrimeDivisors
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogDerivative

namespace OAI

/-! # The finite Euler-factor cost of changing a character's level -/

namespace Ostmann

open Complex Filter
open scoped BigOperators Topology

noncomputable def imprimitiveEulerFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : ℕ) (s : ℂ) : ℂ := 1 - χ p * (p : ℂ) ^ (-s)

noncomputable def imprimitiveEulerProduct {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (s : ℂ) : ℂ := ∏ p ∈ N.primeFactors, imprimitiveEulerFactor χ p s

theorem euler_tail_norm_le_half {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ ‖(p : ℂ) ^ (-s)‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    _ = (p : ℝ) ^ (-s.re) := by rw [Complex.norm_natCast_cpow_of_pos hp.pos]; simp
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2

theorem imprimitiveEulerFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) : imprimitiveEulerFactor χ p s ≠ 0 := by
  intro h
  have hh := euler_tail_norm_le_half χ hp s hs
  have he : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hh
  norm_num at hh

theorem imprimitiveEulerFactor_hasDeriv {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (imprimitiveEulerFactor χ p)
      ((χ p * (p : ℂ) ^ (-s)) * Complex.log (p : ℂ)) s := by
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hh := (((hasDerivAt_id s).neg).const_cpow (.inl hn)).const_mul (χ p) |>.const_sub 1
  change HasDerivAt (fun x : ℂ => 1 - χ p * (p : ℂ) ^ (-x)) _ s
  convert hh using 1 <;> dsimp
  ring

theorem imprimitiveEulerFactor_logDeriv_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (imprimitiveEulerFactor χ p) s‖ ≤ Real.log p := by
  let u := χ p * (p : ℂ) ^ (-s)
  have hu : ‖u‖ ≤ 1 / 2 := euler_tail_norm_le_half χ hp s hs
  have hden : 0 < ‖1 - u‖ := norm_pos_iff.mpr (imprimitiveEulerFactor_ne_zero χ hp s hs)
  have hcomp : ‖u‖ ≤ ‖1 - u‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one] at hh
    linarith
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
  rw [logDeriv_apply, (imprimitiveEulerFactor_hasDeriv χ hp s).deriv, norm_div, norm_mul, hlog]
  apply (div_le_iff₀ hden).mpr
  change ‖u‖ * Real.log p ≤ Real.log p * ‖1 - u‖
  have hplog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le)
  nlinarith [mul_le_mul_of_nonneg_right hcomp hplog]

theorem imprimitiveEulerProduct_logDeriv_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 0 < N) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (imprimitiveEulerProduct χ N) s‖ ≤ Real.log N := by
  have he : logDeriv (imprimitiveEulerProduct χ N) s =
      ∑ p ∈ N.primeFactors, logDeriv (imprimitiveEulerFactor χ p) s := by
    unfold imprimitiveEulerProduct
    rw [logDeriv_fun_prod]
    · intro p hp
      exact imprimitiveEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp) s hs
    · intro p hp
      exact (imprimitiveEulerFactor_hasDeriv χ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun p hp =>
    imprimitiveEulerFactor_logDeriv_bound χ (Nat.prime_of_mem_primeFactors hp) s hs)).trans
  exact sum_log_prime_divisors_le _ hN (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun _ hp => Nat.dvd_of_mem_primeFactors hp)

/-- Passing from a primitive character to any multiple level costs at most
`log N` in its logarithmic derivative, uniformly throughout Re(s)>1. -/
theorem logDeriv_changeLevel_bound {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (hN : q ∣ N) (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hN χ)) s -
      logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ Real.log N := by
  have he : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hN χ) =ᶠ[𝓝 s]
      (DirichletCharacter.LFunction χ) * imprimitiveEulerProduct χ N := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_changeLevel hN χ (.inr (by intro h; simp [h] at hz))
  have hprod : imprimitiveEulerProduct χ N s ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p hp => imprimitiveEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp) s hs.le)
  have hprodD : DifferentiableAt ℂ (imprimitiveEulerProduct χ N) s :=
    DifferentiableAt.fun_finsetProd (fun p hp =>
      (imprimitiveEulerFactor_hasDeriv χ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt)
  have hl := (logDeriv_congr_nhds he).self_of_nhds
  rw [logDeriv_mul s (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (.inr (by intro h; simp [h] at hs)) hs.le) hprod
    (DirichletCharacter.differentiableAt_LFunction χ s (.inl (by intro h; simp [h] at hs))) hprodD] at hl
  rw [hl, add_sub_cancel_left]
  exact imprimitiveEulerProduct_logDeriv_bound χ N (NeZero.pos N) s hs.le

end Ostmann

end OAI
