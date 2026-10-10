import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeReciprocalBound

namespace OAI

/-! # Subexponential weighted squarefree coefficient budget at the paper's scales -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem prime_reciprocal_exponential_cutoff (C T : ℝ)
    (hT : 1 ≤ T) (N : ℕ) (hN : (N : ℝ) ≤ Real.exp (C * T)) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤
      4 * (1 + Real.log (max 1 (C / Real.log 2)) + Real.log T) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := max 1 (C / Real.log 2)
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  apply (prime_reciprocal_sum_le_log N).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  by_cases hj : Nat.log 2 N = 0
  · simp only [hj, Nat.cast_zero, Real.log_zero]
    linarith
  · have hNp : 0 < N := by
      by_contra hh
      have : N = 0 := Nat.eq_zero_of_not_pos hh
      simp [this] at hj
    have hjp : (0 : ℝ) < Nat.log 2 N := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 hNp.ne'
    have hl : (Nat.log 2 N : ℝ) * Real.log 2 ≤ C * T := by
      calc
        _ = Real.log ((2 : ℝ) ^ (Nat.log 2 N)) := (Real.log_pow _ _).symm
        _ ≤ Real.log N := Real.log_le_log (by positivity) hpow
        _ ≤ C * T := (Real.log_le_iff_le_exp (by exact_mod_cast hNp)).mpr hN
    have hjbound : (Nat.log 2 N : ℝ) ≤ D * T := by
      have hh : C ≤ D * Real.log 2 := (div_le_iff₀ hl2).mp (le_max_right _ _)
      nlinarith
    have hlog : Real.log (Nat.log 2 N) ≤ Real.log D + Real.log T := by
      calc
        _ ≤ Real.log (D * T) := Real.log_le_log hjp hjbound
        _ = _ := Real.log_mul hD0.ne' (by linarith)
    linarith

/-- The exponent `1/10^6` is the paper's moment scale; the denominator
budget is measured against `T^(1-10^-7)`, the scale of `K`. -/
theorem squarefree_coefficient_budget (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ N) →
      0 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
        Real.exp (ε * T ^ (9999999 / 10000000 : ℝ)) := by
  let μ : ℝ := 1 / 1000000
  let κ : ℝ := 9999999 / 10000000
  let D := max 1 (C / Real.log 2)
  let A := 1 + Real.log D
  have hD : 1 ≤ D := le_max_left _ _
  have hA : 0 ≤ A := by dsimp [A]; linarith [Real.log_nonneg hD]
  have hδ : 0 < κ - μ := by norm_num [κ, μ]
  have hlog := (isLittleO_log_rpow_atTop hδ).bound (show 0 < ε / 32 by positivity)
  have hconst := (tendsto_rpow_atTop hδ).eventually_ge_atTop (32 * A / ε)
  filter_upwards [hlog, hconst, eventually_ge_atTop (1 : ℝ)] with T hl hc hT N S u hN hS hu huU
  have hT0 : 0 < T := by linarith
  have hp := prime_reciprocal_exponential_cutoff C T hT N hN
  have hl' : Real.log T ≤ ε / 32 * T ^ (κ - μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
      abs_of_nonneg (Real.rpow_nonneg hT0.le _)] using hl
  have hc' : A ≤ ε / 32 * T ^ (κ - μ) := by
    have hh := (div_le_iff₀ hε).mp hc
    calc
      A = (32 * A) / 32 := by ring
      _ ≤ (T ^ (κ - μ) * ε) / 32 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = ε / 32 * T ^ (κ - μ) := by ring
  have hsum : (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      Real.exp (u * ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) := by
    apply squarefree_weighted_reciprocal_le_exp S (Nat.primesLE N) (fun s hs => (hS s hs).1) _ u hu
    intro s hs p hp
    obtain ⟨hpp, hdiv, hs0⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) hdiv).trans (hS s hs).2, hpp⟩
  apply hsum.trans
  apply Real.exp_le_exp.mpr
  have hbase : (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (A + Real.log T) := by
    simpa [A, D, add_assoc] using hp
  have hsmall : A + Real.log T ≤ ε / 16 * T ^ (κ - μ) := by linarith
  calc
    _ ≤ (4 * T ^ μ) * (4 * (A + Real.log T)) :=
      mul_le_mul huU hbase (by positivity) (by positivity)
    _ ≤ (4 * T ^ μ) * (4 * (ε / 16 * T ^ (κ - μ))) := by gcongr
    _ = ε * (T ^ μ * T ^ (κ - μ)) := by ring
    _ = ε * T ^ κ := by
      rw [← Real.rpow_add hT0]
      congr 2
      ring

end Ostmann

end OAI
