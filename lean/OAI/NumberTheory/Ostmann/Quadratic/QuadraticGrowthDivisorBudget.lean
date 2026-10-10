import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthBandBalance
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUniformGauss

namespace OAI

/-! # Actual shorter sieve matrices supply every divisor-band budget -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticGrowthCutoff (C ε ξ : ℝ) (B N i : ℕ) : ℝ :=
  C * ((B : ℝ) * N) ^ ε * ((B : ℝ) ^ ξ + (N : ℝ) / (2 ^ i : ℕ))

noncomputable def quadraticGrowthDivisorBudget (C ε ξ : ℝ) (B N D : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  quadraticGrowthBandBudget (C * ((B : ℝ) * N) ^ ε) ((B : ℝ) ^ ξ) N D
    (Real.sqrt (quadraticDivisorMoment N v) * Real.sqrt (quadraticDivisorMoment N w))

theorem quadratic_growth_cutoff_bounds {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N : ℕ, 0 < B → 0 < N →
      ∀ i ≤ Nat.log 2 N,
        QuadraticSieveBound B (N / 2 ^ i) (quadraticGrowthCutoff C ε ξ B N i) := by
  obtain ⟨C, hC, hc⟩ := quadratic_growth_shortened_transpose h ε hε
  refine ⟨C, hC, ?_⟩
  intro B N hB hN i hi
  apply hc B N (2 ^ i) hB (by exact one_le_pow₀ (by norm_num))
  exact (Nat.pow_le_pow_right (by norm_num) hi).trans
    (Nat.pow_log_le_self 2 hN.ne')

theorem quadratic_growth_cutoff_nonneg {C ε ξ : ℝ} (hC : 0 ≤ C) (B N i : ℕ) :
    0 ≤ quadraticGrowthCutoff C ε ξ B N i := by
  unfold quadraticGrowthCutoff
  positivity

theorem quadratic_growth_divisor_budget_nonneg {C ε ξ : ℝ} (hC : 0 ≤ C)
    (B N D : ℕ) (v w : ℕ → ℂ) :
    0 ≤ quadraticGrowthDivisorBudget C ε ξ B N D v w := by
  unfold quadraticGrowthDivisorBudget
  exact quadratic_growth_band_budget_nonneg (by positivity) (by positivity)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)

theorem quadratic_growth_cutoff_cost {C ε ξ : ℝ} (hC : 0 ≤ C)
    {B N D : ℕ} (hD : 0 < D) (v w : ℕ → ℂ)
    {i j : ℕ} (hP : 2 ^ i * 2 ^ j ≤ 2 * D) :
    Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N i * (2 ^ i : ℕ) *
        quadraticDivisorMoment N v) *
      Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N j * (2 ^ j : ℕ) *
        quadraticDivisorMoment N w) ≤
      quadraticGrowthDivisorBudget C ε ξ B N D v w := by
  apply quadratic_growth_band_root_bound (by positivity) (by positivity) (Nat.cast_nonneg N)
    (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ i from one_le_pow₀ (by norm_num)))
    (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ j from one_le_pow₀ (by norm_num)))
    (by exact_mod_cast hD) (by exact_mod_cast hP)
    (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

theorem quadratic_growth_divisor_bands {ξ ε : ℝ}
    (h : QuadraticSieveGrowth ξ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N D : ℕ, 0 < B → 0 < N → 0 < D →
      ∀ v w : ℕ → ℂ,
        (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange B,
          ‖quadraticGaussDivisorBilinear N N d v w b‖) ≤
          3 * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 2 *
            quadraticGrowthDivisorBudget C ε ξ B N D v w) := by
  obtain ⟨C, hC, hc⟩ := quadratic_growth_cutoff_bounds h hε
  refine ⟨C, hC, ?_⟩
  intro B N D hB hN hD v w
  have hh := quadratic_gauss_uniform_bound B N N D v w
    (quadraticGrowthCutoff C ε ξ B N) (quadraticGrowthCutoff C ε ξ B N)
    (quadraticGrowthDivisorBudget C ε ξ B N D v w)
    (quadratic_growth_divisor_budget_nonneg hC.le B N D v w)
    (fun i _ => quadratic_growth_cutoff_nonneg hC.le B N i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC.le B N i)
    (hc B N hB hN) (hc B N hB hN)
    (fun _ _ _ _ _ hP => quadratic_growth_cutoff_cost hC.le hD v w hP)
  simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hh

end Ostmann

end OAI
