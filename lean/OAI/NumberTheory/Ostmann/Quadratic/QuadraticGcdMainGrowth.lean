import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthDivisorBudget
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTransformedComparison
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveWeight

namespace OAI

/-! # The genuine main-term cancellation under the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_gcd_main_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N D K : ℕ, 0 < M → 0 < N →
      Squarefree D → Odd D → 0 < K → ∀ v : ℕ → ℂ,
      ‖quadraticTransformedFirstMain M N D K quadraticSieveWeight v -
        quadraticSmallTransformedMain M N D K quadraticSieveWeight v‖ ≤
        C * (((K * D ^ 2 : ℕ) : ℝ) * N) ^ (2 * ε) * (D : ℝ) ^ ε *
          (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + N) *
            quadraticSieveEnergy N v := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_transformed_main_comparison quadraticSieveWeight ε hε
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_growth_shortened_transpose h ε hε
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro M N D K hM hN hD ho hK v
  let P := K * D ^ 2
  have hP : 0 < P := Nat.mul_pos hK (pow_pos (Nat.pos_of_ne_zero hD.ne_zero) 2)
  have hb := hc₂ P N 1 hP (by omega) hN
  simp only [Nat.div_one, Nat.cast_one, div_one] at hb
  have hh := hc₁ M (by exact_mod_cast hM) N D K hD ho hK
    (C₂ * ((P : ℝ) * N) ^ ε * ((P : ℝ) ^ ξ + N)) (by positivity) hb v
  have he : ((P : ℝ) ^ ε * (N : ℝ) ^ ε) * ((P : ℝ) * N) ^ ε =
      ((P : ℝ) * N) ^ (2 * ε) := by
    rw [← Real.mul_rpow (Nat.cast_nonneg P) (Nat.cast_nonneg N),
      ← Real.rpow_add (by positivity : 0 < (P : ℝ) * N)]
    congr 1
    ring
  apply hh.trans_eq
  change C₁ * Real.sqrt M * (P : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
    Real.sqrt K * (C₂ * ((P : ℝ) * N) ^ ε * ((P : ℝ) ^ ξ + N)) *
      quadraticSieveEnergy N v = _
  calc
    _ = (C₁ * C₂) * (((P : ℝ) ^ ε * (N : ℝ) ^ ε) * ((P : ℝ) * N) ^ ε) *
        (D : ℝ) ^ ε * (Real.sqrt M / Real.sqrt K) * ((P : ℝ) ^ ξ + N) *
          quadraticSieveEnergy N v := by ring
    _ = _ := by rw [he]

/-- Only the fourth power of the common divisor is needed for exponents at
most two; the shortened matrix parameter remains the actual integer K D². -/
theorem quadratic_gcd_main_exponent {ξ : ℝ} (hξ : ξ ≤ 2)
    {K D : ℕ} (hK : 0 < K) (hD : 0 < D) (N : ℝ) (hN : 0 ≤ N) :
    (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + N) ≤
      (D : ℝ) ^ 4 * ((K : ℝ) ^ ξ + N) := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpow : ((D : ℝ) ^ 2) ^ ξ ≤ (D : ℝ) ^ 4 := by
    calc
      _ ≤ ((D : ℝ) ^ 2) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hDR) hξ
      _ = _ := by rw [Real.rpow_two]; ring
  have hDfour : (1 : ℝ) ≤ (D : ℝ) ^ 4 := one_le_pow₀ hDR
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg K) (by positivity)]
  have hp : 0 ≤ (K : ℝ) ^ ξ := by positivity
  have hh := mul_le_mul_of_nonneg_left hDpow hp
  have hn := mul_le_mul_of_nonneg_right hDfour hN
  nlinarith

end Ostmann

end OAI
