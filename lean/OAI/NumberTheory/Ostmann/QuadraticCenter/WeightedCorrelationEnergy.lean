import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrelationExpansion
import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorCorrelationEuler

namespace OAI

/-! # The divisor sum after the large-kernel pair correlations -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_sum_energy_gram {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ) (G : κ → ι → ℂ) :
    (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) =
      (∑ d ∈ D, ∑ e ∈ D, (c d * conj (c e)) *
        ∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))).re := by
  have hpoint (s : ι) : μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2 =
      ((μ s : ℂ) * ((∑ d ∈ D, c d * G d s) * conj (∑ e ∈ D, c e * G e s))).re := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hpoint]
  rw [← Complex.re_sum]
  congr 1
  have hmul (s : ι) : (μ s : ℂ) * ((∑ d ∈ D, c d * G d s) * conj (∑ e ∈ D, c e * G e s)) =
      (∑ d ∈ D, (μ s : ℂ) * (c d * G d s)) * conj (∑ e ∈ D, c e * G e s) := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [hmul]
  rw [finite_correlation_expansion]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [map_mul]
  ring

theorem weighted_sum_energy_le_correlations {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ) (G : κ → ι → ℂ) :
    (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      ∑ d ∈ D, ∑ e ∈ D, (‖c d‖ * ‖c e‖) *
        ‖∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))‖ := by
  rw [weighted_sum_energy_gram, Complex.re_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro e he
  simpa only [norm_mul, Complex.norm_conj] using Complex.re_le_norm
    ((c d * conj (c e)) * ∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s)))

theorem divisor_combination_energy_bound {ι : Type*}
    (S : Finset ι) (P : Finset ℕ) (μ : ι → ℝ)
    (c : Finset ℕ → ℂ) (G : Finset ℕ → ι → ℂ) (lam C : ℝ)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ lam ^ U.card)
    (hpair : ∀ U ∈ P.powerset, ∀ V ∈ P.powerset,
      ‖∑ s ∈ S, (μ s : ℂ) * (G U s * conj (G V s))‖ ≤
        C * ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹) :
    (∑ s ∈ S, μ s * ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
      C * ∏ p ∈ P, (1 + lam ^ 2 + 2 * lam * (Real.sqrt (p : ℝ))⁻¹) := by
  classical
  apply (weighted_sum_energy_le_correlations S P.powerset μ c G).trans
  calc
    _ ≤ ∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
        C * (lam ^ (U.card + V.card) *
          ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro V hV
      have hprod : 0 ≤ C * ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹ := by
        positivity
      calc
        _ ≤ (lam ^ U.card * lam ^ V.card) *
            (C * ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹) :=
          mul_le_mul (mul_le_mul (hc U hU) (hc V hV) (norm_nonneg _) (by positivity))
            (hpair U hU V hV) (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_add]; ring
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [divisor_correlation_euler_product]

/-- A uniform pair bound costs exactly the square of the divisor-weight sum. -/
theorem uniform_divisor_combination_energy_bound {ι : Type*}
    (S : Finset ι) (P : Finset ℕ) (μ : ι → ℝ)
    (c : Finset ℕ → ℂ) (G : Finset ℕ → ι → ℂ) (lam C : ℝ)
    (hlam : 0 ≤ lam) (_hC : 0 ≤ C)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ lam ^ U.card)
    (hpair : ∀ U ∈ P.powerset, ∀ V ∈ P.powerset,
      ‖∑ s ∈ S, (μ s : ℂ) * (G U s * conj (G V s))‖ ≤ C) :
    (∑ s ∈ S, μ s * ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
      C * (1 + lam) ^ (2 * P.card) := by
  apply (weighted_sum_energy_le_correlations S P.powerset μ c G).trans
  calc
    _ ≤ ∑ U ∈ P.powerset, ∑ V ∈ P.powerset, C * lam ^ (U.card + V.card) := by
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro V hV
      have hh := mul_le_mul
        (mul_le_mul (hc U hU) (hc V hV) (norm_nonneg _) (by positivity))
        (hpair U hU V hV) (norm_nonneg _) (by positivity)
      convert hh using 1
      rw [pow_add]
      ring
    _ = C * (∑ U ∈ P.powerset, ∑ V ∈ P.powerset, lam ^ (U.card + V.card)) := by
      simp_rw [← Finset.mul_sum]
    _ = C * ∏ _p ∈ P, (1 + lam ^ 2 + 2 * lam) := by
      congr 1
      simpa using divisor_correlation_euler_product P lam (fun _ => 1)
    _ = C * (1 + lam) ^ (2 * P.card) := by
      have he : 1 + lam ^ 2 + 2 * lam = (1 + lam) ^ 2 := by ring
      rw [he, Finset.prod_const, pow_mul]

end Ostmann

end OAI
