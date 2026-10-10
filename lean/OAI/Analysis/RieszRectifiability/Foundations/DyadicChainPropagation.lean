import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.DyadicPropagationRadii

namespace OAI

/-!
# Uniform propagation along dyadic descendant chains

A single propagation scale, chosen before the measure, controls squared excess
throughout a finite descendant chain. Scalar oscillation bounds at its preceding
scales also give bilateral flatness at every positive descendant depth.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_dyadic_chain_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ a (r * (2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ∀ L : ℕ,
      (∀ j < L, ScalarOscillationBound (p + 1) μ a
        (descendantRadius r j * propagationTestRadius J)
        (descendantRadius r j ^ (p + 2) * propagationScale J ^ 3)) →
      ∀ j ≤ L,
        squaredExcess (p + 1) μ a (descendantRadius r j) ≤ propagationScale J ^ 2 ∧
        (0 < j → bilateralBeta (p + 1) μ a (descendantRadius r j) < ε) := by
  obtain ⟨J, hJ₀, hJ⟩ := exists_scale_invariant_bilateral_excess_propagation hnd C G hC b hb1 hb2
    D (1 / 2) ε (by norm_num) hε J₀
  refine ⟨J, hJ₀, ?_⟩
  intro μ hg hlower a ha r hr horizon hinit hB L hosc j
  have hweight (i l : ℕ) (hil : i ≤ l) :
      (propagationScale J * b ^ i) ^ 2 ≤ (propagationScale J * b ^ l) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (propagationScale_pos J).le
      (pow_nonneg (zero_lt_one.trans hb1).le i))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1.le hil) (propagationScale_pos J).le
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hjL
    cases j with
    | zero =>
      refine ⟨?_, by omega⟩
      simpa only [descendantRadius_zero, pow_zero, mul_one] using! hinit 0 (by omega)
    | succ k =>
      have hkL : k < L := by omega
      have hlocal : ∀ l ≤ propagationHorizon J,
          squaredExcess (p + 1) μ a (descendantRadius r k * (2 : ℝ) ^ l) ≤
            (propagationScale J * b ^ l) ^ 2 := by
        intro l hl
        by_cases hlk : l ≤ k
        · rw [descendantRadius_mul_dyadic_small r k l hlk]
          have hprev := (ih (k - l) (by omega) (by omega)).1
          have hw := hweight 0 l (by omega)
          simp only [pow_zero, mul_one] at hw
          exact hprev.trans hw
        · rw [descendantRadius_mul_dyadic_large r k l (by omega)]
          exact (hinit (l - k) (by omega)).trans (hweight (l - k) l (Nat.sub_le l k))
      have hout := hJ μ hg hlower a ha (descendantRadius r k) (descendantRadius_pos r hr k)
        (descendantRadius_admissible_horizon μ r hr k (propagationHorizon J) horizon)
        hlocal (hosc k hkL) hB
      rw [descendantRadius_half] at hout
      exact ⟨hout.1, fun _ => hout.2⟩

end

end RieszRectifiability

end OAI
