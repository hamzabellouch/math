import OAI.NumberTheory.Ostmann.Characters.CharacterLogDerivativeSeparated
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourLogGrowth

namespace OAI

/-! # Uniform polynomial control of L'/L away from the local zero set -/

namespace Ostmann

open Complex Metric
open scoped BigOperators

theorem character_logDeriv_growth (χ : PrimitiveComplexCharacter) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t δ : ℝ), 0 < δ → ∀ s : ℂ,
      ‖s - characterZeroCenter t‖ ≤ 5 / 2 →
      (∀ z ∈ characterContourZeros χ t, δ ≤ ‖s - z‖) →
      ‖logDeriv χ.L s‖ ≤ K * (1 + |t|) * (1 + δ⁻¹) := by
  obtain ⟨B, hB, hBgrowth⟩ := character_contour_log_growth χ
  let D := B / Real.log (22 / 21 : ℝ)
  let E := 1312 * (B + D * Real.log 21 + 1)
  have hl : 0 < Real.log (22 / 21 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := div_pos hB hl
  have hG : 0 < Real.log 21 := Real.log_pos (by norm_num)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E + D, by positivity, ?_⟩
  intro t δ hδ s hs hsep
  obtain ⟨M, hM, hbound, hlog⟩ := hBgrowth t
  let N := ∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)
  have hN : N ≤ D * (1 + |t|) := by
    apply (characterContourZeros_mass_bound χ t M hM hbound).trans
    exact (div_le_div_of_nonneg_right hlog hl.le).trans_eq (by dsimp [D]; ring)
  have hh := character_logDeriv_separated_bound χ t M δ hM hδ hbound s hs hsep
  have he : 1312 * (Real.log (3 * M) + N * Real.log 21 + 1) ≤ E * (1 + |t|) := by
    have hn := mul_le_mul_of_nonneg_right hN hG.le
    dsimp [E]
    nlinarith [abs_nonneg t]
  have hn : N / δ ≤ D * (1 + |t|) * δ⁻¹ := by
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hN hδ.le
  apply hh.trans
  change 1312 * (Real.log (3 * M) + N * Real.log 21 + 1) + N / δ ≤ _
  apply (add_le_add he hn).trans
  have h1 : 0 ≤ E * (1 + |t|) * δ⁻¹ := by positivity
  have h2 : 0 ≤ D * (1 + |t|) := by positivity
  nlinarith

end Ostmann

end OAI
