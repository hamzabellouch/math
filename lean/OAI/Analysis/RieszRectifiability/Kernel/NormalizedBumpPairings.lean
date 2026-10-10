import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LocalizedRieszPairingBounds
import OAI.Analysis.RieszRectifiability.Nets.ScaledBallBumps

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

def normalizedBumpPairingBound (p : ℕ) (C c : ℝ) : ℝ :=
  8 * C ^ 2 * 4 ^ (p + 1) * 2 ^ (p + 1) * 2 ^ p / c +
    (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) * C * 2 ^ (p + 1)

theorem normalizedBumpPairingBound_nonneg (p : ℕ) (C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) : 0 ≤ normalizedBumpPairingBound p C c := by
  unfold normalizedBumpPairingBound
  positivity

theorem normalized_bump_pairing_uniform_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (hnonneg : ∀ x, 0 ≤ φ x) (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ 2 * r)
    (hmean : (∫ x, φ x ∂μ) = 1)
    (hL : (L : ℝ) ≤ (c * r ^ (p + 1 + 1))⁻¹) (e : Ambient d) :
    |rieszScalarPairing (p + 1) μ a (4 * r) e φ| ≤
      ‖e‖ * normalizedBumpPairingBound p C c := by
  have hC : 0 ≤ C := hg.1
  have hφzero : ∀ x ∉ ball a (4 * r), φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : 2 * r < 4 * r))
  have hmass : (∫ x in ball a (4 * r), |φ x| ∂μ) = 1 := by
    simp only [abs_of_nonneg (hnonneg _)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hφzero, hmean]
  have hb := rieszScalarPairing_compact_lipschitz_bound p C μ hg e φ L hφ a
    (2 * r) (4 * r) (by positivity) (by positivity) (by linarith) hsupport
  rw [hmass] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (1 / 2 : ℝ) * ((‖e‖ * (c * r ^ (p + 1 + 1))⁻¹) *
        (C * (4 * r) ^ (p + 1) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * (4 * r)))))) +
        (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) *
          (‖e‖ * (2 * r) * 1) * (2 * (C * 2 ^ (p + 1) / (4 * r))) := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL (norm_nonneg _)) (by positivity)
    _ = _ := by
      unfold normalizedBumpPairingBound
      simp only [mul_pow, pow_succ]
      field_simp
      ring

theorem exists_uniformly_bounded_normalized_bump {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (hmass : ENNReal.ofReal (c * r ^ (p + 1)) ≤ μ (ball a r)) :
    ∃ (φ : Ambient d → ℝ) (L : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith L φ ∧ (∀ x, 0 ≤ φ x) ∧
      (∀ x, φ x ≠ 0 → dist x a ≤ 2 * r) ∧ (∫ x, φ x ∂μ) = 1 ∧
      ∀ e : Ambient d, |rieszScalarPairing (p + 1) μ a (4 * r) e φ| ≤
        ‖e‖ * normalizedBumpPairingBound p C c := by
  obtain ⟨φ, L, hcomp, hφ, hn, hs, hm, hL⟩ :=
    exists_normalized_ball_bump (p + 1) C c μ hg hc a r hr hmass
  exact ⟨φ, L, hcomp, hφ, hn, hs, hm,
    fun e => normalized_bump_pairing_uniform_bound p C c μ hg hc a r hr φ L hφ hn hs hm hL e⟩

end

end RieszRectifiability

end OAI
