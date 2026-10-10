import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.RenormalizedFarPairing
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedTailDecay

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

def normalizedExteriorBound (m : ℕ) (C B H R b : ℝ) (K : ℝ≥0) (W P : ℝ)
    (ℓ : ℕ) (lastError : ℝ) : ℝ :=
  (2 ^ (m + 1) * (P * (2 * (C * 2 ^ m / R)))) * (1 / 2 : ℝ) ^ ℓ +
    (((m + 1 : ℝ) * 2 ^ (m + 2) * H) * (P * ((B / R) / (1 - b / 2)))) * (b / 2) ^ ℓ +
    (((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
      (P * (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))))) * lastError

theorem normalized_far_pairing_bound_shifted {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (u φ : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (hφm : Measurable φ) (hφ : Integrable φ ν)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H)
    (N ℓ : ℕ) (hℓ : ℓ ≤ N) (δ b W P : ℝ)
    (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : |u a| ≤ W)
    (hφu : Integrable (fun x => φ x * (u x / δ)) ν)
    (hPφ : (∫ x, |φ x| ∂ν) ≤ P) (hPu : (∫ x, |φ x * (u x / δ)| ∂ν) ≤ P)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    Integrable (renormalizedNormalIntegrand m (fun x => u x / δ) φ a)
      (ν.prod (μ.restrict (closedExterior a (R * 2 ^ ℓ)))) ∧
      (∫ q, |renormalizedNormalIntegrand m (fun x => u x / δ) φ a q|
        ∂ν.prod (μ.restrict (closedExterior a (R * 2 ^ ℓ)))) ≤
        normalizedExteriorBound m C B H R b K W P ℓ ((R * 2 ^ N)⁻¹ / δ) := by
  obtain ⟨hweight, hZ⟩ := normalized_weighted_height_tail_shifted m C B μ hg hCB u K hu
    a R hR N ℓ hℓ δ b W hδ hb0 hb2 hW hsecond
  let Z := (B / R) / (1 - b / 2) * (b / 2) ^ ℓ +
    (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))) * ((R * 2 ^ N)⁻¹ / δ)
  have hZ0 : 0 ≤ Z := (integral_nonneg (fun _ =>
    mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))).trans hZ
  have hRℓ : 0 < R * (2 : ℝ) ^ ℓ := by positivity
  have hRle : R ≤ R * (2 : ℝ) ^ ℓ := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  obtain ⟨hi, hb⟩ := renormalized_far_pairing_integrable_and_bound m C μ ν hg
    (fun x => u x / δ) φ (hu.continuous.measurable.div_const δ) hφm hφ hφu
    a H (R * 2 ^ ℓ) hH hRℓ (hHR.trans hRle) hnear hweight Z hZ
  refine ⟨hi, hb.trans ?_⟩
  calc
    _ ≤ 2 ^ (m + 1) * (P * (2 * (C * 2 ^ m / (R * 2 ^ ℓ)))) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * (P * Z) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hPu (by positivity [hg.1])) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hPφ hZ0) (by positivity)
    _ = _ := by
      have hhalf : ((2 : ℝ) ^ ℓ)⁻¹ = (1 / 2 : ℝ) ^ ℓ := by rw [one_div, inv_pow]
      have hbase : 2 * (C * 2 ^ m / (R * 2 ^ ℓ)) =
          (2 * (C * 2 ^ m / R)) * (1 / 2 : ℝ) ^ ℓ := by
        rw [div_eq_mul_inv, mul_inv_rev, hhalf]
        ring
      rw [hbase]
      unfold normalizedExteriorBound Z
      ring

theorem normalized_far_pairings_vanish {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ ν : ℕ → Measure (Ambient d)) [∀ j, SFinite (μ j)] [∀ j, IsFiniteMeasure (ν j)]
    (hg : ∀ j, GlobalUpperGrowth m C (μ j)) (hCB : C * 2 ^ m ≤ B)
    (u φ : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (hφm : ∀ j, Measurable (φ j)) (hφ : ∀ j, Integrable (φ j) (ν j))
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ j, ∀ᵐ x ∂ν j, φ j x ≠ 0 → dist x a ≤ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (b W P : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : ∀ j, |u j a| ≤ W)
    (hφu : ∀ j, Integrable (fun x => φ j x * (u j x / δ j)) (ν j))
    (hPφ : ∀ᶠ j in atTop, (∫ x, |φ j x| ∂ν j) ≤ P)
    (hPu : ∀ᶠ j in atTop, (∫ x, |φ j x * (u j x / δ j)| ∂ν j) ≤ P)
    (hlast : Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsecond : ∀ j k, k < N j → (∫ y in dyadicAnnulus a R k, u j y ^ 2 ∂μ j) ≤
      (B * (R * 2 ^ k) ^ m) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ ℓ : ℕ, ∀ᶠ j in atTop,
      Integrable (renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a)
        ((ν j).prod ((μ j).restrict (closedExterior a (R * 2 ^ ℓ)))) ∧
      (∫ q, |renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a q|
        ∂(ν j).prod ((μ j).restrict (closedExterior a (R * 2 ^ ℓ)))) < ε := by
  intro ε hε
  let A₀ := 2 ^ (m + 1) * (P * (2 * (C * 2 ^ m / R)))
  let A₁ := ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * (P * ((B / R) / (1 - b / 2)))
  let A₂ := ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
    (P * (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))))
  have hg₀ := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul A₀
  have hg₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ b / 2)
    (by linarith : b / 2 < 1)).const_mul A₁
  have hgeom : Tendsto (fun ℓ : ℕ => A₀ * (1 / 2 : ℝ) ^ ℓ + A₁ * (b / 2) ^ ℓ) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using! hg₀.add hg₁
  obtain ⟨ℓ, hℓ⟩ := (hgeom.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨ℓ, ?_⟩
  have hrem : Tendsto (fun j => A₂ * ((R * (2 : ℝ) ^ N j)⁻¹ / δ j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using! hlast.const_mul A₂
  filter_upwards [hN.eventually (eventually_ge_atTop ℓ), hrem.eventually (gt_mem_nhds (half_pos hε)),
    hPφ, hPu] with j hjN hjrem hjPφ hjPu
  obtain ⟨hi, hb⟩ := normalized_far_pairing_bound_shifted m C B (μ j) (ν j) (hg j) hCB
    (u j) (φ j) K (hu j) (hφm j) (hφ j) a H R hH hR hHR (hnear j)
    (N j) ℓ hjN (δ j) b W P (hδ j) hb0 hb2 (hW j) (hφu j) hjPφ hjPu (hsecond j)
  refine ⟨hi, hb.trans_lt ?_⟩
  change A₀ * (1 / 2 : ℝ) ^ ℓ + A₁ * (b / 2) ^ ℓ + A₂ * ((R * 2 ^ N j)⁻¹ / δ j) < ε
  linarith

end

end RieszRectifiability

end OAI
