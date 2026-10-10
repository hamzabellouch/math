import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ShiftedHeightTail

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem normalized_last_radius_dyadic_identity (R : ℝ) (hR : 0 < R) (j : ℕ) :
    (R * (2 : ℝ) ^ (2 * j + 3))⁻¹ / (1 / 2 : ℝ) ^ j =
      (R * 8)⁻¹ * (1 / 2 : ℝ) ^ j := by
  rw [pow_add, pow_mul, div_pow]
  norm_num
  field_simp
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num

theorem normalized_last_radius_dyadic_tendsto (R : ℝ) (hR : 0 < R) :
    Tendsto (fun j : ℕ => (R * (2 : ℝ) ^ (2 * j + 3))⁻¹ / (1 / 2 : ℝ) ^ j) atTop (𝓝 0) := by
  simp only [normalized_last_radius_dyadic_identity R hR]
  simpa only [mul_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((R * 8)⁻¹)

theorem normalized_height_tails_vanish {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth m C (μ j))
    (hCB : C * 2 ^ m ≤ B) (u : ℕ → Ambient d → ℝ)
    (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j)) (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (b W : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : ∀ j, |u j a| ≤ W)
    (hlast : Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsecond : ∀ j k, k < N j → (∫ y in dyadicAnnulus a R k, u j y ^ 2 ∂μ j) ≤
      (B * (R * 2 ^ k) ^ m) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ ℓ : ℕ, ∀ᶠ j in atTop,
      IntegrableOn (fun y => |u j y / δ j| * inverseDistancePow (m + 2) a y)
        (closedExterior a (R * 2 ^ ℓ)) (μ j) ∧
      (∫ y in closedExterior a (R * 2 ^ ℓ), |u j y / δ j| * inverseDistancePow (m + 2) a y ∂μ j) < ε := by
  intro ε hε
  let A : ℝ := (B / R) / (1 - b / 2)
  let D : ℝ := ((K : ℝ) + W / R) * (2 * (C * 2 ^ m))
  have hratio0 : 0 ≤ b / 2 := by positivity
  have hratio1 : b / 2 < 1 := by linarith
  have hgeom : Tendsto (fun ℓ : ℕ => A * (b / 2) ^ ℓ) atTop (𝓝 0) := by
    simpa only [mul_zero] using! (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).const_mul A
  obtain ⟨ℓ, hℓ⟩ := (hgeom.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨ℓ, ?_⟩
  have hrem : Tendsto (fun j => D * ((R * (2 : ℝ) ^ N j)⁻¹ / δ j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using! hlast.const_mul D
  filter_upwards [hN.eventually (eventually_ge_atTop ℓ), hrem.eventually (gt_mem_nhds (half_pos hε))]
    with j hjN hjrem
  obtain ⟨hi, hb⟩ := normalized_weighted_height_tail_shifted m C B (μ j) (hg j) hCB (u j) K
    (hu j) a R hR (N j) ℓ hjN (δ j) b W (hδ j) hb0 hb2 (hW j) (hsecond j)
  refine ⟨hi, hb.trans_lt ?_⟩
  change A * (b / 2) ^ ℓ + D * ((R * 2 ^ N j)⁻¹ / δ j) < ε
  linarith

end

end RieszRectifiability

end OAI
