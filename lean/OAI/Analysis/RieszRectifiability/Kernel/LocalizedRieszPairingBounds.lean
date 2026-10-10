import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactRieszPairing

namespace OAI

/-!
# Localized scalar Riesz pairing bounds

Lipschitz cancellation bounds the interior integrand by a weakly singular kernel.
The exterior estimate uses compact support and the normal height to control its
tail, giving quantitative bounds for the localized scalar pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszInteriorIntegrand_weak_kernel_bound {d : ℕ} (p : ℕ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (x y : Ambient d) :
    |rieszInteriorIntegrand (p + 1) e φ (x, y)| ≤
      (‖e‖ * (L : ℝ)) * inverseDistancePow p x y := by
  by_cases hxy : x = y
  · subst y
    simp only [rieszInteriorIntegrand, sub_self, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) L.coe_nonneg)
      (inverseDistancePow_nonneg _ _ _)
  have hd : dist x y ≠ 0 := (dist_pos.mpr hxy).ne'
  have he : |inner ℝ e (kernel (p + 1) x y)| ≤
      ‖e‖ * (dist x y ^ (p + 1))⁻¹ := by
    simpa only [Real.norm_eq_abs, kernel_norm_of_ne _ _ _ hxy] using!
      norm_inner_le_norm (𝕜 := ℝ) e (kernel (p + 1) x y)
  have hl : |φ x - φ y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hφ.dist_le_mul x y
  calc
    _ = |inner ℝ e (kernel (p + 1) x y)| * |φ x - φ y| := by
      rw [rieszInteriorIntegrand, abs_mul]
    _ ≤ (‖e‖ * (dist x y ^ (p + 1))⁻¹) * ((L : ℝ) * dist x y) :=
      mul_le_mul he hl (abs_nonneg _) (by positivity)
    _ = _ := by
      unfold inverseDistancePow
      rw [pow_succ]
      field_simp

theorem rieszInteriorIntegrand_integral_abs_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    (∫ q, |rieszInteriorIntegrand (p + 1) e φ q| ∂ν.prod ν) ≤
      (‖e‖ * (L : ℝ)) *
        (ν.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) := by
  have hi := rieszInteriorIntegrand_integrable_of_lipschitz p C ν hg e φ L hφ r hr hdiam
  have hw := nearPairWeight_integrable p C ν hg r hr
  have hb : ∀ᵐ q ∂ν.prod ν, |rieszInteriorIntegrand (p + 1) e φ q| ≤
      (‖e‖ * (L : ℝ)) * nearPairWeight p r q := by
    filter_upwards [hdiam] with q hq
    have hmem : q ∈ nearPairSet r := by
      simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hq
    rw [nearPairWeight, indicator_of_mem hmem]
    exact rieszInteriorIntegrand_weak_kernel_bound p e φ L hφ q.1 q.2
  calc
    _ ≤ ∫ q, (‖e‖ * (L : ℝ)) * nearPairWeight p r q ∂ν.prod ν :=
      integral_mono_ae hi.abs (hw.const_mul _) hb
    _ = (‖e‖ * (L : ℝ)) * ∫ q, nearPairWeight p r q ∂ν.prod ν :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (nearPairWeight_integral_bound p C ν hg r hr)
      (mul_nonneg (norm_nonneg _) L.coe_nonneg)

theorem rieszFarIntegrand_integral_abs_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    (∫ q, |rieszFarIntegrand m e φ a q|
      ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) ≤
      (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
        (‖e‖ * H * (∫ x in ball a R, |φ x| ∂μ)) * (2 * (C * 2 ^ m / R)) := by
  have hC : 0 ≤ C := hg.1
  let ν := μ.restrict (ball a R)
  let w := affineNormalHeight e a 0
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w ‖e‖₊ hw a R hR
  have hφL2 := lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR
  have hφI : Integrable φ ν := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν :=
    memLp_one_iff_integrable.mp (hφL2.mul hwL2)
  have hmoment : (∫ x, |φ x * w x| ∂ν) ≤
      (‖e‖ * H) * (∫ x, |φ x| ∂ν) := by
    calc
      _ ≤ ∫ x, (‖e‖ * H) * |φ x| ∂ν := by
        apply integral_mono hφw.abs (hφI.abs.const_mul _)
        intro x
        change |φ x * w x| ≤ (‖e‖ * H) * |φ x|
        by_cases hx : φ x = 0
        · simp only [hx, zero_mul, abs_zero, mul_zero, le_refl]
        have hwx : |w x| ≤ ‖e‖ * H := by
          have hb := hw.dist_le_mul x a
          simp only [Real.dist_eq, hwa, sub_zero, coe_nnnorm] at hb
          exact hb.trans (mul_le_mul_of_nonneg_left (hsupport x hx) (norm_nonneg _))
        rw [abs_mul, mul_comm (‖e‖ * H)]
        exact mul_le_mul_of_nonneg_left hwx (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w ‖e‖₊ hw a R hR
  simp only [hwa, abs_zero, zero_div, add_zero, coe_nnnorm] at hZ
  have hb := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable hφI hφw a H R hH hR hHR
    (Eventually.of_forall hsupport) hweighted _ hZ).2
  have heq : rieszFarIntegrand m e φ a = renormalizedNormalIntegrand m w φ a := by
    funext q
    rw [rieszFarIntegrand_eq_normal_sub_correction m e w φ
      (affineNormalHeight_difference e a 0), hwa, mul_zero, zero_mul, sub_zero]
  rw [heq]
  calc
    _ ≤ _ := hb
    _ ≤ 2 ^ (m + 1) * (((‖e‖ * H) * (∫ x, |φ x| ∂ν)) *
        (2 * (C * 2 ^ m / R))) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          ((∫ x, |φ x| ∂ν) * (‖e‖ * (2 * (C * 2 ^ m / R)))) := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmoment (by positivity)) (by positivity)
    _ = _ := by dsimp only [ν]; ring

theorem rieszScalarPairing_compact_lipschitz_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    |rieszScalarPairing (p + 1) μ a R e φ| ≤
      (1 / 2 : ℝ) * ((‖e‖ * (L : ℝ)) *
        (C * R ^ (p + 1) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * R))))) +
      (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) *
        (‖e‖ * H * (∫ x in ball a R, |φ x| ∂μ)) *
          (2 * (C * 2 ^ (p + 1) / R)) := by
  have hC : 0 ≤ C := hg.1
  let ν := μ.restrict (ball a R)
  let : IsFiniteMeasure ν :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hnear := rieszInteriorIntegrand_integral_abs_bound p C ν
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) e φ L hφ
    (2 * R) (by positivity) (ball_restriction_pair_diameter μ a R)
  have hmass := ball_restriction_mass_bound (p + 1) C μ hg a R hR
  have hfar := rieszFarIntegrand_integral_abs_bound (p + 1) C μ hg e φ L hφ
    a H R hH hR hHR hsupport
  simp only [Nat.cast_add, Nat.cast_one] at hfar
  have hn : |∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν| ≤
      (‖e‖ * (L : ℝ)) *
        (C * R ^ (p + 1) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * R)))) := by
    apply abs_integral_le_integral_abs.trans
    apply hnear.trans
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmass (by positivity)) (by positivity)
  have hf := abs_integral_le_integral_abs.trans hfar
  unfold rieszScalarPairing
  dsimp only
  apply (abs_add_le _ _).trans
  apply add_le_add _ hf
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left hn (by norm_num)

end

end RieszRectifiability

end OAI
