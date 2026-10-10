import OAI.MathematicalPhysics.Boltzmann.Branching.HotQuadraticGain

namespace OAI

/-! # Regular chart volume and transverse inverse-distance averaging -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain

namespace BoltzmannNonuniqueness.RegularChart

def ballMass (v p : Velocity) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, ∫⁻ s : ℝ, if ‖chart v p z s - v‖ ≤ R then 1 else 0

theorem ballMass_le {R : ℝ} (hR : 0 ≤ R) (v p : Velocity) (hn : normal v p ≠ 0) :
    ballMass v p R ≤ ENNReal.ofReal (4 * R ^ 2) := by
  let m := inner ℝ (TransverseLine.quarterTurn (direction (normal v p))) (transverse v)
  have he : ‖direction (normal v p)‖ = 1 := norm_direction hn
  have hpoint (z s : ℝ) :
      (if ‖chart v p z s - v‖ ≤ R then (1 : ℝ≥0∞) else 0) ≤
      (Icc (-R) R).indicator (fun _ => (1 : ℝ≥0∞)) z *
        (Icc (m - R) (m + R)).indicator (fun _ => (1 : ℝ≥0∞)) s := by
    by_cases hb : ‖chart v p z s - v‖ ≤ R
    · have hs : s ∈ ballLineRegion (direction (normal v p)) (transverse v)
          (offset v p - slope v p * z) z R := by
        rw [← sq_le_sq₀ (norm_nonneg _) hR, chart_displacement_norm_sq] at hb
        exact hb
      have hz : z ∈ Icc (-R) R := by
        have h := hs
        change ‖TransverseLine.line _ _ _ - _‖ ^ 2 + z ^ 2 ≤ R ^ 2 at h
        have hsq : 0 ≤ ‖TransverseLine.line (direction (normal v p))
            (offset v p - slope v p * z) s - transverse v‖ ^ 2 := sq_nonneg _
        have ha : |z| ≤ R := by nlinarith [sq_abs z, abs_nonneg z]
        exact abs_le.mp ha
      have hs' := ballLineRegion_subset_rectangle hR _ _ he _ _ hs
      change s ∈ Icc (m - R) (m + R) at hs'
      simp only [ite_eq_left hb, indicator_of_mem hz, indicator_of_mem hs', mul_one]
      exact le_rfl
    · rw [ite_eq_right hb]
      exact bot_le
  calc
    _ ≤ ∫⁻ z : ℝ, ∫⁻ s : ℝ,
        (Icc (-R) R).indicator (fun _ => (1 : ℝ≥0∞)) z *
          (Icc (m - R) (m + R)).indicator (fun _ => (1 : ℝ≥0∞)) s :=
      lintegral_mono (fun z => lintegral_mono (hpoint z))
    _ = ENNReal.ofReal (4 * R ^ 2) := by
      simp_rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Icc)]
      rw [lintegral_mul_const' _ _ (by simp)]
      simp only [lintegral_indicator measurableSet_Icc, lintegral_one,
        Measure.restrict_apply_univ, Real.volume_Icc]
      have h₁ : m + R - (m - R) = 2 * R := by ring
      have h₂ : R - -R = 2 * R := by ring
      rw [h₁, h₂, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem inverse_norm_le_extendedKernel (q : ℝ) (v p : Transverse) :
    ENNReal.ofReal (‖v - p‖⁻¹) ≤ extendedKernel q v p := by
  classical
  by_cases h : RegularTransverse v p
  · rw [extendedKernel, ite_eq_left h]
    apply ENNReal.ofReal_le_ofReal
    unfold kernel
    have hp : 0 ≤ |inner ℝ (direction v) (‖v - p‖⁻¹ • (v - p))| ^ (1 - q) :=
      Real.rpow_nonneg (abs_nonneg _) _
    rw [inv_eq_one_div]
    rw [inv_eq_one_div] at hp
    exact div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)
  · rw [extendedKernel, ite_eq_right h]
    exact le_top

theorem transverseLaw_inverse_norm_bound {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, ENNReal.ofReal (‖v - p‖⁻¹) ∂transverseLaw d) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  apply (lintegral_mono (inverse_norm_le_extendedKernel q v)).trans
  obtain rfl | hdpos := hd.eq_or_lt
  · simpa only [transverseLaw, ite_true] using atom_extendedKernel_lintegral_le q hv
  · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using
      gaussian_extendedKernel_lintegral_le hq₁ hq₂ hdpos hv

theorem sheet_inverse_norm_bound {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, ENNReal.ofReal (‖normal v p‖⁻¹) ∂sheetLaw d ρ) ≤
      ENNReal.ofReal (expectationConstant q / ‖transverse v‖) := by
  have := transverseLaw_isProbabilityMeasure hd
  rw [sheetLaw, lintegral_map_equiv]
  simp_rw [normal_join]
  have hm : Measurable (fun p : Transverse × ℝ =>
      ENNReal.ofReal (‖transverse v - p.1‖⁻¹)) := by fun_prop
  rw [lintegral_prod _ hm.aemeasurable]
  simpa only [lintegral_const, measure_univ, mul_one] using
    transverseLaw_inverse_norm_bound hq₁ hq₂ hd hv

theorem one_ball_sheet_bound {q d R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 0 ≤ R) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    chartRegionGain (sheetLaw d ρ) (fun _ => 1) v (ballRegion v R) ≤
      (2 * ENNReal.ofReal (4 * R ^ 2)) *
        ENNReal.ofReal (expectationConstant q / ‖transverse v‖) := by
  have hp (p : Velocity) :
      ENNReal.ofReal (‖normal v p‖⁻¹) * ballMass v p R ≤
        ENNReal.ofReal (‖normal v p‖⁻¹) * ENNReal.ofReal (4 * R ^ 2) := by
    by_cases hn : normal v p = 0
    · simp [hn]
    · exact mul_le_mul' le_rfl (ballMass_le hR v p hn)
  change 2 * (∫⁻ p, ENNReal.ofReal (‖normal v p‖⁻¹) * ballMass v p R ∂sheetLaw d ρ) ≤ _
  calc
    _ ≤ 2 * (∫⁻ p, ENNReal.ofReal (‖normal v p‖⁻¹) *
        ENNReal.ofReal (4 * R ^ 2) ∂sheetLaw d ρ) :=
      mul_le_mul' le_rfl (lintegral_mono hp)
    _ = (2 * ENNReal.ofReal (4 * R ^ 2)) *
        (∫⁻ p, ENNReal.ofReal (‖normal v p‖⁻¹) ∂sheetLaw d ρ) := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl (sheet_inverse_norm_bound hq₁ hq₂ hd hv ρ)

end BoltzmannNonuniqueness.RegularChart

end

end OAI
