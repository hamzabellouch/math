import OAI.Probability.SLE.Geometry.ScaledMarkedKernel
import OAI.Probability.SLE.Geometry.NormalizedMarkedState

namespace OAI

/-! Centered-density domination for the actual capacity-normalized restart.
The fresh marked point has unit modulus in the application; its source
radius level is transported to the original physical radius level. -/

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def normalizedRestartDriver (U : ℝ≥0 → ℝ) (T a : ℝ≥0) (t : ℝ≥0) : ℝ :=
  (U (T + a ^ 2 * t) - U T) / (a : ℝ)

lemma normalized_restart_witness
    {U : ℝ≥0 → ℝ} (T a : ℝ≥0) (ha : 0 < a)
    {β : ℝ≥0 → ℂ} {G' F' : ℝ≥0 → ℂ → ℂ}
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F') :
    IsCapacityTwoWitness (fun t => U (T + t) - U T)
      (sourceScaleTrace a β) (sourceScaleChart a G') (sourceScaleChart a F') := by
  have hh := source_scale_witness a ha _ β G' F' hb
  have htime (t : ℝ≥0) : a ^ 2 * sourceScaleTime a t = t := by
    dsimp only [sourceScaleTime]
    field_simp
  have hdriver : (fun t => (a : ℝ) * normalizedRestartDriver U T a (sourceScaleTime a t)) =
      (fun t => U (T + t) - U T) := by
    funext t
    unfold normalizedRestartDriver
    rw [htime t]
    field_simp
  rwa [hdriver] at hh

lemma initialGreen_pos_real_mul
    (κ : ℝ) (a : ℝ) (ha : 0 < a) (w : ℂ) (hw : w ∈ upperHalfPlane) :
    initialGreen κ ((a : ℂ) * w) = a ^ (-codimension κ) * initialGreen κ w := by
  have him : 2 * ((a : ℂ) * w).im = a * (2 * w.im) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  rw [initialGreen, him, sin_arg_pos_real_mul a ha,
    Real.mul_rpow ha.le (mul_pos (by norm_num) hw).le, initialGreen, mul_assoc]

/-- The normalized fresh finite-centered density is dominated by the
terminal physical density, relative to the density at the actual past stop. -/
theorem IsCapacityTwoWitness.normalized_restart_stopped_green_lower
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T a : ℝ≥0) (ha : 0 < a)
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F')
    (κ : ℝ) (w : ℂ) (hwH : w ∈ upperHalfPlane) (u v : ℝ)
    (hbase : fullRadius G T (F T ((a : ℂ) * w + (U T : ℂ))) =
      (2 * (F T ((a : ℂ) * w + (U T : ℂ))).im) * Real.exp (-u)) :
    greenDensity κ U γ G T (F T ((a : ℂ) * w + (U T : ℂ))) *
        (stoppedGreen κ (normalizedRestartDriver U T a) β G' w v / initialGreen κ w) ≤
      stoppedGreen κ U γ G (F T ((a : ℂ) * w + (U T : ℂ))) (u + v) := by
  have hbup := normalized_restart_witness T a ha hb
  have haR : 0 < (a : ℝ) := ha
  have hwup : (a : ℂ) * w ∈ upperHalfPlane := by
    change 0 < ((a : ℂ) * w).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      mul_pos haR hwH
  have hV : Continuous (normalizedRestartDriver U T a) := by
    unfold normalizedRestartDriver
    fun_prop
  by_cases hfinite : radiusLevelTime β G' w v < ∞
  · obtain ⟨t, ht, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G' w v hfinite
    have htu : (a : ℂ) * w ∈ survivingDomain (sourceScaleTrace a β) (a ^ 2 * t) := by
      rw [source_scale_domain_iff a _ ha β, source_scale_time_mul_sq a t ha,
        mul_div_cancel_left₀ w (by exact_mod_cast ha.ne' : (a : ℂ) ≠ 0)]
      exact ht
    have hRu : fullRadius (sourceScaleChart a G') (a ^ 2 * t) ((a : ℂ) * w) =
        (2 * ((a : ℂ) * w).im) * Real.exp (-v) := by
      rw [hb.scaled_radius a ha t w ht, hR]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      ring
    have hphysical := hw.restart_level_of_live_source hU T hbup ((a : ℂ) * w) u v hbase
      (a ^ 2 * t) htu hRu
    have hgreen := hw.restart_green_composition hU T hbup κ (a ^ 2 * t) ((a : ℂ) * w) htu
    have hscale := hb.scaled_green hV a ha κ t w ht
    have hdriver : (fun t => (a : ℝ) * normalizedRestartDriver U T a (sourceScaleTime a t)) =
        (fun t => U (T + t) - U T) := by
      funext r
      unfold normalizedRestartDriver sourceScaleTime
      have htime : a ^ 2 * (r / a ^ 2) = r := by field_simp
      rw [htime]
      field_simp
    rw [hdriver] at hscale
    rw [hscale] at hgreen
    rw [stoppedGreen_eq_of_live_level hV hb κ w v t ht hR,
      stoppedGreen_eq_of_live_level hU hw κ _ _ (T + a ^ 2 * t)
        (hw.restart_forward_composition T hbup (a ^ 2 * t) ((a : ℂ) * w) htu).1 hphysical.1,
      hgreen, hw.restart_green_initial hU T hbup κ ((a : ℂ) * w) hwup,
      initialGreen_pos_real_mul κ a haR w hwH]
    exact le_of_eq (by field_simp [(initialGreen_pos κ w hwH).ne'])
  · simp only [stoppedGreen, ite_eq_right hfinite, zero_div, mul_zero]
    exact stoppedGreen_nonneg hw κ _ _

end SLEExactGauge

end

end OAI
