import OAI.Probability.SLE.Geometry.RestartGreenKernel
import OAI.Probability.SLE.InteriorDiskProof

namespace OAI

/-! Exact scaling of the marked radius, angle, and Green kernel. These
identities normalize a random restarted marked point to modulus one. -/

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma source_scale_time_mul_sq (c t : ℝ≥0) (hc : 0 < c) :
    sourceScaleTime c (c ^ 2 * t) = t := by
  unfold sourceScaleTime
  exact mul_div_cancel_left₀ t (pow_ne_zero 2 hc.ne')

lemma sin_arg_pos_real_mul (c : ℝ) (hc : 0 < c) (z : ℂ) :
    Real.sin (Complex.arg ((c : ℂ) * z)) = Real.sin (Complex.arg z) := by
  rw [Complex.sin_arg, Complex.sin_arg, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hc]
  by_cases hz : z = 0
  · simp [hz]
  · field_simp

lemma IsCapacityTwoWitness.scaled_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (c : ℝ≥0) (hc : 0 < c)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    deriv (sourceScaleChart c G (c ^ 2 * t)) ((c : ℂ) * z) = deriv (G t) z := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdiv : (c : ℂ) * z / (c : ℂ) = z := mul_div_cancel_left₀ z hcC
  have hGd := ((hw.2.2.2.1 t).differentiableAt
    ((isOpen_survivingDomain hw.1 t).mem_nhds hz)).hasDerivAt
  have hGd' : HasDerivAt (G t) (deriv (G t) z) ((c : ℂ) * z / (c : ℂ)) := by
    rwa [hdiv]
  have hd := (hGd'.comp ((c : ℂ) * z)
    ((hasDerivAt_id ((c : ℂ) * z)).div_const (c : ℂ))).const_mul (c : ℂ)
  change deriv (fun w => (c : ℂ) * G (sourceScaleTime c (c ^ 2 * t)) (w / (c : ℂ)))
    ((c : ℂ) * z) = _
  rw [source_scale_time_mul_sq c t hc]
  have hcoeff : (c : ℂ) * (deriv (G t) z * (1 / (c : ℂ))) = deriv (G t) z := by
    field_simp
  simpa only [Function.comp_def, id_eq, hcoeff] using hd.deriv

lemma IsCapacityTwoWitness.scaled_radius
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (c : ℝ≥0) (hc : 0 < c)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    fullRadius (sourceScaleChart c G) (c ^ 2 * t) ((c : ℂ) * z) =
      (c : ℝ) * fullRadius G t z := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [fullRadius, hw.scaled_derivative c hc t z hz,
    sourceScaleChart, source_scale_time_mul_sq c t hc, mul_div_cancel_left₀ z hcC,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, fullRadius]
  ring

lemma IsCapacityTwoWitness.scaled_green
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (c : ℝ≥0) (hc : 0 < c) (κ : ℝ) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) :
    greenDensity κ (fun t => (c : ℝ) * U (sourceScaleTime c t))
        (sourceScaleTrace c γ) (sourceScaleChart c G) (c ^ 2 * t) ((c : ℂ) * z) =
      (c : ℝ) ^ (-codimension κ) * greenDensity κ U γ G t z := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hscaled : (c : ℂ) * z ∈ survivingDomain (sourceScaleTrace c γ) (c ^ 2 * t) := by
    rw [source_scale_domain_iff c _ hc γ, source_scale_time_mul_sq c t hc,
      mul_div_cancel_left₀ z hcC]
    exact hz
  have hcenter : sourceScaleChart c G (c ^ 2 * t) ((c : ℂ) * z) -
      ((c : ℝ) * U (sourceScaleTime c (c ^ 2 * t)) : ℝ) =
      (c : ℂ) * (G t z - (U t : ℂ)) := by
    rw [sourceScaleChart, source_scale_time_mul_sq c t hc, mul_div_cancel_left₀ z hcC,
      Complex.ofReal_mul]
    ring
  rw [greenDensity, ite_eq_left hscaled, hw.scaled_radius c hc t z hz, hcenter,
    sin_arg_pos_real_mul c hc, Real.mul_rpow c.coe_nonneg (hw.fullRadius_positive hU t z hz).le,
    greenDensity, ite_eq_left hz, mul_assoc]

end SLEExactGauge

end

end OAI
