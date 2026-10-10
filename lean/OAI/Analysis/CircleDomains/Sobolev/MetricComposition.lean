import OAI.Analysis.CircleDomains.Uniformization.MetricConformality

namespace OAI

/-!
# Metric conformality after a holomorphic change of target

The actual chart differential is multiplied by the nonzero complex
derivative of the target map. Its Gram matrix is consequently multiplied
by the squared norm of that derivative, and its orientation stays positive.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem complex_mul_column_norm (a z : ℂ) :
    (a * z).re ^ 2 + (a * z).im ^ 2 =
      (a.re ^ 2 + a.im ^ 2) * (z.re ^ 2 + z.im ^ 2) := by
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem complex_mul_column_dot (a z w : ℂ) :
    (a * z).re * (a * w).re + (a * z).im * (a * w).im =
      (a.re ^ 2 + a.im ^ 2) * (z.re * w.re + z.im * w.im) := by
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem complex_mul_column_det (a z w : ℂ) :
    (a * z).re * (a * w).im - (a * w).re * (a * z).im =
      (a.re ^ 2 + a.im ^ 2) * (z.re * w.im - w.re * z.im) := by
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem complex_column_norm_pos {a : ℂ} (ha : a ≠ 0) : 0 < a.re ^ 2 + a.im ^ 2 := by
  have hn : a.re ^ 2 + a.im ^ 2 ≠ 0 := by
    intro h
    have hr : a.re = 0 := by nlinarith [sq_nonneg a.im]
    have hi : a.im = 0 := by nlinarith [sq_nonneg a.re]
    exact ha (Complex.ext hr hi)
  exact lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) hn.symm

theorem IsMetricConformalAt.comp_conformal
    {g : (ℝ × ℝ) → FiniteTransfer.PlanarMetric} {f h : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p) (hh : IsConformalAt h (f p)) :
    IsMetricConformalAt g (h ∘ f) p := by
  obtain ⟨hfc, hd, scale, hscale, hxx, hyy, hxy, hdet⟩ := hf
  obtain ⟨hhc, a, ha, hader⟩ := hh
  have hx : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  have had : HasFDerivAt (sphereLocalMap h (f p))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).restrictScalars ℝ)
      (sphereLocalMap f p (chart p p)) := by
    rw [hx]
    exact hader.hasFDerivAt.restrictScalars ℝ
  have hcomp := had.comp (chart p p) hd.hasFDerivAt
  have hcont : Tendsto (fun z => f (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (f p)) := by
    have hfc' : ContinuousAt f (chartSymm p (chart p p)) := by
      rw [chartSymm_chart_self]
      exact hfc
    have hc := hfc'.comp (continuous_chartSymm p).continuousAt
    simpa only [Function.comp_def, chartSymm_chart_self] using hc.tendsto
  have heq : sphereLocalMap (h ∘ f) p =ᶠ[𝓝 (chart p p)]
      (sphereLocalMap h (f p)) ∘ sphereLocalMap f p := by
    filter_upwards [hcont.eventually (eventually_chartSymm_chart (f p))] with z hz
    simp only [sphereLocalMap, Function.comp_apply]
    rw [hz]
  have hdcomp := hcomp.congr_of_eventuallyEq heq
  have hvalue (z : ℂ) : fderiv ℝ (sphereLocalMap (h ∘ f) p) (chart p p) z =
      a * fderiv ℝ (sphereLocalMap f p) (chart p p) z := by
    rw [hdcomp.fderiv]
    change fderiv ℝ (sphereLocalMap f p) (chart p p) z * a =
      a * fderiv ℝ (sphereLocalMap f p) (chart p p) z
    exact mul_comm _ _
  refine ⟨hhc.comp hfc, hdcomp.differentiableAt,
    (a.re ^ 2 + a.im ^ 2) * scale, mul_pos (complex_column_norm_pos ha) hscale, ?_, ?_, ?_, ?_⟩
  · simp only [hvalue, complex_mul_column_norm, hxx]
    ring
  · simp only [hvalue, complex_mul_column_norm, hyy]
    ring
  · simp only [hvalue, complex_mul_column_dot, hxy]
    ring
  · simp only [hvalue, complex_mul_column_det]
    exact mul_pos (complex_column_norm_pos ha) hdet

end CircleDomainRigidity

end

end OAI
