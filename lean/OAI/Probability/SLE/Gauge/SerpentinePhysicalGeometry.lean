import OAI.Probability.SLE.Gauge.SerpentinePhysicalMass

namespace OAI

/-! Properness and half-plane geometry of the physical fitted chart.
Only the normalized chart is used in the uniform probabilistic iteration. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

theorem physicalFitChart_geometry {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    Continuous (physicalFitChart s w m) ∧ InjOn (physicalFitChart s w m) closedRibbon ∧
      (∀ z ∈ closedRibbon, 0 < z.re → physicalFitChart s w m z ∈ upperHalfPlane) ∧
      Tendsto (fun t : ℝ => ‖physicalFitChart s w m (t : ℂ)‖) atTop atTop := by
  have hℓ := fit_width_pos hs hm
  refine ⟨continuous_const.mul (fitChart_continuous hs w hw hm), ?_, ?_, ?_⟩
  · intro z hz z' hz' he
    apply fitChart_injective hs w hw hm hz hz'
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hℓ.ne') he
  · intro z hz hz0
    have hh : 0 < (fitChart s w m z).im := fitChart_upper hs w hw hm z hz hz0
    change 0 < ((ribbonWidth (halfHeight s) m : ℂ) * fitChart s w m z).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using mul_pos hℓ hh
  · have hn : Tendsto (fun t : ℝ => ‖fitChart s w m (t : ℂ)‖) atTop atTop := by
      simpa only [fitChart, normalRibbon, Complex.ofReal_im, Complex.ofReal_re,
        Complex.ofReal_zero, zero_mul, zero_add, add_zero, fitSpine, Function.comp_def] using
        tendsto_norm_cocompact_atTop.comp
          (completeSpine_escape m (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m))
    have hh := hn.const_mul_atTop hℓ
    simpa only [physicalFitChart, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ] using hh

lemma physicalFitChart_zero {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) : physicalFitChart s w m 0 = 0 := by
  have he := fitChart_initial hs w hw hm
    (z := 0) (show (0 : ℂ).re ≤ fitHeight m by unfold fitHeight; positivity)
  simp only [physicalFitChart, he, mul_zero]

end SLEExactGauge.Serpentine

end

end OAI
