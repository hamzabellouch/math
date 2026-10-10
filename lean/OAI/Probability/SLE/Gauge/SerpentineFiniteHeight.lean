import OAI.Probability.SLE.Gauge.SerpentineTerminalGuide

namespace OAI

/-! Every point in the finite experiment, before its final integer front,
is below the height used to attach the marked hook. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma array_normal_im_upper_before_end {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : 0 ≤ z.re ∧ |z.im| ≤ 1) (hze : z.re ≤ arrayEnd m (2 * m) + 1) :
    (normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) z).im ≤ 401 * m := by
  have hh : (0 : ℝ) < 100 * m := by positivity
  by_cases he : z.re ≤ arrayEnd m (2 * m)
  · rcases array_pieces m (2 * m) ⟨hz.1, he⟩ with ⟨i, hi, u, hu, _, hs, hT⟩ |
      ⟨i, hi, u, hu, _, hs, hT⟩
    · simp only [normalRibbon]
      rw [hs, hT, normal_straight_eq hm]
      have hb := columnPoint_bound hh hm hi 0 (straight_height_bound m i hu) hz.2
      rw [dist_zero_right] at hb
      exact (Complex.im_le_norm _).trans (by linarith)
    · simp only [normalRibbon]
      rw [hs, hT, normal_circular_eq hm]
      have hb := turnPoint_bound hh hm (show i + 1 ≤ 2 * m by omega) 0 (u / 50) hz.2
      rw [dist_zero_right] at hb
      exact (Complex.im_le_norm _).trans (by linarith)
  · have hE : columnEntry 0 m (2 * m) ≤ z.re := by
      have h := lt_of_not_ge he
      dsimp only [arrayEnd] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have ht := array_normal_terminal hm (a := z.im) hE
    rw [Complex.re_add_im z] at ht
    rw [ht, columnPoint_im]
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp only [arrayEnd] at hze
    simp only [Complex.zero_im, zero_add]
    linarith

lemma lowConnector_im_mono {r X : ℝ} (hr : 0 < r) (hX : 2 * r < X) (H : ℝ) :
    Monotone (fun t => (lowConnector H r X t).im) :=
  monotone_of_hasDerivAt_nonneg
    (fun t => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (lowConnector_hasDerivAt hr hX t))
    (fun t => (lowConnectorTangent_nonneg (H := H) hr hX t).2)

lemma physicalFitChart_before_entry_height {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1) (hz : z.re ≤ fitEntry s w m) :
    (physicalFitChart s w m z).im ≤ w.im := by
  obtain ⟨hr, hx, hy, _⟩ := fit_parameters hs w hw hm
  have hA4 : connectorFourth (fitHeight m) (fitRadius m) (fitX s w m) < fitEntry s w m := by
    unfold fitEntry connectorEntry
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hcenter := lowConnector_im_mono (by linarith : 0 < fitRadius m) hx (fitHeight m) hz
  dsimp only at hcenter
  rw [(lowConnector_after hA4).1] at hcenter
  simp only [connectorTail, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add] at hcenter
  have hAeq : fitHeight m + 2 * fitRadius m +
      (fitEntry s w m - connectorFourth (fitHeight m) (fitRadius m) (fitX s w m)) = fitY s w m := by
    unfold fitEntry connectorEntry
    ring
  rw [hAeq] at hcenter
  have hnormal : (normalRibbon (lowConnector (fitHeight m) (fitRadius m) (fitX s w m))
      (lowConnectorTangent (fitHeight m) (fitRadius m) (fitX s w m)) z).im ≤ fitY s w m + 1 := by
    have hb : ‖normalRibbon (lowConnector (fitHeight m) (fitRadius m) (fitX s w m))
      (lowConnectorTangent (fitHeight m) (fitRadius m) (fitX s w m)) z -
        lowConnector (fitHeight m) (fitRadius m) (fitX s w m) z.re‖ ≤ 1 := by
      simp only [normalRibbon, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, lowConnectorTangent_norm, mul_one]
      exact ha
    have hi := (Complex.abs_im_le_norm _).trans hb
    rw [Complex.sub_im] at hi
    linarith [le_abs_self ((normalRibbon (lowConnector (fitHeight m) (fitRadius m) (fitX s w m))
      (lowConnectorTangent (fitHeight m) (fitRadius m) (fitX s w m)) z).im -
        (lowConnector (fitHeight m) (fitRadius m) (fitX s w m) z.re).im)]
  have hh := mul_le_mul_of_nonneg_left hnormal (fit_width_pos hs hm).le
  have hY := fit_scaledY hs w hm
  have hwidth := fit_width_le hs hm
  change ((ribbonWidth (halfHeight s) m : ℂ) *
    normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).im ≤ _
  rw [complete_normal_of_le m _ _ _ _ hz]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  nlinarith

lemma physicalFitChart_finite_height_lt_two {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) {m : ℕ} (hm : 0 < m)
    {z : ℂ} (hz : z ∈ closedRibbon) (hzK : z.re ≤ fitCompletion s w m) :
    (physicalFitChart s w m z).im < 2 := by
  have hwi := (Complex.im_le_norm w).trans hw1
  by_cases hA : z.re ≤ fitEntry s w m
  · exact (physicalFitChart_before_entry_height hs w hw hm hz.2 hA).trans_lt (by linarith)
  · have hz' : 0 ≤ (z - (fitEntry s w m : ℂ)).re ∧
        |(z - (fitEntry s w m : ℂ)).im| ≤ 1 := by
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      exact ⟨by linarith, hz.2⟩
    have hze : (z - (fitEntry s w m : ℂ)).re ≤ arrayEnd m (2 * m) + 1 := by
      have hh := (fitCompletion_bounds hs w hw hm).2
      simp only [Complex.sub_re, Complex.ofReal_re, arrayEnd]
      linarith
    have hb := mul_le_mul_of_nonneg_left (array_normal_im_upper_before_end hm hz' hze)
      (fit_width_pos hs hm).le
    have hmℓ := fit_width_mul hs hm
    have hcenter := congrArg Complex.im (fit_scaled_arrayCenter hs w hm)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      positiveCenter, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, zero_add] at hcenter
    change ((ribbonWidth (halfHeight s) m : ℂ) *
      normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).im < _
    rw [complete_normal_of_gt m _ _ _ _ (lt_of_not_ge hA)]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im]
    unfold fitEntry at hb
    nlinarith

end SLEExactGauge.Serpentine

end

end OAI
