import OAI.Probability.SLE.Geometry.RoundedConnectorCurve
import OAI.Probability.SLE.Gauge.NormalRibbonInjectivity

namespace OAI

/-! Uniform local geometry of the actual rounded connector. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

lemma shifted_lipschitz {f : ℝ → ℂ} {K : ℝ≥0} (hf : LipschitzWith K f) (a : ℝ) :
    LipschitzWith K (fun t => f (t - a)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro t u
  simpa only [dist_sub_right] using hf.dist_le_mul (t - a) (u - a)

lemma lowConnectorTangent_lipschitz {H r X : ℝ} (hr : 50 ≤ r) (hX : 2 * r < X) :
    LipschitzWith (1 / 50) (lowConnectorTangent H r X) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hc1, hc2, hc3⟩ := connector_cuts (H := H) hr0 hX
  have hI : LipschitzWith (1 / 50) (fun _ : ℝ => Complex.I) :=
    (LipschitzWith.const _).weaken (by norm_num)
  have h1 : LipschitzWith (1 / 50) (fun _ : ℝ => (1 : ℂ)) :=
    (LipschitzWith.const _).weaken (by norm_num)
  have hq := shifted_lipschitz (quarterTangent_lipschitz hr) H
  have hu := shifted_lipschitz (upperQuarterTangent_lipschitz hr) (connectorThird H r X)
  have hj1 := curveJoin_lipschitz (c := H) hI hq (by simp [quarterTangent_zero])
  have hj2 := curveJoin_lipschitz (c := connectorSecond H r) hj1 h1 (by
    rw [curveJoin_of_gt hc1]
    simp [connectorSecond, quarterTangent_end hr0])
  have hj3 := curveJoin_lipschitz (c := connectorThird H r X) hj2 hu (by
    rw [curveJoin_of_gt hc2]
    simp [upperQuarterTangent_zero hr0])
  exact curveJoin_lipschitz (c := connectorFourth H r X) hj3 hI (by
    rw [curveJoin_of_gt hc3]
    simp [connectorFourth, upperQuarterTangent_end])

lemma lowConnector_initial {H r X t : ℝ} (hr : 0 < r) (hX : 2 * r < X) (ht : t ≤ H) :
    lowConnector H r X t = (t : ℂ) * Complex.I ∧
      lowConnectorTangent H r X t = Complex.I := by
  obtain ⟨hc1, hc2, hc3⟩ := connector_cuts (H := H) hr hX
  have ht2 : t ≤ connectorSecond H r := ht.trans hc1.le
  have ht3 : t ≤ connectorThird H r X := ht2.trans hc2.le
  have ht4 : t ≤ connectorFourth H r X := ht3.trans hc3.le
  simp only [lowConnector, lowConnectorTangent, curveJoin_of_le ht4,
    curveJoin_of_le ht3, curveJoin_of_le ht2, curveJoin_of_le ht, connectorInitial, and_self]

lemma lowConnector_normal_patch_bounds {H r X : ℝ} (hr : 50 ≤ r) (hX : 2 * r < X) (k : ℝ) :
    LipschitzOnWith 2 (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X))
      (RibbonCoordinates.ribbonStepPatch k) ∧
    ∀ z ∈ RibbonCoordinates.ribbonStepPatch k,
      ∀ w ∈ RibbonCoordinates.ribbonStepPatch k,
        dist z w ≤ 2 * dist (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z)
          (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) w) := by
  have hr0 : 0 < r := by linarith
  have hbound z (hz : z ∈ RibbonCoordinates.ribbonStepPatch k)
      w (hw : w ∈ RibbonCoordinates.ribbonStepPatch k) :=
    normalRibbon_patch_bounds (lowConnector H r X) (lowConnectorTangent H r X) (k - 1) (k + 3)
      (by ring_nf; norm_num)
      (fun t _ => (lowConnector_hasDerivAt hr0 hX t).hasDerivWithinAt)
      (fun t _ => lowConnectorTangent_norm H r X t)
      (lowConnectorTangent_lipschitz hr hX).lipschitzOnWith
      z w ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩ ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  exact ⟨lipschitzOnWith_iff_dist_le_mul.mpr (fun z hz w hw => (hbound z hz w hw).1),
    fun z hz w hw => (hbound z hz w hw).2⟩

lemma quarterTangent_nonneg {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Icc (0 : ℝ) (quarterLength r)) :
    0 ≤ (quarterTangent r t).re ∧ 0 ≤ (quarterTangent r t).im := by
  have hθ : t / r ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact div_nonneg ht.1 hr.le
    · apply (div_le_iff₀ hr).mpr
      dsimp only [quarterLength] at ht
      linarith [ht.2]
  simp only [quarterTangent_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, mul_one, zero_add]
  exact ⟨Real.sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2.trans (by linarith [Real.pi_pos])⟩,
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩⟩

lemma lowConnectorTangent_nonneg {H r X : ℝ} (hr : 0 < r) (hX : 2 * r < X) (t : ℝ) :
    0 ≤ (lowConnectorTangent H r X t).re ∧ 0 ≤ (lowConnectorTangent H r X t).im := by
  obtain ⟨hc1, hc2, hc3⟩ := connector_cuts (H := H) hr hX
  by_cases h4 : t ≤ connectorFourth H r X
  · by_cases h3 : t ≤ connectorThird H r X
    · by_cases h2 : t ≤ connectorSecond H r
      · by_cases h1 : t ≤ H
        · simp only [lowConnectorTangent, curveJoin_of_le h4, curveJoin_of_le h3,
            curveJoin_of_le h2, curveJoin_of_le h1, Complex.I_re, Complex.I_im]
          norm_num
        · simp only [lowConnectorTangent, curveJoin_of_le h4, curveJoin_of_le h3,
            curveJoin_of_le h2, curveJoin_of_gt (lt_of_not_ge h1)]
          apply quarterTangent_nonneg hr
          constructor
          · linarith
          · dsimp only [connectorSecond] at h2
            linarith
      · simp only [lowConnectorTangent, curveJoin_of_le h4, curveJoin_of_le h3,
          curveJoin_of_gt (lt_of_not_ge h2), Complex.one_re, Complex.one_im]
        norm_num
    · simp only [lowConnectorTangent, curveJoin_of_le h4, curveJoin_of_gt (lt_of_not_ge h3),
        upperQuarterTangent]
      apply quarterTangent_nonneg hr
      constructor
      · dsimp only [connectorFourth] at h4
        linarith
      · linarith
  · simp only [lowConnectorTangent, curveJoin_of_gt (lt_of_not_ge h4), Complex.I_re, Complex.I_im]
    norm_num

lemma lowConnector_taxicab_speed {H r X : ℝ} (hr : 0 < r) (hX : 2 * r < X) (t : ℝ) :
    1 ≤ (lowConnectorTangent H r X t).re + (lowConnectorTangent H r X t).im := by
  obtain ⟨hre, him⟩ := lowConnectorTangent_nonneg (H := H) hr hX t
  have hn := lowConnectorTangent_norm H r X t
  have hs := Complex.sq_norm (lowConnectorTangent H r X t)
  rw [hn, Complex.normSq_apply] at hs
  have hab := mul_nonneg hre him
  nlinarith [sq_nonneg ((lowConnectorTangent H r X t).re +
    (lowConnectorTangent H r X t).im - 1)]

lemma lowConnector_chord_bound {H r X : ℝ} (hr : 0 < r) (hX : 2 * r < X) (s t : ℝ) :
    |s - t| ≤ 2 * ‖lowConnector H r X s - lowConnector H r X t‖ := by
  let F := fun u => (lowConnector H r X u).re + (lowConnector H r X u).im
  have hF (u : ℝ) : HasDerivAt F
      ((lowConnectorTangent H r X u).re + (lowConnectorTangent H r X u).im) u := by
    have hr' := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (lowConnector_hasDerivAt (H := H) hr hX u)
    have hi' := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u (lowConnector_hasDerivAt (H := H) hr hX u)
    exact hr'.add hi'
  have hslow (a b : ℝ) (hab : a ≤ b) : b - a ≤ 2 * ‖lowConnector H r X b - lowConnector H r X a‖ := by
    have hder : ∀ u ∈ interior (Icc a b), (1 : ℝ) ≤ deriv F u := by
      intro u _
      rw [(hF u).deriv]
      exact lowConnector_taxicab_speed (H := H) hr hX u
    have hh := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      (fun u _ => (hF u).continuousAt.continuousWithinAt)
      (fun u _ => (hF u).differentiableAt.differentiableWithinAt)
      hder a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
    have hre := Complex.abs_re_le_norm (lowConnector H r X b - lowConnector H r X a)
    have him := Complex.abs_im_le_norm (lowConnector H r X b - lowConnector H r X a)
    have hbnd : F b - F a ≤ 2 * ‖lowConnector H r X b - lowConnector H r X a‖ := by
      dsimp only [F]
      rw [Complex.sub_re] at hre
      rw [Complex.sub_im] at him
      have h1 := le_abs_self ((lowConnector H r X b).re - (lowConnector H r X a).re)
      have h2 := le_abs_self ((lowConnector H r X b).im - (lowConnector H r X a).im)
      linarith
    linarith
  by_cases hst : s ≤ t
  · rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub, norm_sub_rev]
    exact hslow s t hst
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hst))]
    exact hslow t s (le_of_not_ge hst)

/-- The normal ribbon around the whole low connector is embedded. -/
theorem lowConnector_normal_injective {H r X : ℝ} (hr : 50 ≤ r) (hX : 2 * r < X) :
    InjOn (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X))
      {z : ℂ | 0 ≤ z.re ∧ |z.im| ≤ 1} := by
  have hr0 : 0 < r := by linarith
  exact normalRibbon_injective_of_chord_bound _ _ (lowConnector_hasDerivAt hr0 hX)
    (lowConnectorTangent_norm H r X) (lowConnectorTangent_lipschitz hr hX)
    (fun s t _ _ => lowConnector_chord_bound hr0 hX s t)

end SLEExactGauge.Serpentine

end

end OAI
