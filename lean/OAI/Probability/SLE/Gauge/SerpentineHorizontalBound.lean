import OAI.Probability.SLE.Gauge.SerpentineExperimentGeometry

namespace OAI

/-! The whole completed physical ribbon stays between the exterior
vertical lines x=-2 and x=2. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma array_normal_re_upper {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : 0 ≤ z.re ∧ |z.im| ≤ 1) :
    (normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) z).re ≤ 400 * m := by
  have hh : (0 : ℝ) < 100 * m := by positivity
  by_cases he : z.re ≤ arrayEnd m (2 * m)
  · rcases array_pieces m (2 * m) ⟨hz.1, he⟩ with ⟨i, hi, u, hu, _, hs, hT⟩ |
      ⟨i, hi, u, hu, _, hs, hT⟩
    · simp only [normalRibbon]
      rw [hs, hT, normal_straight_eq hm]
      have hb := columnPoint_bound hh hm hi 0 (straight_height_bound m i hu) hz.2
      rw [dist_zero_right] at hb
      have hi := Complex.re_le_norm (columnPoint 0 (100 * m) m i (side i * (-100 * m + u)) z.im)
      linarith
    · simp only [normalRibbon]
      rw [hs, hT, normal_circular_eq hm]
      have hb := turnPoint_bound hh hm (show i + 1 ≤ 2 * m by omega) 0 (u / 50) hz.2
      rw [dist_zero_right] at hb
      exact (Complex.re_le_norm _).trans (by linarith)
  · have hE : columnEntry 0 m (2 * m) ≤ z.re := by
      have h := lt_of_not_ge he
      dsimp only [arrayEnd] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have ht := array_normal_terminal hm (a := z.im) hE
    rw [Complex.re_add_im z] at ht
    rw [ht, columnPoint_re]
    simp only [columnOffset, normalized_spacing hm, normalized_width hm, side_even,
      one_mul, Complex.zero_re, zero_add, Nat.cast_mul, Nat.cast_ofNat]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [(abs_le.mp hz.2).1]

lemma lowConnector_re_bounds {H r X : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (hX : 2 * r < X)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (lowConnector H r X t).re ∧ (lowConnector H r X t).re ≤ X := by
  have hmono : Monotone (fun t => (lowConnector H r X t).re) :=
    monotone_of_hasDerivAt_nonneg
      (fun t => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (lowConnector_hasDerivAt hr hX t))
      (fun t => (lowConnectorTangent_nonneg (H := H) hr hX t).1)
  have hzero := hmono ht
  dsimp only at hzero
  rw [(lowConnector_initial hr hX hH).1] at hzero
  simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re] at hzero
  let u := max t (connectorFourth H r X + 1)
  have hu : connectorFourth H r X < u := by
    have h := le_max_right t (connectorFourth H r X + 1)
    dsimp only [u]
    linarith
  have hup := hmono (le_max_left t (connectorFourth H r X + 1))
  dsimp only at hup
  rw [(lowConnector_after hu).1] at hup
  have hup' : (lowConnector H r X t).re ≤ X := by
    simpa only [connectorTail, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hup
  exact ⟨hzero, hup'⟩

lemma lowConnector_normal_re_bounds {H r X : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (hX : 2 * r < X)
    {z : ℂ} (hz : 0 ≤ z.re ∧ |z.im| ≤ 1) :
    -1 ≤ (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z).re ∧
      (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z).re ≤ X + 1 := by
  have hcenter := lowConnector_re_bounds hH hr hX hz.1
  have hdist : ‖normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z -
      lowConnector H r X z.re‖ ≤ 1 := by
    simp only [normalRibbon, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, lowConnectorTangent_norm, mul_one]
    exact hz.2
  have hab := (Complex.abs_re_le_norm _).trans hdist
  rw [Complex.sub_re, abs_le] at hab
  constructor <;> linarith

end SLEExactGauge.Serpentine

end

end OAI
