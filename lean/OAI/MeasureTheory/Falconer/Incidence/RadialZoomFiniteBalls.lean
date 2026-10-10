import OAI.MeasureTheory.Falconer.Radial.RadialZoomBounds

namespace OAI

/-! # Finite-scale conditional balls and reverse caps after a fixed contraction -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_ae_iff (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c : Space d) (P : Space d → Prop) :
    (∀ᵐ x ∂Measure.map (radialZoom a ha.ne' c) μ, P x) ↔
      ∀ᵐ x ∂μ, P (radialZoom a ha.ne' c x) := by
  have h := MeasurableEquiv.map_ae (radialZoom a ha.ne' c).toMeasurableEquiv μ
  change Filter.map (radialZoom a ha.ne' c) (ae μ) =
    ae (Measure.map (radialZoom a ha.ne' c) μ) at h
  rw [← h]
  rfl

theorem radialZoom_scaled_ball_bound (μ : Measure (Space d))
    {a δ K L s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 1 ≤ K)
    (hL : 0 < L) (hs : 0 ≤ s) (hmass : μ univ ≤ 1) (c : Space d)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1/L →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K*(L*r)^s)) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → δ ≤ r →
      Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) ≤
        ENNReal.ofReal (K*a^(-s)*(L*r)^s) := by
  intro x r hr hδ
  rw [radialZoom_ball_apply μ ha]
  have hrra : r ≤ r/a := (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hr.le ha1)
  have he : K*(L*(r/a))^s = K*a^(-s)*(L*r)^s := by
    rw [show L*(r/a) = (L*r)/a by ring,
      Real.div_rpow (mul_pos hL hr).le ha.le,div_eq_mul_inv,← Real.rpow_neg ha.le]
    ring
  rw [← he]
  by_cases hsmall : r/a ≤ 1/L
  · exact hball _ _ (hδ.trans hrra) hsmall
  · have hscale : 1 ≤ L*(r/a) := by
      have hh := (lt_of_not_ge hsmall)
      have hh' := (div_lt_iff₀ hL).mp hh
      nlinarith
    have hp := Real.one_le_rpow hscale hs
    have hcoeff : 1 ≤ K*(L*(r/a))^s := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hcoeff)

theorem norm_radialZoom_sub {a : ℝ} (ha : 0 < a) (c x y : Space d) :
    ‖radialZoom a ha.ne' c x-radialZoom a ha.ne' c y‖ = a*‖x-y‖ := by
  rw [radialZoom_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem radialZoom_reverse_cap (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        dist (normalize (x-radialZoom a ha.ne' c z)) u < r} =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} := by
  let e := radialZoom a ha.ne' c
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      dist (normalize (x-e z)) u < r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_lt ((measurable_normalized_vector
        (measurable_id.sub measurable_const)).dist measurable_const) measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
