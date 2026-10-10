import OAI.MeasureTheory.Falconer.Incidence.RadialZoomFiniteBalls

namespace OAI

/-! # Geometric data for middle-interval pruning after cell normalization -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_quarter_bound {a : ℝ} (ha : 0 < a) (c z : Space d)
    (hz : ‖z-c‖ ≤ 1/(4*a)) : ‖radialZoom a ha.ne' c z‖ ≤ 1/4 := by
  rw [radialZoom_norm ha]
  calc
    _ ≤ a*(1/(4*a)) := mul_le_mul_of_nonneg_left hz ha.le
    _ = _ := by field_simp

theorem radialZoom_pin_distance {a r : ℝ} (ha : 0 < a) (c x : Space d)
    (hx : r ≤ ‖c-x‖) : a*r ≤ ‖(0:Space d)-radialZoom a ha.ne' c x‖ := by
  rw [zero_sub,norm_neg,radialZoom_norm ha,norm_sub_rev x c]
  exact mul_le_mul_of_nonneg_left hx ha.le

theorem radialZoom_pair_ae_bound (μ : Measure (Space d)) {a H : ℝ}
    (ha : 0 < a) (c x : Space d) (h : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) :
    ∀ᵐ y ∂Measure.map (radialZoom a ha.ne' c) μ,
      ‖y-radialZoom a ha.ne' c x‖ ≤ a*H := by
  rw [radialZoom_ae_iff μ ha]
  filter_upwards [h] with y hy
  rw [norm_radialZoom_sub ha]
  exact mul_le_mul_of_nonneg_left hy ha.le

theorem radialZoom_reverse_slab (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        |inner ℝ u (normalize (x-radialZoom a ha.ne' c z))| ≤ r} =
      ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} := by
  let e := radialZoom a ha.ne' c
  have hi : Measurable (fun x : Space d => inner ℝ u (normalize (x-e z))) :=
    measurable_const.inner (measurable_normalized_vector (measurable_id.sub measurable_const))
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      |inner ℝ u (normalize (x-e z))| ≤ r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_le hi.abs measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
