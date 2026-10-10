import OAI.MeasureTheory.Falconer.Radial.RadialSphereLaw
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMass

namespace OAI

/-! # Positive affine changes of scale preserve original radial directions -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialZoom (a : ℝ) (ha : a ≠ 0) (c : Space d) : Space d ≃ₜ Space d where
  toFun x := a • (x-c)
  invFun y := c+a⁻¹ • y
  left_inv x := by simp only [smul_smul,inv_mul_cancel₀ ha,one_smul]; abel
  right_inv y := by simp only [add_sub_cancel_left,smul_smul,mul_inv_cancel₀ ha,one_smul]
  continuous_toFun := (continuous_id.sub continuous_const).const_smul a
  continuous_invFun := continuous_const.add (continuous_id.const_smul a⁻¹)

@[simp] theorem radialZoom_apply (a : ℝ) (ha : a ≠ 0) (c x : Space d) :
    radialZoom a ha c x = a • (x-c) := rfl

@[simp] theorem radialZoom_sub (a : ℝ) (ha : a ≠ 0) (c x y : Space d) :
    radialZoom a ha c x-radialZoom a ha c y = a • (x-y) := by
  simp only [radialZoom_apply,← smul_sub,sub_sub_sub_cancel_right]

theorem normalizeToSphere_smul_pos (w₀ : Sphere d) {a : ℝ} (ha : 0 < a) (x : Space d) :
    normalizeToSphere w₀ (a • x) = normalizeToSphere w₀ x := by
  by_cases hx : x = 0
  · simp [hx]
  · apply Subtype.ext
    rw [normalizeToSphere_coe_of_ne w₀ (smul_ne_zero ha.ne' hx),
      normalizeToSphere_coe_of_ne w₀ hx,normalize_smul_of_pos ha]

theorem radialZoom_direction (w₀ : Sphere d) {a : ℝ} (ha : 0 < a) (c x y : Space d) :
    normalizeToSphere w₀ (radialZoom a ha.ne' c x-radialZoom a ha.ne' c y) =
      normalizeToSphere w₀ (x-y) := by
  rw [radialZoom_sub,normalizeToSphere_smul_pos w₀ ha]

noncomputable def zoomPairSet (e : Space d ≃ₜ Space d)
    (G : Set (Space d × Space d)) : Set (Space d × Space d) :=
  {p | (e.symm p.1,e.symm p.2) ∈ G}

theorem zoomPairSet_measurable (e : Space d ≃ₜ Space d)
    {G : Set (Space d × Space d)} (hG : MeasurableSet G) : MeasurableSet (zoomPairSet e G) :=
  hG.preimage (e.symm.measurable.prodMap e.symm.measurable)

@[simp] theorem mem_zoomPairSet (e : Space d ≃ₜ Space d) (G : Set (Space d × Space d))
    (z x : Space d) : (e z,e x) ∈ zoomPairSet e G ↔ (z,x) ∈ G := by
  simp only [zoomPairSet,mem_ofPred_eq,e.symm_apply_apply]

theorem zoom_pair_mass (e : Space d ≃ₜ Space d) (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    ((Measure.map e μ).prod (Measure.map e ν)) (zoomPairSet e G) = (μ.prod ν) G := by
  rw [Measure.map_prod_map μ ν e.measurable e.measurable,
    Measure.map_apply (e.measurable.prodMap e.measurable) (zoomPairSet_measurable e hG)]
  congr 1
  ext p
  exact mem_zoomPairSet e G p.1 p.2

theorem radial_collision_zoom (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z x : Space d) (θ : ℝ) :
    radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ
      (radialZoom a ha.ne' c z,radialZoom a ha.ne' c x) = radialCollisionMass μ θ (z,x) := by
  let e := radialZoom a ha.ne' c
  unfold radialCollisionMass
  rw [Measure.map_apply e.measurable (by
    apply measurableSet_le _ measurable_const
    exact (measurable_normalized_vector (measurable_id.sub measurable_const)).dist measurable_const)]
  congr 1
  ext y
  dsimp only [e]
  simp only [mem_preimage,mem_ofPred_eq,radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
