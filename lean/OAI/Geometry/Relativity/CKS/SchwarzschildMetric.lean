import OAI.Geometry.Relativity.CKS.SchwarzschildMetricDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildCharts

namespace OAI

noncomputable section
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] CKSSpatialManifold.real_id_isometric
local instance : IsBoundedSMul ℝ SpatialBilinear :=
  @NormedSpace.toIsBoundedSMul ℝ SpatialBilinear _ _ _
local instance : TopologicalSpace (TotalSpace (E3 →L[ℝ] ℝ)
    (fun x : Exterior => TangentSpace I3 x →L[ℝ] ℝ)) := inferInstance

lemma radialUnit_smoothAt {x : E3} (hx : x ≠ 0) : ContDiffAt ℝ ∞ radialUnit x := by
  exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
lemma radialForm_smoothAt {x : E3} (hx : x ≠ 0) : ContDiffAt ℝ ∞ radialForm x := by
  have h := (innerSL ℝ).contDiff.contDiffAt.comp x (radialUnit_smoothAt hx)
  convert h.smulRight h using 1
  ext y v w
  rfl
lemma cartMetric_smoothAt {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    ContDiffAt ℝ ∞ (cartMetric m) x := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  have hx : x ≠ 0 := norm_pos_iff.mp hn
  exact contDiffAt_const.add (((lapseSquared_smoothAt hn).comp x
    (contDiffAt_norm ℝ hx)).inv (ne_of_gt (lapseSquared_pos hm hr)) |>.sub contDiffAt_const |>.smul
      (radialForm_smoothAt hx))
lemma velocity_deriv_smooth (m : ℝ) : ContDiff ℝ ∞ (deriv (velocity m)) := by
  exact ((contDiff_infty_iff_deriv).mp (velocity_smooth m)).2
lemma cartTensor_smoothAt {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    ContDiffAt ℝ ∞ (cartTensor m) x := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  have hx : x ≠ 0 := norm_pos_iff.mp hn
  have hnorm := contDiffAt_norm ℝ hx (n := ∞)
  have hv := ((velocity_smooth m).contDiffAt.comp x hnorm).div hnorm (ne_of_gt hn)
  have hd := ((velocity_deriv_smooth m).contDiffAt.comp x hnorm).div
    ((lapseSquared_smoothAt hn).comp x hnorm) (ne_of_gt (lapseSquared_pos hm hr))
  exact (hv.smul contDiffAt_const).add ((hd.sub hv).smul (radialForm_smoothAt hx))

lemma euclideanForm_apply (v w : E3) : euclideanForm v w = ⟪v,w⟫_ℝ := rfl
lemma radialForm_apply (x v w : E3) :
    radialForm x v w = ⟪radialUnit x,v⟫_ℝ * ⟪radialUnit x,w⟫_ℝ := rfl
lemma cartMetric_apply (m : ℝ) (x v w : E3) :
    cartMetric m x v w = ⟪v,w⟫_ℝ + ((lapseSquared m ‖x‖)⁻¹-1) *
      (⟪radialUnit x,v⟫_ℝ * ⟪radialUnit x,w⟫_ℝ) := rfl
lemma cartMetric_symm (m : ℝ) (x v w : E3) : cartMetric m x v w = cartMetric m x w v := by
  rw [cartMetric_apply,cartMetric_apply,real_inner_comm v w,mul_comm (⟪radialUnit x,v⟫_ℝ)]
lemma cartTensor_symm (m : ℝ) (x v w : E3) : cartTensor m x v w = cartTensor m x w v := by
  change velocity m ‖x‖ / ‖x‖ * ⟪v,w⟫_ℝ +
      (deriv (velocity m) ‖x‖ / lapseSquared m ‖x‖ - velocity m ‖x‖ / ‖x‖) *
      (⟪radialUnit x,v⟫_ℝ * ⟪radialUnit x,w⟫_ℝ) = _
  simp only [cartTensor,add_apply,smul_apply,
    smul_eq_mul,euclideanForm_apply,radialForm_apply,real_inner_comm v w,
    mul_comm (⟪radialUnit x,v⟫_ℝ)]
lemma norm_radialUnit {x : E3} (hx : x ≠ 0) : ‖radialUnit x‖ = 1 := by
  rw [radialUnit,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
lemma cartMetric_pos {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖)
    (v : E3) (hv : v ≠ 0) : 0 < cartMetric m x v v := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  have hbound := real_inner_mul_inner_self_le (radialUnit x) v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,norm_radialUnit (norm_pos_iff.mp hn)] at hbound
  have hnorm : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hl : 0 < (lapseSquared m ‖x‖)⁻¹ := inv_pos.mpr (lapseSquared_pos hm hr)
  rw [cartMetric_apply,real_inner_self_eq_norm_sq]
  by_cases hh : ⟪radialUnit x,v⟫_ℝ = 0
  · simp [hh,hnorm]
  · have hp : 0 < (lapseSquared m ‖x‖)⁻¹ * (⟪radialUnit x,v⟫_ℝ)^2 :=
      mul_pos hl (sq_pos_of_ne_zero hh)
    nlinarith

lemma metricInner_smooth {m : ℝ} (hm : 0 < m) :
    ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 (metricInner m)) := by
  intro p
  apply endInner_smoothAt (position_smooth m p)
  apply cartMetric_smoothAt hm
  rw [norm_position hm]
  exact radius_ge m p
lemma tensorInner_smooth {m : ℝ} (hm : 0 < m) :
    ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 (tensorInner m)) := by
  intro p
  apply endInner_smoothAt (position_smooth m p)
  apply cartTensor_smoothAt hm
  rw [norm_position hm]
  exact radius_ge m p
lemma metricInner_symm (m : ℝ) (p : Exterior) (v w : TangentSpace I3 p) :
    metricInner m p v w = metricInner m p w v := by
  exact cartMetric_symm m _ _ _
lemma tensorInner_symm (m : ℝ) (p : Exterior) (v w : TangentSpace I3 p) :
    tensorInner m p v w = tensorInner m p w v := by
  exact cartTensor_symm m _ _ _
lemma metricInner_pos {m : ℝ} (hm : 0 < m) (p : Exterior) (v : TangentSpace I3 p) (hv : v ≠ 0) :
    0 < metricInner m p v v := by
  change 0 < cartMetric m (position m p) (ambientDerivative (position m) p v)
    (ambientDerivative (position m) p v)
  apply cartMetric_pos hm
  · rw [norm_position hm]; exact radius_ge m p
  · intro h
    apply hv
    exact (position_derivative_injective hm p) (h.trans (map_zero _).symm)

def smoothMetric {m : ℝ} (hm : 0 < m) : SmoothMetric I3 (M := Exterior) where
  inner := metricInner m
  symm := metricInner_symm m
  pos := metricInner_pos hm
  isVonNBounded p := positive_bilinear_bounded (metricInner m p) (metricInner_pos hm p)
  contMDiff := metricInner_smooth hm

theorem exists_schwarzschild_smooth_data {m : ℝ} (hm : 0 < m) :
    (∃ g : SmoothMetric I3 (M := Exterior), g.inner = metricInner m) ∧
    ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 (tensorInner m)) ∧
    ∀ p v w, tensorInner m p v w = tensorInner m p w v := by
  exact ⟨⟨smoothMetric hm,rfl⟩,tensorInner_smooth hm,tensorInner_symm m⟩

end CKSSchwarzschild

end

end OAI
