import OAI.Geometry.Perimeter.Regularity.NonlinearSmooth
import OAI.Geometry.Perimeter.Regularity.MinimalFlux
import OAI.Geometry.Perimeter.Regularity.NormalAdjustment
import OAI.Geometry.Perimeter.Regularity.GraphGeoCoordinates

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem normal_graph_smooth_threshold (hn : 1<n) {v : Euc n} (hv : ‖v‖=1)
    {η : ℝ} (hη : 0<η) : ∃ ε : ℝ, 0<ε ∧
    ∀ f : normalPlane v → ℝ,
    ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)) →
    (∀ x∈Metric.ball (0:normalPlane v) (1/4), GeometricHolderAt η (fderiv ℝ f) x) →
    (∀ x∈Metric.ball (0:normalPlane v) (1/4), ‖fderiv ℝ f x‖<ε) →
    (∀ ψ : normalPlane v → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 (1/4) →
      (∫ y, inner ℝ (gradient f y) (gradient ψ y)/Real.sqrt (1+‖gradient f y‖^2))=0) →
    ContDiffOn ℝ ∞ f (Metric.ball 0 (1/4)) := by
  obtain ⟨θ,δ,K,hθ,hθb,hδ,hK,hc⟩ := exists_linear_contraction (by omega : 0<n-1) hη
  obtain ⟨ε,hε,hsmall⟩ := minimalFlux_exists_small (n:=n-1) hδ
  refine ⟨ε,hε,fun f hf hh hs heq ↦ ?_⟩
  let e := normalPlaneEuclideanChart hv
  let U : Set (normalPlane v) := Metric.ball 0 (1/4)
  let V := e ⁻¹' U
  have hU : IsOpen U := Metric.isOpen_ball
  have hV : IsOpen V := hU.preimage e.continuous
  have hgeo := geoC_one_isometry hθ.le (hθb.trans_le (min_le_right _ _)).le
    (hθb.trans_le (min_le_left _ _)).le e hU hf hh
  have hweak : WeakFluxEquation (fun x ↦ minimalFlux (gradient (f ∘ e) x)) V := by
    intro φ
    have hz := minimal_equation_isometry e heq φ
    change (∫ x, inner ℝ (minimalFlux (gradient (f ∘ e) x)) (gradient φ.val x))=0
    convert hz using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [minimalFlux,real_inner_smul_left,div_eq_mul_inv,mul_comm]
  have hnear : ∀ x∈V, ‖ContinuousLinearMap.id ℝ (Euc (n-1))-
      fderiv ℝ minimalFlux (gradient (f ∘ e) x)‖ < min δ (1/2) := by
    intro x hx
    apply hsmall
    rw [gradient_comp_isometry,e.symm.norm_map]
    have hnorm : ‖gradient f (e x)‖=‖fderiv ℝ f (e x)‖ :=
      (InnerProductSpace.toDual ℝ (normalPlane v)).symm.norm_map _
    rw [hnorm]
    exact hs (e x) hx
  have hsm := nonlinear_smooth hθ (hθb.trans_le (min_le_right _ _)).le hK hc
    minimalFlux_smooth hV hgeo hweak hnear
  have him : MapsTo e.symm U V := by
    intro x hx
    change e (e.symm x)∈U
    simpa only [e.apply_symm_apply] using hx
  have hout := hsm.comp e.symm.contDiff.contDiffOn him
  simpa only [Function.comp_def,e.apply_symm_apply] using hout

end RPISingularHarnack

end

end OAI
