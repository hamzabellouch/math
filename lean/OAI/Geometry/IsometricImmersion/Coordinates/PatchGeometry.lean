import OAI.Geometry.IsometricImmersion.Metrics.MetricLocality
import OAI.Geometry.IsometricImmersion.Metrics.ModelProfile

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Model

def patchBox : Set Coord :=
  Icc (fun _ => (-(1 / 10 : ℝ))) (fun _ => (1 / 10 : ℝ))

def centralBox : Set Coord :=
  Icc (fun _ => (-(1 / 5 : ℝ))) (fun _ => (1 / 5 : ℝ))

theorem patchBox_subset_centralBox : patchBox ⊆ centralBox := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

theorem gaussianCurvature_eventuallyEq_of_metric_eventuallyEq
    {g h : MetricField} {p : Coord} (heq : g =ᶠ[𝓝 p] h) :
    gaussianCurvature g =ᶠ[𝓝 p] gaussianCurvature h := by
  filter_upwards [heq.eventuallyEq_nhds] with q hq
  exact gaussianCurvature_eq_of_eventuallyEq hq

theorem patch_smallCurvature_eventually_model
    {g0 eta : MetricField} {kappa : ℝ} {U : Set Coord}
    (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    {p : Coord} (hp : p ∈ U)
    (hsmall : |gaussianCurvature (g0 + eta) p| ≤ kappa / 8) :
    gaussianCurvature (g0 + eta) =ᶠ[𝓝 p] modelCurvature kappa := by
  have hout : p ∉ patchBox := by
    intro hin
    have hneg := hcentral p (patchBox_subset_centralBox hin)
    have hlo := (abs_le.mp hsmall).1
    linarith
  have hts : p ∉ tsupport eta := fun hin => hout (hsupport hin)
  have hsame := gaussianCurvature_eventuallyEq_of_metric_eventuallyEq
    (metric_add_eventuallyEq_of_not_mem_tsupport g0 eta hts)
  have hmodel : gaussianCurvature g0 =ᶠ[𝓝 p] modelCurvature kappa := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hbackground q hq
  exact hsame.trans hmodel

theorem patch_smallCurvature_model_firstJet
    {g0 eta : MetricField} {kappa : ℝ} {U : Set Coord}
    (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    {p : Coord} (hp : p ∈ U)
    (hsmall : |gaussianCurvature (g0 + eta) p| ≤ kappa / 8) :
    gaussianCurvature (g0 + eta) p = modelCurvature kappa p ∧
      ∀ i : Fin 2, coordPartial i (gaussianCurvature (g0 + eta)) p =
        coordPartial i (modelCurvature kappa) p := by
  have heq := patch_smallCurvature_eventually_model hk hU hbackground hsupport hcentral hp hsmall
  exact ⟨heq.self_of_nhds, fun i => coordPartial_eq_of_eventuallyEq heq i⟩

end SmoothLocal.Geometry

end

end OAI
