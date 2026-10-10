import OAI.Analysis.LienardCycles.PeriodicBasics

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile GlobalODE
lemma vectorField_local_flow {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (z : Plane) :
    ∃ f : Plane × ℝ → Plane, ContDiffAt ℝ ω f (z,0) ∧
      ∀ᶠ q in 𝓝 (z,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s=>f (q.1,s)) (vectorField F (f q)) q.2 := by
  let A : Plane →L[ℝ] Plane := (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-(ContinuousLinearMap.fst ℝ ℝ ℝ))
  let I : ℝ →L[ℝ] Plane := ContinuousLinearMap.inl ℝ ℝ ℝ
  let W : SmoothFlow.Path Plane → SmoothFlow.Path Plane := fun u=>SmoothFlow.pathMap A u-
    SmoothFlow.pathMap I ((AxisFlow.polynomial a).onPaths u)
  have hp := SmoothFlow.AlgebraicExpr.path_properties (AxisFlow.polynomial a) (AxisFlow.polynomial_regular a z)
  have hW : ContDiffAt ℝ ω W (SmoothFlow.constCLM z) :=
    (SmoothFlow.pathMap A).contDiff.contDiffAt.sub
      ((SmoothFlow.pathMap I).contDiff.contDiffAt.comp _ hp.2.1)
  apply SmoothFlow.exists_analytic_local_flow_eventually W (vectorField F) z _ hW
  filter_upwards [hp.2.2] with u hu s
  simp only [W,ContinuousMap.sub_apply,SmoothFlow.pathMap_apply,hu s,AxisFlow.polynomial_eval]
  simp [A,I,vectorField,hF]
lemma IsSolution.cutoff {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} (hz : IsSolution F z) {T : ℝ} (hT : 0<T) :
    ∃ (W : Plane → Plane) (K L : ℝ≥0) (hK : LipschitzWith K W) (hL : ∀ x, ‖W x‖≤L),
      (∀ t ∈ Icc (-1) (T+1), GlobalODE.flow W hK hL (z 0) t=z t) ∧
      (∀ t ∈ Icc (-1) (T+1), ContDiffAt ℝ ω (fun q : Plane × ℝ=>GlobalODE.flow W hK hL q.1 q.2) (z 0,t)) ∧
      ∀ t ∈ Icc (-1) (T+1), ∀ᶠ q : Plane × ℝ in 𝓝 (z 0,t),
        W (GlobalODE.flow W hK hL q.1 q.2)=vectorField F (GlobalODE.flow W hK hL q.1 q.2) := by
  simpa using GlobalODE.analytic_cutoff_along_compact_solution (vectorField F) isOpen_univ
    ((vectorField_contDiff F).of_le (by simp)).contDiffOn
    (fun x _=>vectorField_local_flow hF x) (a:=-1) (b:=T+1) (c:=0)
    (by norm_num) (by linarith) hz.continuous (fun _ _=>mem_univ _) (fun t _=>hz t)
end QuinticLienard

end OAI
