import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ChartCenterGain

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TrueCenterJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance trueCenterJetFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

structure TrueCenterJet (u:M → ℝ) (a c:M) (φ:ℝ → ℝ) (l:ℝ) where
  y : M
  b : Model n
  q : Model n
  chart : b∈(extChartAt 𝓘(ℝ,Model n) a).target
  regular : chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  endpoint : movingPrefix a 1 b q=y
  endChart : y∈(extChartAt 𝓘(ℝ,Model n) c).source
  p : TangentSpace 𝓘(ℝ,Model n) y
  A : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y
  original : NormalAlexandrovContact (n:=n) u y p A
  positive : ∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d
  pole : riemannianExp y (l • p)=(extChartAt 𝓘(ℝ,Model n) a).symm b
  smooth : ContDiffAt ℝ 2 φ (cTransform u y)
  slope : deriv φ (cTransform u y)=l
  s : Model n
  S : Model n →L[ℝ] Model n
  symmetric : ∀d e,inner ℝ (S d) e=inner ℝ d (S e)
  expansion : HasQuadraticExpansion (fun h=>φ (cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h)))) s S

def TrueCenterJet.fullRay {u:M → ℝ} {a c:M} {φ:ℝ → ℝ} {l:ℝ}
    (J:TrueCenterJet (n:=n) u a c φ l) : TangentBundle 𝓘(ℝ,Model n) M:=⟨J.y,J.p⟩
def TrueCenterJet.shortRay {u:M → ℝ} {a c:M} {φ:ℝ → ℝ} {l:ℝ}
    (J:TrueCenterJet (n:=n) u a c φ l) : TangentBundle 𝓘(ℝ,Model n) M:=
  ⟨(extChartAt 𝓘(ℝ,Model n) a).symm J.b,chartFiberInverse a J.b J.q⟩
def TrueCenterJet.matrix {u:M → ℝ} {a c:M} {φ:ℝ → ℝ} {l:ℝ}
    (J:TrueCenterJet (n:=n) u a c φ l) : Model n →L[ℝ] Model n →L[ℝ] ℝ:=
  chartJetMatrix a c J.b J.q (innerSL ℝ J.s) ((innerSL ℝ).comp J.S)
def TrueCenterJet.curvature {u:M → ℝ} {a c:M} {φ:ℝ → ℝ} {l:ℝ}
    (J:TrueCenterJet (n:=n) u a c φ l) : ℝ:=iteratedDeriv 2 φ (cTransform u J.y)

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_true_center_jet_gain : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀l∈U,0<l → l<1 → ∀(u:M → ℝ) (a c:M) (φ:ℝ → ℝ),
    ∀J:TrueCenterJet (n:=n) u a c φ l,
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (bilinearOperator V).det=(chartFiberInverse a J.b).toLinearMap.normDet^2*l^n*
        (expJacobian J.shortRay.1 J.shortRay.2)^2*(normalHessianOperator J.y J.p+J.A).det ∧
      ∀d,V d d+δ*(1-l)*frameMetric a J.b d d+
        (J.curvature/l^2)*(frameMetric a J.b J.q d)^2≤J.matrix d d := by
  obtain ⟨δ,hδ,Hδ⟩:=exists_chart_true_center_gain (n:=n) (M:=M)
  obtain ⟨U,hU,hUo,h1⟩:=mem_nhds_iff.mp Hδ
  refine ⟨δ,hδ,U,hUo,h1,?_⟩
  intro l hl hl0 hl1 u a c φ J
  exact hU hl hl1 hl0 u a c J.y J.b J.q J.chart J.regular J.endpoint
    J.endChart J.p J.A J.original J.positive J.pole φ J.smooth J.slope J.s J.S
    J.symmetric J.expansion

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma TrueCenterJet.det_pos {u:M → ℝ} {a c:M} {φ:ℝ → ℝ} {l:ℝ}
    (J:TrueCenterJet (n:=n) u a c φ l) : 0<(normalHessianOperator J.y J.p+J.A).det :=
  symmetric_det_pos (normal_contact_matrix_symmetric J.original) J.positive

end TrueCenterJet
end WeakMTWTransport

end
end

end OAI
