import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.TrueCenterJet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TrueCenterJetBuild
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def trueCenterJetOfOriginal {u:M → ℝ} {a c y:M} {φ:ℝ → ℝ} {l:ℝ}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    (hl:0<l) (hl1:l<1)
    (hy:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hz:(reverseRay (⟨y,l • p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hφ:ContDiffAt ℝ 2 φ (cTransform u y)) (hφd:deriv φ (cTransform u y)=l)
    {s:Model n} {S:Model n →L[ℝ] Model n}
    (hS:∀d e,inner ℝ (S d) e=inner ℝ d (S e))
    (hSe:HasQuadraticExpansion (fun h=>φ (cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h)))) s S) :
    TrueCenterJet (n:=n) u a c φ l := by
  let z:=reverseRay (⟨y,l • p⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hrec:=graph_coordinate_reconstruction hz
  have hreg:z.2∈injectivityDomain z.1:=
    reverseRay_regular (contracted_minimizer_mem_injectivityDomain (injectivityDomain_subset_minimizingVectors _ hA.2.1) hl hl1)
  refine {
    y := y
    b := graphBaseCoordinate a z
    q := graphVelocityCoordinate a z
    chart := (extChartAt 𝓘(ℝ,Model n) a).map_source hz
    regular := ?_
    endpoint := ?_
    endChart := hy
    p := p
    A := A
    original := hA
    positive := hp
    pole := ?_
    smooth := hφ
    slope := hφd
    s := s
    S := S
    symmetric := hS
    expansion := hSe }
  · exact (congrArg (fun w:TangentBundle 𝓘(ℝ,Model n) M=>w.2∈injectivityDomain w.1) hrec).mpr hreg
  · rw [movingPrefix_graph_coordinates hz,one_smul]
    exact reverseRay_endpoint _
  · exact (reverseRay_base (⟨y,l • p⟩:TangentBundle 𝓘(ℝ,Model n) M)).symm.trans
      ((extChartAt 𝓘(ℝ,Model n) a).left_inv hz).symm
end TrueCenterJetBuild
end WeakMTWTransport

end
end

end OAI
