import Mathlib
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.TwistedCurveTensor
import OAI.Geometry.SplitTangent.PositiveCoverLift
import OAI.Geometry.SplitTangent.OpenPositiveLeaves

namespace OAI

/-! R C Covariant Vanishing. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent

 

structure HolomorphicTangentTensor (X : ComplexManifold.{u}) (m : ℕ) where
  value : X.Carrier → TangentTensor X m
  holomorphic : ∀x,ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,TangentTensor X m) ω
    (fun y => (value y).compContinuousLinearMap (fun _ =>
      (trivializationAt (Model X) (Tangent X) x).symmL ℂ y))
    (trivializationAt (Model X) (Tangent X) x).baseSet

namespace HolomorphicTangentTensor
variable {X : ComplexManifold.{u}} {m : ℕ} (A : HolomorphicTangentTensor X m)

def coordinates (x y : X.Carrier) : TangentTensor X m :=
  (A.value y).compContinuousLinearMap (fun _ =>
    (trivializationAt (Model X) (Tangent X) x).symmL ℂ y)

lemma coordinates_zero_iff {x y : X.Carrier}
    (hy : y∈(trivializationAt (Model X) (Tangent X) x).baseSet) :
    A.coordinates x y=0 ↔ A.value y=0 := by
  let t := trivializationAt (Model X) (Tangent X) x
  constructor
  · intro h
    apply ContinuousMultilinearMap.ext
    intro v
    have h' := congrArg (fun B : TangentTensor X m =>
      B (fun i => t.continuousLinearMapAt ℂ y (v i))) h
    change A.value y (fun i => t.symmL ℂ y (t.continuousLinearMapAt ℂ y (v i)))=0 at h'
    have he : (fun i => t.symmL ℂ y (t.continuousLinearMapAt ℂ y (v i))) = v := by
      funext i
      exact t.symmL_continuousLinearMapAt hy (v i)
    rw [he] at h'
    exact h'
  · intro h
    apply ContinuousMultilinearMap.ext
    intro v
    simp [coordinates,h]
    rfl

def along (g : RationalCurve X) : TwistedCurveTensor g 0 m where
  finite := A.value ∘ g.finite
  infinity := A.value ∘ g.infinity
  finite_holomorphic z := by
    exact (((A.holomorphic (g.finite z)).contMDiffAt
      ((trivializationAt (Model X) (Tangent X) (g.finite z)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' _))).comp z
      (g.finite_holomorphic z)).contDiffAt.analyticAt
  infinity_holomorphic z := by
    exact (((A.holomorphic (g.infinity z)).contMDiffAt
      ((trivializationAt (Model X) (Tangent X) (g.infinity z)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' _))).comp z
      (g.infinity_holomorphic z)).contDiffAt.analyticAt
  overlap z hz := by simp [g.overlap z hz]

lemma zero_on_positive_curve (hm : 0 < m) (g : RationalCurve X)
    (hg : PointedGenerated g (fun _ => ⊤)) : A.value (g.finite 1)=0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  exact (A.along g).vanish_on_generated_fiber hg hm v (fun _ => Submodule.mem_top)

lemma local_analytic_zero_locus (x : X.Carrier) :
    ∃e : OpenPartialHomeomorph X.Carrier (Model X),x∈e.source ∧
      ∃f : Model X → TangentTensor X m,AnalyticOnNhd ℂ f e.target ∧
        ∀y∈e.source,A.value y=0 ↔ f (e y)=0 := by
  let t := trivializationAt (Model X) (Tangent X) x
  let c := chartAt (Model X) x
  let e := c.restr t.baseSet
  have hsrc : e.source=c.source ∩ t.baseSet := c.restr_source' _ t.open_baseSet
  have htarg : e.target=c.target ∩ c.symm ⁻¹' t.baseSet := by
    rw [OpenPartialHomeomorph.restr_target,t.open_baseSet.interior_eq]
  refine ⟨e,?_,fun z => A.coordinates x (c.symm z),?_,?_⟩
  · rw [hsrc]
    exact ⟨mem_chart_source (Model X) x,FiberBundle.mem_baseSet_trivializationAt' _⟩
  · intro z hz
    rw [htarg] at hz
    have hc : ContMDiffAt 𝓘(ℂ,Model X) (ModelWithCorners X) ω c.symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) x) hz.1
    exact (((A.holomorphic x).contMDiffAt (t.open_baseSet.mem_nhds hz.2)).comp z hc).contDiffAt.analyticAt
  · intro y hy
    rw [hsrc] at hy
    change A.value y=0 ↔ A.coordinates x (c.symm (c y))=0
    rw [c.left_inv hy.1]
    exact (A.coordinates_zero_iff hy.2).symm

lemma eq_zero_of_nonempty_open [PreconnectedSpace X.Carrier]
    {U : Set X.Carrier} (hU : IsOpen U) (hne : U.Nonempty)
    (hzero : ∀x∈U,A.value x=0) : ∀x,A.value x=0 := by
  have hZ : {x | A.value x=0}=univ :=
    AnalyticContinuation.eq_univ_of_local_analytic_zero_locus
      A.local_analytic_zero_locus (by
        obtain ⟨x,hx⟩ := hne
        exact ⟨x,mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (hU.mem_nhds hx) hzero)⟩)
  intro x
  have := Set.mem_univ x
  rwa [←hZ] at this

end HolomorphicTangentTensor

namespace RationallyConnected
variable {X : ComplexManifold.{u}} [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
include e hRC

 

theorem exists_open_positive_tangent_curves (hdim : 0<X.dim) :
    ∃U : Set X.Carrier,IsOpen U ∧ U.Nonempty ∧
      ∀x∈U,∃g : RationalCurve X,g.finite 1=x ∧ PointedGenerated g (fun _ => ⊤) := by
  obtain ⟨T,hT,G,hs⟩ := hRC.exists_submersive_family e hdim
  let := hT
  refine ⟨Set.range (G.evaluation 1),(G.evaluation_open hs).isOpen_range,
    Set.range_nonempty _,?_⟩
  rintro x ⟨τ,rfl⟩
  refine ⟨G.curve τ,rfl,?_⟩
  intro v hv
  obtain ⟨σ,h0,h1⟩ := G.exists_section_endpoints (hs τ) 0 v
  exact ⟨σ,fun _ => Submodule.mem_top,fun _ => Submodule.mem_top,h0,h1⟩

 

theorem holomorphic_tensor_zero [PreconnectedSpace X.Carrier] (hdim : 0<X.dim)
    {m : ℕ} (hm : 0 < m) (A : HolomorphicTangentTensor X m) :
    ∀x,A.value x=0 := by
  obtain ⟨U,hU,hUn,hpos⟩ := hRC.exists_open_positive_tangent_curves e hdim
  apply A.eq_zero_of_nonempty_open hU hUn
  intro x hx
  obtain ⟨g,hg0,hg⟩ := hpos x hx
  rw [←hg0]
  exact A.zero_on_positive_curve hm g hg

 

theorem holomorphic_cover_tensor_zero [ConnectedSpace X.Carrier]
    {Y : ComplexManifold.{u}} [CompactSpace Y.Carrier] [ConnectedSpace Y.Carrier]
    {p : Y.Carrier → X.Carrier} (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (hdim : 0<X.dim) {m : ℕ} (hm : 0 < m) (A : HolomorphicTangentTensor Y m) :
    ∀y,A.value y=0 := by
  have hs : Function.Surjective p := by
    have hc : IsClopen (Set.range p) :=
      ⟨isCompact_range hcover.continuous |>.isClosed,hcover.isOpenMap.isOpen_range⟩
    exact Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))
  obtain ⟨U,hU,hUn,hpos⟩ := hRC.exists_open_positive_tangent_curves e hdim
  apply A.eq_zero_of_nonempty_open (hU.preimage hcover.continuous)
    (hUn.preimage hs)
  intro y hy
  obtain ⟨g,hg1,hg⟩ := hpos (p y) hy
  obtain ⟨k,hk1,hk,_,_⟩ := g.exists_positive_cover_lift_at hg hcover hp 1 y hg1.symm
  rw [←hk1]
  exact A.zero_on_positive_curve hm k hk

end RationallyConnected
end SplitTangent

end

end OAI
