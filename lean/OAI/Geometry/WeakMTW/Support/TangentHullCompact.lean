import Mathlib
import OAI.Geometry.WeakMTW.Support.FiniteActiveGraph
import OAI.Geometry.WeakMTW.Support.FiberHullCompact

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ConvexRepresentation
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def tangentHull (K : Set (TangentBundle (model n) M)) : Set (TangentBundle (model n) M) :=
    {p | p.2 ∈ convexHull ℝ {a | (⟨p.1,a⟩ : TangentBundle (model n) M) ∈ K}}

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentHull_chart (x : M) (K : Set (TangentBundle (model n) M))
    {X : Set M} (hX : X ⊆ (chartAt (Model n) x).source)
    {p : TangentBundle (model n) M} (hp : p.1 ∈ X) :
    stateChart x p ∈ fiberHull (stateChart x '' (K ∩ {q | q.1 ∈ X})) ↔ p ∈ tangentHull K := by
  cases p with | mk b v =>
    let c := chartAt (Model n) x
    let e := trivializationAt (Model n) (TangentSpace (model n)) x
    have hb : b ∈ e.baseSet := by
      simpa only [e,TangentBundle.trivializationAt_baseSet] using hX hp
    let L := e.continuousLinearEquivAt ℝ b hb
    let A : Set (TangentSpace (model n) b) := {a | (⟨b,a⟩ : TangentBundle (model n) M) ∈ K}
    have heq : {w : Model n | (c b,w) ∈ stateChart x '' (K ∩ {q | q.1 ∈ X})} = L '' A := by
      ext w
      constructor
      · rintro ⟨⟨d,u⟩,⟨huK,huX⟩,hcoord⟩
        have hdb : d = b := c.injOn (hX huX) (hX hp) (congrArg Prod.fst hcoord)
        subst d
        exact ⟨u,huK,congrArg Prod.snd hcoord⟩
      · rintro ⟨u,hu,rfl⟩
        exact ⟨⟨b,u⟩,⟨hu,hp⟩,rfl⟩
    change L v ∈ convexHull ℝ {w | (c b,w) ∈ stateChart x '' (K ∩ {q | q.1 ∈ X})} ↔ v ∈ convexHull ℝ A
    have hL : L '' convexHull ℝ A = convexHull ℝ (L '' A) := L.toLinearMap.image_convexHull A
    rw [heq,← hL]
    exact L.injective.mem_set_image

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentHull_closed {K : Set (TangentBundle (model n) M)} (hK : IsCompact K) :
    IsClosed (tangentHull K) := by
  apply isClosed_iff_nhds.mpr
  intro p hp
  let c := chartAt (Model n) p.1
  obtain ⟨X,hXn,hXcl,hXc⟩ := exists_mem_nhds_isClosed_subset (c.open_source.mem_nhds (mem_chart_source (Model n) p.1))
  have hb : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  let K' := K ∩ {q : TangentBundle (model n) M | q.1 ∈ X}
  have hK' : IsCompact K' := hK.inter_right (hXcl.preimage hb)
  have hKS : K' ⊆ (stateChart p.1).source := fun q hq => (stateChart_source p.1 q).mpr (hXc hq.2)
  let C := stateChart p.1 '' K'
  have hC : IsCompact C := hK'.image_of_continuousOn ((stateChart p.1).continuousOn.mono hKS)
  have hH := fiberHull_compact hC
  have hpS : p ∈ (stateChart p.1).source := (stateChart_source p.1 p).mpr (mem_chart_source (Model n) p.1)
  have hcp : ContinuousAt (stateChart p.1) p := (stateChart p.1).continuousAt hpS
  have hpX : p.1 ∈ X := mem_of_mem_nhds hXn
  apply (tangentHull_chart p.1 K hXc hpX).mp
  by_contra hn
  have hpre : stateChart p.1 ⁻¹' (fiberHull C)ᶜ ∈ 𝓝 p :=
    hcp.preimage_mem_nhds (hH.isClosed.isOpen_compl.mem_nhds hn)
  have hbase : {q : TangentBundle (model n) M | q.1 ∈ X} ∈ 𝓝 p := hb.continuousAt.preimage_mem_nhds hXn
  obtain ⟨q,⟨hqX,hqC⟩,hqH⟩ := hp _ (inter_mem hbase hpre)
  exact hqC ((tangentHull_chart p.1 K hXc hqX).mpr hqH)

 theorem activeHullGraph_compact {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → M) (h : ι → ℝ) : IsCompact (activeHullGraph (n := n) y h) := by
  have hclosed : IsClosed (activeHullGraph (n := n) y h) :=
    tangentHull_closed (activeGraph_compact y h)
  apply (tangent_disk_compact (n := n) (M := M) (Metric.diam (univ : Set M))).of_isClosed_subset hclosed
  intro p hp
  exact activeHull_bound y h p.1 hp

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
