import Mathlib
import OAI.Geometry.SplitTangent.CompactSetLimits
import OAI.Geometry.SplitTangent.FoliationLeaves
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.LeafCompactLimits
import OAI.Geometry.SplitTangent.LeafLimitsSinglePlaque

namespace OAI

/-! Compact Leaf Quotient. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

lemma isClosed_range_compactLeaf : IsClosed (range (L.compactLeaf e hRC hdim)) := by
  apply isClosed_of_closure_subset
  intro K hK
  obtain ⟨x,hx⟩ := L.leafLimits_nonempty e hRC hdim hK
  exact ⟨x,Compacts.ext (L.leafLimits_eq_leaf e hRC hdim hK hx).symm⟩

lemma compactLeaf_eq_of_mem {x y : X.Carrier} (h : y∈L.leaf x) :
    L.compactLeaf e hRC hdim y=L.compactLeaf e hRC hdim x :=
  Compacts.ext (L.plaques.leaf_eq_of_mem h)

lemma isClosed_graph_compactLeaf :
    IsClosed {p : X.Carrier × Compacts X.Carrier | p.2=L.compactLeaf e hRC hdim p.1} := by
  have hC := (L.isClosed_range_compactLeaf e hRC hdim).preimage (continuous_snd : Continuous (Prod.snd : X.Carrier × Compacts X.Carrier → _))
  have hI := (CompactSetLimits.isClosed_incidence (X := X.Carrier)).preimage (continuous_swap : Continuous (Prod.swap : X.Carrier × Compacts X.Carrier → _))
  convert hC.inter hI using 1
  ext p
  constructor
  · intro h
    refine ⟨⟨p.1,h.symm⟩,?_⟩
    change p.1∈(p.2 : Set X.Carrier)
    rw [show p.2=L.compactLeaf e hRC hdim p.1 from h]
    exact PlaqueSystem.Reachable.refl L.plaques p.1
  · intro h
    rcases h.1 with ⟨y,hy⟩
    have hx : p.1∈L.leaf y := by
      change p.1∈(L.compactLeaf e hRC hdim y : Set X.Carrier)
      rw [hy]
      exact h.2
    exact hy.symm.trans (L.compactLeaf_eq_of_mem e hRC hdim hx).symm

lemma continuous_compactLeaf : Continuous (L.compactLeaf e hRC hdim) := by
  apply continuous_iff_isClosed.mpr
  intro C hC
  have hh := isClosedMap_fst_of_compactSpace _
    ((L.isClosed_graph_compactLeaf e hRC hdim).inter (hC.preimage continuous_snd))
  convert hh using 1
  ext x
  constructor
  · intro hx
    exact ⟨(x,L.compactLeaf e hRC hdim x),⟨rfl,hx⟩,rfl⟩
  · rintro ⟨⟨y,K⟩,⟨hK,hC⟩,rfl⟩
    change K=L.compactLeaf e hRC hdim y at hK
    change L.compactLeaf e hRC hdim y∈C
    rwa [hK] at hC

 

def CompactLeafSpace := range (L.compactLeaf e hRC hdim)

instance compactSpace_compactLeafSpace : CompactSpace (L.CompactLeafSpace e hRC hdim) :=
  isCompact_iff_compactSpace.mp (L.isClosed_range_compactLeaf e hRC hdim).isCompact

def leafQuotient (x : X.Carrier) : L.CompactLeafSpace e hRC hdim :=
  ⟨L.compactLeaf e hRC hdim x,⟨x,rfl⟩⟩

lemma continuous_leafQuotient : Continuous (L.leafQuotient e hRC hdim) :=
  (L.continuous_compactLeaf e hRC hdim).subtype_mk _

lemma surjective_leafQuotient : Function.Surjective (L.leafQuotient e hRC hdim) := by
  rintro ⟨K,x,rfl⟩
  exact ⟨x,rfl⟩

lemma leafQuotient_eq_iff (x y : X.Carrier) :
    L.leafQuotient e hRC hdim x=L.leafQuotient e hRC hdim y ↔ y∈L.leaf x := by
  constructor
  · intro h
    have h' : L.leaf x=L.leaf y := congrArg (fun K => (K.val : Set X.Carrier)) h
    rw [h']
    exact PlaqueSystem.Reachable.refl L.plaques y
  · intro h
    exact Subtype.ext (L.compactLeaf_eq_of_mem e hRC hdim h).symm

lemma isQuotientMap_leafQuotient : IsQuotientMap (L.leafQuotient e hRC hdim) :=
  (L.continuous_leafQuotient e hRC hdim).isClosedMap.isQuotientMap
    (L.continuous_leafQuotient e hRC hdim) (L.surjective_leafQuotient e hRC hdim)

lemma isClosedMap_leafQuotient : IsClosedMap (L.leafQuotient e hRC hdim) :=
  (L.continuous_leafQuotient e hRC hdim).isClosedMap

lemma leafQuotient_image (U : Set X.Carrier) :
    L.leafQuotient e hRC hdim '' U=
      {K : L.CompactLeafSpace e hRC hdim | ((K.val : Set X.Carrier)∩U).Nonempty} := by
  ext K
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,PlaqueSystem.Reachable.refl L.plaques x,hx⟩
  · rintro ⟨x,hxK,hxU⟩
    refine ⟨x,hxU,?_⟩
    obtain ⟨y,hy⟩ := K.property
    apply Subtype.ext
    change L.compactLeaf e hRC hdim x=K.val
    have hx : x∈L.leaf y := by
      change x∈(L.compactLeaf e hRC hdim y : Set X.Carrier)
      rwa [hy]
    exact (L.compactLeaf_eq_of_mem e hRC hdim hx).trans hy

lemma isOpenMap_leafQuotient : IsOpenMap (L.leafQuotient e hRC hdim) := by
  intro U hU
  rw [L.leafQuotient_image e hRC hdim U]
  exact (Compacts.isOpen_inter_nonempty_of_isOpen hU).preimage continuous_subtype_val

lemma isOpenQuotientMap_leafQuotient : IsOpenQuotientMap (L.leafQuotient e hRC hdim) :=
  ⟨L.surjective_leafQuotient e hRC hdim,L.continuous_leafQuotient e hRC hdim,
    L.isOpenMap_leafQuotient e hRC hdim⟩

instance connectedSpace_compactLeafSpace : ConnectedSpace (L.CompactLeafSpace e hRC hdim) :=
  (L.surjective_leafQuotient e hRC hdim).connectedSpace (L.continuous_leafQuotient e hRC hdim)

end SplitTangent.LeafJetAtlas

end

end OAI
