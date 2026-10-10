import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SmoothLeafManifold
import OAI.Geometry.SplitTangent.SmoothLeafProjection
import OAI.Geometry.SplitTangent.EverywhereSmoothLeafQuotient
import OAI.Geometry.SplitTangent.ProductCriteria

namespace OAI

/-! Leaf Products. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent

lemma TangentSplitting.ext_projector {X : ComplexManifold.{u}} {S T : TangentSplitting X}
    (h : S.projector=T.projector) : S=T := by
  cases S
  cases T
  cases h
  rfl

lemma TangentSplitting.swap_swap_eq {X : ComplexManifold.{u}} (S : TangentSplitting X) :
    S.swap.swap=S := by
  apply TangentSplitting.ext_projector
  funext x
  ext v
  change v-(v-S.projector x v)=S.projector x v
  abel

namespace LeafJetAtlas

lemma leaf_cast {X : ComplexManifold.{u}} {S T : TangentSplitting X}
    (h : S=T) (L : LeafJetAtlas S) (x : X.Carrier) :
    (h ▸ L).leaf x=L.leaf x := by
  cases h
  rfl

variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

 

theorem compatible_projective_product_of_leafPair_injective
    (hinj : Function.Injective (L.leafPair M e hRC hdim)) :
    HasCompatibleProjectiveProduct X S := by
  let N : LeafJetAtlas S.swap.swap := S.swap_swap_eq.symm ▸ L
  have hinj' : Function.Injective (M.leafPair N e hRC hdim) := by
    intro x y hxy
    apply hinj
    apply Prod.ext
    · have he := congrArg Prod.snd hxy
      change N.leafQuotient e hRC hdim x=N.leafQuotient e hRC hdim y at he
      have hm := (N.leafQuotient_eq_iff e hRC hdim x y).mp he
      apply (L.leafQuotient_eq_iff e hRC hdim x y).mpr
      change y∈N.leaf x at hm
      rw [leaf_cast S.swap_swap_eq.symm L x] at hm
      exact hm
    · exact congrArg Prod.fst hxy
  have hL : ∀x,L.leafQuotient e hRC hdim x∈L.smoothLeafLocus e hRC hdim := by
    intro x
    rw [L.smoothLeafLocus_eq_univ_of_pair_injective M e hRC hdim hinj]
    exact mem_univ _
  have hM : ∀x,M.leafQuotient e hRC hdim x∈M.smoothLeafLocus e hRC hdim := by
    intro x
    rw [M.smoothLeafLocus_eq_univ_of_pair_injective N e hRC hdim hinj']
    exact mem_univ _
  let x₀ := Classical.arbitrary X.Carrier
  let Y := SmoothLeafManifold.manifold (L := M) (e := e) (hRC := hRC) (hdim := hdim) N x₀
  let Z := SmoothLeafManifold.manifold (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀
  let p : X.Carrier → Y.Carrier := SmoothLeafManifold.projection N x₀ hM
  let q : X.Carrier → Z.Carrier := SmoothLeafManifold.projection M x₀ hL
  have hp := SmoothLeafManifold.projection_holomorphic N x₀ hM
  have hq := SmoothLeafManifold.projection_holomorphic M x₀ hL
  have hk₁ (x) : LinearMap.ker
      (mfderiv (ModelWithCorners X) (ModelWithCorners Y) p x).toLinearMap=S.second x := by
    have h := SmoothLeafManifold.projection_kernel N x₀ hM x
    rw [S.swap_first] at h
    exact h
  have hk₂ (x) : LinearMap.ker
      (mfderiv (ModelWithCorners X) (ModelWithCorners Z) q x).toLinearMap=S.first x :=
    SmoothLeafManifold.projection_kernel M x₀ hL x
  have hb : Function.Bijective (fun x => (p x,q x)) := by
    constructor
    · intro x y hxy
      apply hinj
      exact Prod.ext (congrArg (fun z => z.2.val) hxy) (congrArg (fun z => z.1.val) hxy)
    · intro yz
      obtain ⟨x,hx⟩ := L.surjective_leafPair M e hRC hdim (yz.2.val,yz.1.val)
      exact ⟨x,Prod.ext (Subtype.ext (congrArg Prod.snd hx))
        (Subtype.ext (congrArg Prod.fst hx))⟩
  exact S.compatible_product_of_bijective_quotients e Y Z p q hp hq
    (SmoothLeafManifold.projection_submersion N x₀ hM)
    (SmoothLeafManifold.projection_submersion M x₀ hL) hk₁ hk₂ hb

end LeafJetAtlas
end SplitTangent

end

end OAI
