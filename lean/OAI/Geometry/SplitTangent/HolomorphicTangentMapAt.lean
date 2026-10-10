import Mathlib
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Holomorphic Tangent Map At. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent

 

lemma holomorphicAt_tangentMap {X Y : ComplexManifold.{u}}
    {f : X.Carrier → Y.Carrier} {x : X.Carrier}
    (hf : ContMDiffAt (ModelWithCorners X) (ModelWithCorners Y) ω f x)
    (v : Tangent X x) :
    ContMDiffAt ((ModelWithCorners X).prod 𝓘(ℂ,Model X))
      ((ModelWithCorners Y).prod 𝓘(ℂ,Model Y)) ω
      (tangentMap (ModelWithCorners X) (ModelWithCorners Y) f)
      (⟨x,v⟩ : TangentBundle (ModelWithCorners X) X.Carrier) := by
  obtain ⟨s,hs,hfs⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp : (ω : WithTop ℕ∞)≠∞)).mp hf
  obtain ⟨U,hUs,hU,hxU⟩ := mem_nhds_iff.mp hs
  have hFU := hfs.mono hUs
  have hTU := hFU.contMDiffOn_tangentMapWithin (m := ω) (by simp) hU.uniqueMDiffOn
  have hπ : Continuous (fun p : TangentBundle (ModelWithCorners X) X.Carrier => p.proj) :=
    (contMDiff_proj (IB := ModelWithCorners X) (n := ω) (TangentSpace (ModelWithCorners X))).continuous
  have hn : (fun p : TangentBundle (ModelWithCorners X) X.Carrier => p.proj) ⁻¹' U ∈
      𝓝 (⟨x,v⟩ : TangentBundle (ModelWithCorners X) X.Carrier) :=
    hπ.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
  apply (hTU.contMDiffAt hn).congr_of_eventuallyEq
  filter_upwards [hn] with p hp
  exact (tangentMapWithin_eq_tangentMap (hU.uniqueMDiffOn p.proj hp)
    ((hFU.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))).symm

end SplitTangent

end

end OAI
