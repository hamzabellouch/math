import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseKernel
import OAI.Analysis.WeakInfiniteness.SmallCStar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u v

lemma exact_kernel_small (A : Type u) [NonUnitalCStarAlgebra A] (hA : Exact A)
    {C D : Type v} [CStarAlgebra C] [CStarAlgebra D]
    [Small.{0} C] [Small.{0} D]
    (q : C →⋆ₙₐ[ℂ] D) (hq : Function.Surjective q)
    (z : MinimalTensor A C)
    (hz : minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z=0) :
    z.val ∈ tensorKernelIdeal (A := A) q := by
  let E := ULift.{u} (SmallCStarCarrier C)
  let F := ULift.{u} (SmallCStarCarrier D)
  let e : E ≃⋆ₐ[ℂ] C := uliftStarAlgEquiv.trans (smallCStarStarAlgEquiv C)
  let f : F ≃⋆ₐ[ℂ] D := uliftStarAlgEquiv.trans (smallCStarStarAlgEquiv D)
  let r : E →⋆ₙₐ[ℂ] F := f.symm.toNonUnitalStarAlgHom.comp (q.comp e.toNonUnitalStarAlgHom)
  have hr : Function.Surjective r := f.symm.surjective.comp (hq.comp e.surjective)
  let idA := NonUnitalStarAlgHom.id ℂ A
  let Z := minimalMapAny idA e.symm.toNonUnitalStarAlgHom z
  have heq : (minimalMapAny idA r).comp (minimalMapAny idA e.symm.toNonUnitalStarAlgHom)=
      (minimalMapAny idA f.symm.toNonUnitalStarAlgHom).comp (minimalMapAny idA q) := by
    apply minimalTensor_hom_ext
    intro a c
    rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply,
      minimalMapAny_elementary idA e.symm.toNonUnitalStarAlgHom,
      minimalMapAny_elementary idA r, minimalMapAny_elementary idA q,
      minimalMapAny_elementary idA f.symm.toNonUnitalStarAlgHom]
    change minimalElementary a (f.symm (q (e (e.symm c)))) =
      minimalElementary a (f.symm (q c))
    rw [e.apply_symm_apply]
  have hZ : minimalMapAny idA r Z=0 := by
    change ((minimalMapAny idA r).comp (minimalMapAny idA e.symm.toNonUnitalStarAlgHom)) z=0
    rw [heq]
    change minimalMapAny idA f.symm.toNonUnitalStarAlgHom (minimalMapAny idA q z)=0
    rw [hz,map_zero]
  have hm := exact_kernel_mapAny hA E F r hr Z hZ
  have hqr : ∀ c, r c=0 → q (e c)=0 := by
    intro c hc
    change f.symm (q (e c)) = 0 at hc
    have hh := congrArg f hc
    simpa only [StarAlgEquiv.apply_symm_apply, map_zero] using hh
  have hh := minimalMapAny_tensorKernel idA e.toNonUnitalStarAlgHom r q hqr Z hm
  have hi : (minimalMapAny idA e.toNonUnitalStarAlgHom).comp
      (minimalMapAny idA e.symm.toNonUnitalStarAlgHom)=
      NonUnitalStarAlgHom.id ℂ (MinimalTensor A C) := by
    apply minimalTensor_hom_ext
    intro a c
    rw [NonUnitalStarAlgHom.comp_apply,
      minimalMapAny_elementary idA e.symm.toNonUnitalStarAlgHom,
      minimalMapAny_elementary idA e.toNonUnitalStarAlgHom]
    change minimalElementary a (e (e.symm c)) = minimalElementary a c
    rw [e.apply_symm_apply]
  have hzz : minimalMapAny idA e.toNonUnitalStarAlgHom Z=z := DFunLike.congr_fun hi z
  rwa [hzz] at hh

end

end WeakPureInfiniteness
end

end OAI
