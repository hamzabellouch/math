import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseKernel
import OAI.Analysis.WeakInfiniteness.CrossUniverseLeftMap

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

open Filter Topology

universe u v w

lemma kernel_of_injective_unital {A : Type u} {B : Type v} {C D : Type w}
    [CStarAlgebra A] [CStarAlgebra B] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (q : C →⋆ₙₐ[ℂ] D)
    (hB : ∀ z : MinimalTensor B C, minimalMapAny (NonUnitalStarAlgHom.id ℂ B) q z=0 →
      z.val ∈ tensorKernelIdeal (A := B) q)
    (z : MinimalTensor A C) (hz : minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z=0) :
    z.val ∈ tensorKernelIdeal (A := A) q := by
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let I := kernelAlgebra q
  let := CStarAlgebra.spectralOrder I
  let := CStarAlgebra.spectralOrderedRing I
  let l := CStarAlgebra.approximateUnit I
  have hl := CStarAlgebra.increasingApproximateUnit I
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  let e : I → C := Subtype.val
  have he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1 := by
    filter_upwards [hl.eventually_nonneg,hl.eventually_norm] with i hi hn
    refine ⟨?_,hn⟩
    obtain ⟨x,hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hi
    have hi' : e i=star (e x)*e x := congrArg Subtype.val hx
    rw [hi']
    exact star_mul_self_nonneg _
  have happ : ∀ c : C,q c=0 → Tendsto (fun i => c*e i) l (𝓝 c) := by
    intro c hc
    let x : I := ⟨c,hc⟩
    exact continuous_subtype_val.tendsto x |>.comp (hl.tendsto_mul_left x)
  let Φ : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B C := minimalMapLeftAny φ.toNonUnitalStarAlgHom
  have hm : (Φ z).val ∈ tensorKernelIdeal (A := B) q := by
    apply hB
    have heq := minimalMapLeftAny_right_comm φ.toNonUnitalStarAlgHom q
    have hh := DFunLike.congr_fun heq z
    change minimalMapAny (NonUnitalStarAlgHom.id ℂ B) q (Φ z)=minimalMapLeftAny φ.toNonUnitalStarAlgHom (minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z) at hh
    rw [hh,hz,map_zero]
  have hcuts := tensorCut_tendsto_zero_on_ideal l e he q happ (Φ z) hm
  have hcutz : Tendsto (fun i => tensorCut (e i) z) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := tendsto_zero_iff_norm_tendsto_zero.mp hcuts
    convert hn using 1
    funext i
    rw [← minimalMapLeftAny_tensorCut]
    exact (norm_minimalMapLeftAny φ.toNonUnitalStarAlgHom hφ _).symm
  exact tensor_mem_ideal_of_cuts l e q (fun i => i.property) z hcutz

lemma universal_fixed_kernel_impossible
    (h : ∀ z : MinimalTensor UniversalContraction (FullGroupAlgebra (FreeGroup Bool)),
      minimalMapAny (NonUnitalStarAlgHom.id ℂ UniversalContraction)
        fullToReducedLarge.toNonUnitalStarAlgHom z=0 →
      z.val ∈ tensorKernelIdeal (A := UniversalContraction) fullToReducedLarge.toNonUnitalStarAlgHom) : False := by
  apply not_le_of_gt freeDiagonalFunctional_witness_gap
  apply freeDiagonalFunctional_bound_of_kernel
  intro z hz
  have hm := kernel_of_injective_unital fullToUniversal fullToUniversal_injective
    fullToReducedLarge.toNonUnitalStarAlgHom h z ((DFunLike.congr_fun (minimalMapAny_right fullToReducedLarge.toNonUnitalStarAlgHom) z).trans hz)
  apply minimalKernel_induction fullToReducedLarge.toNonUnitalStarAlgHom
    freeDiagonalFunctional.toLinearMap.ker
    (isClosed_singleton.preimage freeDiagonalFunctional.continuous) ?_ z hm
  intro a c hc
  exact freeDiagonalFunctional_large_elementary_kernel a c hc

end

end WeakPureInfiniteness
end

end OAI
