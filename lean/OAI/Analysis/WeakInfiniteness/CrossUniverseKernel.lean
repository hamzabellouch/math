import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws
import OAI.Analysis.WeakInfiniteness.UnitizationTensor

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

open TopologicalSpace Topology

universe u v w x y z

section

variable {A : Type u} {C D : Type v} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma minimalMapAny_right (q : C →⋆ₙₐ[ℂ] D) :
    minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q=minimalMapRight (A := A) q := by
  apply minimalTensor_hom_ext
  intro a c
  simp only [minimalMapAny_elementary,minimalMapRight_elementary]
  rfl

lemma minimalKernel_induction (q : C →⋆ₙₐ[ℂ] D)
    (S : Submodule ℂ (MinimalTensor A C)) (hS : IsClosed (S : Set (MinimalTensor A C)))
    (he : ∀ a c, q c=0 → minimalElementary a c ∈ S)
    (z : MinimalTensor A C) (hz : z.val ∈ tensorKernelIdeal (A := A) q) : z ∈ S := by
  let T : Submodule ℂ (SpatialAmbient A C) := S.map (minimalTensorSubalgebra A C).toSubmodule.subtype
  have hT : IsClosed (T : Set (SpatialAmbient A C)) := isClosed_closure.isClosedMap_subtype_val _ hS
  have hs : Submodule.span ℂ {z | ∃ a : A,∃ c : C,q c=0 ∧ z=spatialElementary a c} ≤ T := by
    apply Submodule.span_le.mpr
    rintro y ⟨a,c,hc,rfl⟩
    exact ⟨minimalElementary a c,he a c hc,rfl⟩
  change z.val ∈ (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A C)) at hz
  rw [tensorKernelIdeal_eq_closure_span] at hz
  obtain ⟨y,hy,hyz⟩ := (closure_minimal hs hT) hz
  exact (Subtype.ext hyz : y=z) ▸ hy

lemma exact_kernel_mapAny (hA : Exact A) (C D : Type u)
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (q : C →⋆ₙₐ[ℂ] D) (hq : Function.Surjective q)
    (z : MinimalTensor A C) (hz : minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z=0) :
    z.val ∈ tensorKernelIdeal (A := A) q := by
  apply hA C D q hq z
  exact (minimalMapRight_eq_zero_iff q z).mp (by rw [← minimalMapAny_right]; exact hz)

end

section KernelMap

variable {A : Type u} {B : Type w} {C D : Type v} {E F : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra F]

lemma minimalMapAny_tensorKernel (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] E)
    (q : C →⋆ₙₐ[ℂ] D) (r : E →⋆ₙₐ[ℂ] F) (hqr : ∀ c, q c=0 → r (ψ c)=0)
    (z : MinimalTensor A C) (hz : z.val ∈ tensorKernelIdeal (A := A) q) :
    (minimalMapAny φ ψ z).val ∈ tensorKernelIdeal (A := B) r := by
  let f := (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra B E)).comp (minimalMapAny φ ψ)
  let S := (tensorKernelIdeal (A := B) r).toSubmodule.comap (show MinimalTensor A C →ₗ[ℂ] SpatialAmbient B E from
    { toFun := f, map_add' := map_add f, map_smul' := map_smul f })
  apply minimalKernel_induction q S ?_ ?_ z hz
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous f)
  · intro a c hc
    change (minimalMapAny φ ψ (minimalElementary a c)).val ∈ tensorKernelIdeal (A := B) r
    rw [minimalMapAny_elementary]
    apply NonUnitalStarSubalgebra.le_topologicalClosure
    apply NonUnitalStarAlgebra.subset_adjoin
    exact ⟨φ a,ψ c,hqr c hc,rfl⟩

end KernelMap

section TensorEquivalence

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def minimalTensorEquiv (e : A ≃⋆ₐ[ℂ] B) (f : C ≃⋆ₐ[ℂ] D) :
    MinimalTensor A C ≃⋆ₐ[ℂ] MinimalTensor B D := by
  let F := minimalMapAny e.toNonUnitalStarAlgHom f.toNonUnitalStarAlgHom
  let G := minimalMapAny e.symm.toNonUnitalStarAlgHom f.symm.toNonUnitalStarAlgHom
  have hGF : G.comp F=NonUnitalStarAlgHom.id ℂ (MinimalTensor A C) := by
    apply minimalTensor_hom_ext
    intro a c
    simp [F,G]
  have hFG : F.comp G=NonUnitalStarAlgHom.id ℂ (MinimalTensor B D) := by
    apply minimalTensor_hom_ext
    intro a c
    simp [F,G]
  have hl : Function.LeftInverse G F := fun x => DFunLike.congr_fun hGF x
  have hr : Function.RightInverse G F := fun x => DFunLike.congr_fun hFG x
  exact StarAlgEquiv.ofBijective F ⟨hl.injective,hr.surjective⟩

@[simp] lemma minimalTensorEquiv_elementary (e : A ≃⋆ₐ[ℂ] B) (f : C ≃⋆ₐ[ℂ] D)
    (a : A) (c : C) : minimalTensorEquiv e f (minimalElementary a c)=minimalElementary (e a) (f c) :=
  minimalMapAny_elementary _ _ a c

end TensorEquivalence

end

end WeakPureInfiniteness
end

end OAI
