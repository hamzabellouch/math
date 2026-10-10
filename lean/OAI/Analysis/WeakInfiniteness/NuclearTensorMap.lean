import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseKernel
import OAI.Analysis.WeakInfiniteness.NuclearTensorBound

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

universe u v w x

section

variable {A : Type u} {B : Type v} {C : Type w}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

def tensorPolynomial : (A × C →₀ ℂ) →ₗ[ℂ] MinimalTensor A C :=
  Finsupp.linearCombination ℂ (fun p => minimalElementary p.1 p.2)

@[simp] lemma tensorPolynomial_single (a : A) (c : C) :
    tensorPolynomial (Finsupp.single (a,c) 1)=minimalElementary a c := by
  simp [tensorPolynomial]

lemma tensorPolynomial_dense : DenseRange (tensorPolynomial (A := A) (C := C)) := by
  have hd : (LinearMap.range (tensorPolynomial (A := A) (C := C))).topologicalClosure=⊤ := by
    apply minimal_elementary_span_dense _ (Submodule.isClosed_topologicalClosure _)
    intro a c
    apply Submodule.le_topologicalClosure
    exact ⟨Finsupp.single (a,c) 1,tensorPolynomial_single a c⟩
  apply dense_iff_closure_eq.mpr
  exact congrArg (fun S : Submodule ℂ (MinimalTensor A C) => (S : Set (MinimalTensor A C))) hd

lemma minimalTensor_clm_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : MinimalTensor A C →L[ℂ] E}
    (h : ∀ a c,f (minimalElementary a c)=g (minimalElementary a c)) : f=g := by
  have hs : LinearMap.ker (f-g).toLinearMap=⊤ := by
    apply minimal_elementary_span_dense _ (f-g).isClosed_ker
    intro a c
    change f (minimalElementary a c)-g (minimalElementary a c)=0
    exact sub_eq_zero.mpr (h a c)
  ext z
  have hz : z ∈ LinearMap.ker (f-g).toLinearMap := by rw [hs]; trivial
  exact sub_eq_zero.mp hz

def starHomContinuousLinear (f : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B where
  toLinearMap := { toFun := f, map_add' := map_add f, map_smul' := map_smul f }
  cont := nonUnitalStarHom_continuous f

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

def cpTensorPolynomial (φ : A →L[ℂ] B) : (A × C →₀ ℂ) →ₗ[ℂ] MinimalTensor B C :=
  Finsupp.linearCombination ℂ (fun p => minimalElementary (φ p.1) p.2)

lemma norm_cpTensorPolynomial_le (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) (d : A × C →₀ ℂ) :
    ‖cpTensorPolynomial φ d‖ ≤ (4*‖φ‖)*‖tensorPolynomial d‖ := by
  classical
  change ‖(minimalTensorSubalgebra B C).subtype (d.sum fun p t => t • minimalElementary (φ p.1) p.2)‖ ≤
    (4*‖φ‖)*‖(minimalTensorSubalgebra A C).subtype (d.sum fun p t => t • minimalElementary p.1 p.2)‖
  simp only [Finsupp.sum,map_sum,map_smul]
  change ‖∑ p ∈ d.support,d p • spatialElementary (φ p.1) p.2‖ ≤
    (4*‖φ‖)*‖∑ p ∈ d.support,d p • spatialElementary p.1 p.2‖
  simpa only [map_smul,spatialElementary_smul_left] using
    norm_spatialSum_cp d.support (fun p => d p • p.1) Prod.snd φ hφ

def minimalCPMap (φ : A →L[ℂ] B) : MinimalTensor A C →L[ℂ] MinimalTensor B C :=
  (cpTensorPolynomial φ).extendOfNorm tensorPolynomial

lemma minimalCPMap_polynomial (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) (d : A × C →₀ ℂ) :
    minimalCPMap φ (tensorPolynomial d)=cpTensorPolynomial φ d :=
  LinearMap.extendOfNorm_eq tensorPolynomial_dense ⟨4*‖φ‖,norm_cpTensorPolynomial_le φ hφ⟩ d

lemma minimalCPMap_elementary (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) (a : A) (c : C) :
    minimalCPMap φ (minimalElementary a c)=minimalElementary (φ a) c := by
  rw [← tensorPolynomial_single a c,minimalCPMap_polynomial φ hφ]
  simp [cpTensorPolynomial]

lemma norm_minimalCPMap_le (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) (z : MinimalTensor A C) :
    ‖minimalCPMap φ z‖ ≤ (4*‖φ‖)*‖z‖ :=
  LinearMap.norm_extendOfNorm_apply_le tensorPolynomial_dense _ (norm_cpTensorPolynomial_le φ hφ) z

lemma minimalCPMap_kernel {D : Type w} [NonUnitalCStarAlgebra D]
    (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) (q : C →⋆ₙₐ[ℂ] D)
    (z : MinimalTensor A C) (hz : z.val ∈ tensorKernelIdeal (A := A) q) :
    (minimalCPMap φ z).val ∈ tensorKernelIdeal (A := B) q := by
  let f := (starHomContinuousLinear (minimalAmbientInclusion (A := B) (B := C))).comp (minimalCPMap φ)
  let S := (tensorKernelIdeal (A := B) q).toSubmodule.comap f.toLinearMap
  apply minimalKernel_induction q S ?_ ?_ z hz
  · exact isClosed_closure.preimage f.continuous
  · intro a c hc
    change (minimalCPMap φ (minimalElementary a c)).val ∈ tensorKernelIdeal (A := B) q
    rw [minimalCPMap_elementary φ hφ]
    apply NonUnitalStarSubalgebra.le_topologicalClosure
    apply NonUnitalStarAlgebra.subset_adjoin
    exact ⟨φ a,c,hc,rfl⟩

lemma minimalCPMap_right_comm {D : Type w} [NonUnitalCStarAlgebra D]
    (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) (q : C →⋆ₙₐ[ℂ] D)
    (z : MinimalTensor A C) :
    minimalMapRight q (minimalCPMap φ z)=minimalCPMap φ (minimalMapRight q z) := by
  let f : MinimalTensor B C →L[ℂ] MinimalTensor B D := starHomContinuousLinear (minimalMapRight q)
  let g : MinimalTensor A C →L[ℂ] MinimalTensor A D := starHomContinuousLinear (minimalMapRight q)
  let F : MinimalTensor A C →L[ℂ] MinimalTensor B C := minimalCPMap φ
  let G : MinimalTensor A D →L[ℂ] MinimalTensor B D := minimalCPMap φ
  have he : f.comp F=G.comp g := by
    apply minimalTensor_clm_ext
    intro a c
    change minimalMapRight q (minimalCPMap φ (minimalElementary a c))=
      minimalCPMap φ (minimalMapRight q (minimalElementary a c))
    rw [minimalCPMap_elementary φ hφ,minimalMapRight_elementary,minimalMapRight_elementary,
      minimalCPMap_elementary φ hφ]
  exact DFunLike.congr_fun he z

end

end

end WeakPureInfiniteness
end

end OAI
