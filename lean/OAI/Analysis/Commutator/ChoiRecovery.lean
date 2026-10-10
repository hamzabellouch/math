import Mathlib
import OAI.Analysis.Commutator.ChoiFunctional
import OAI.Analysis.Commutator.ChoiGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.OperatorSystem

open ChoiGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

def choiEmbedding (η : CStarMatrix ι ι A →ₚ[ℂ] ℂ) (i₀ : ι) : CoordinateSpace ι →L[ℂ] η.GNS :=
  ({ toFun x := ∑ i,x i • vector η (entry i₀ i 1)
     map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
     map_smul' c x := by simp [mul_smul,Finset.smul_sum] } :
    CoordinateSpace ι →ₗ[ℂ] η.GNS).toContinuousLinearMap

@[simp] lemma choiEmbedding_apply (η : CStarMatrix ι ι A →ₚ[ℂ] ℂ) (i₀ : ι) (x : CoordinateSpace ι) :
    choiEmbedding η i₀ x=∑ i,x i • vector η (entry i₀ i 1) := rfl

@[simp] lemma choiEmbedding_basis (η : CStarMatrix ι ι A →ₚ[ℂ] ℂ) (i₀ j : ι) :
    choiEmbedding η i₀ (basisVector j)=vector η (entry i₀ j 1) := by
  simp [choiEmbedding_apply,basisVector_apply,ite_smul]

def choiRepresentation (η : CStarMatrix ι ι A →ₚ[ℂ] ℂ) : A →⋆ₐ[ℂ] (η.GNS →L[ℂ] η.GNS) :=
  η.gnsStarAlgHom.comp diagonal

lemma choi_coefficient (η : CStarMatrix ι ι A →ₚ[ℂ] ℂ) (i₀ i j : ι) (a : A) :
    ⟪basisVector i,(choiEmbedding η i₀).adjoint
      (choiRepresentation η a (choiEmbedding η i₀ (basisVector j)))⟫_ℂ=η (entry i j a) := by
  rw [ContinuousLinearMap.adjoint_inner_right,choiEmbedding_basis,choiEmbedding_basis]
  change ⟪vector η (entry i₀ i 1),η.gnsStarAlgHom (diagonal a) (vector η (entry i₀ j 1))⟫_ℂ=_
  rw [representation_vector,inner_vector,entry_diagonal_entry]

omit [PartialOrder A] [StarOrderedRing A] in
lemma entry_mem (S : Submodule ℂ A) (a : S) (i j : ι) : entry i j (a : A)∈matrices S ι := by
  intro k l
  by_cases h : k=i ∧ l=j <;> simp [entry_apply,h,a.property]

def systemEntry (S : Submodule ℂ A) (a : S) (i j : ι) : matrices S ι :=
  ⟨entry i j (a : A),entry_mem S a i j⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma mapMatrix_systemEntry (S : Submodule ℂ A)
    (f : S →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι)) (a : S) (i j k l : ι) :
    mapMatrix S f (systemEntry S a i j) k l=if k=i ∧ l=j then f a else 0 := by
  by_cases h : k=i ∧ l=j
  · have he : (⟨(systemEntry S a i j).val k l,(systemEntry S a i j).property k l⟩ : S)=a := by
      apply Subtype.ext
      simp [systemEntry,entry_apply,h]
    rw [mapMatrix_apply,he,ite_eq_left h]
  · have he : (⟨(systemEntry S a i j).val k l,(systemEntry S a i j).property k l⟩ : S)=0 := by
      apply Subtype.ext
      simp [systemEntry,entry_apply,h]
    rw [mapMatrix_apply,he,map_zero,ite_eq_right h]

omit [PartialOrder A] [StarOrderedRing A] in
lemma choi_systemEntry (S : Submodule ℂ A)
    (f : S →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι)) (a : S) (i j : ι) :
    choi S f (systemEntry S a i j)=⟪basisVector i,f a (basisVector j)⟫_ℂ := by
  change (∑ k,∑ l,⟪basisVector k,mapMatrix S f (systemEntry S a i j) k l (basisVector l)⟫_ℂ)=_
  simp only [mapMatrix_systemEntry]
  have he (k l : ι) : ⟪basisVector k,(if k=i ∧ l=j then f a else 0) (basisVector l)⟫_ℂ=
      if k=i ∧ l=j then ⟪basisVector k,f a (basisVector l)⟫_ℂ else 0 := by
    by_cases h : k=i ∧ l=j <;> simp [h]
  simp_rw [he]
  simp [ite_and]

lemma sum_basis (x : CoordinateSpace ι) : ∑ i,x i • basisVector i=x := by
  ext j
  simp [basisVector_apply]

lemma basis_inner_ext (T U : CoordinateSpace ι →L[ℂ] CoordinateSpace ι)
    (h : ∀ i j,⟪basisVector i,T (basisVector j)⟫_ℂ=⟪basisVector i,U (basisVector j)⟫_ℂ) : T=U := by
  have he (j : ι) : T (basisVector j)=U (basisVector j) := by
    apply ext_inner_left ℂ
    intro x
    rw [←sum_basis x]
    simp only [sum_inner,inner_smul_left]
    exact Finset.sum_congr rfl (fun i _ => by rw [h i j])
  ext x
  rw [←sum_basis x]
  simp [he]

end Kadison.OperatorSystem

end

end
end

end OAI
