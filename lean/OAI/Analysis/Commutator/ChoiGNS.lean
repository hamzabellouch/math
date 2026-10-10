import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.ChoiGNS

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type} [Fintype ι]

local instance choiGNSDecidableEq : DecidableEq ι := Classical.decEq ι

def entry (i j : ι) (a : A) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (fun k l => if k=i ∧ l=j then a else 0)

omit [Fintype ι] in
@[simp] lemma entry_apply (i j k l : ι) (a : A) :
    entry i j a k l=if k=i ∧ l=j then a else 0 := rfl

omit [Fintype ι] in
@[simp] lemma entry_star (i j : ι) (a : A) : star (entry i j a)=entry j i (star a) := by
  ext k l
  by_cases h : k=j ∧ l=i <;> simp [CStarMatrix.star_apply,entry_apply,and_comm,h]

lemma entry_mul (i j k l : ι) (a b : A) :
    entry i j a*entry k l b=if j=k then entry i l (a*b) else 0 := by
  ext r s
  by_cases hjk : j=k <;> by_cases hr : r=i <;> by_cases hs : s=l <;>
    simp [CStarMatrix.mul_apply,entry_apply,hjk,hr,hs,ite_mul,mul_ite,eq_comm]

def diagonal : A →⋆ₐ[ℂ] CStarMatrix ι ι A where
  toFun a := CStarMatrix.ofMatrix (fun i j => if i=j then a else 0)
  map_zero' := by ext i j; change (if i=j then 0 else 0)=(0 : A); simp
  map_one' := by ext i j; rfl
  map_add' a b := by
    ext i j
    change (if i=j then a+b else 0)=(if i=j then a else 0)+(if i=j then b else 0)
    by_cases h : i=j <;> simp [h]
  map_mul' a b := by
    ext i j
    rw [CStarMatrix.mul_apply]
    change (if i=j then a*b else 0)=∑ k,(if i=k then a else 0)*(if k=j then b else 0)
    simp [ite_mul,mul_ite]
  commutes' c := by
    ext i j
    change (if i=j then algebraMap ℂ A c else 0)=(algebraMap ℂ (CStarMatrix ι ι A) c) i j
    by_cases h : i=j <;> simp [Algebra.algebraMap_eq_smul_one,h]
  map_star' a := by
    ext i j
    rw [CStarMatrix.star_apply]
    change (if i=j then star a else 0)=star (if j=i then a else 0)
    by_cases h : i=j <;> simp [h,eq_comm]

@[simp] lemma diagonal_apply (a : A) (i j : ι) : diagonal a i j=if i=j then a else 0 := rfl

lemma diagonal_entry (a b : A) (i j : ι) : diagonal a*entry i j b=entry i j (a*b) := by
  ext k l
  by_cases hki : k=i <;> by_cases hlj : l=j <;>
    simp [CStarMatrix.mul_apply,diagonal_apply,entry_apply,ite_mul,mul_ite,hki,hlj]

lemma entry_diagonal_entry (a : A) (i₀ i j : ι) :
    star (entry i₀ i (1 : A))*(diagonal a*entry i₀ j 1)=entry i j a := by
  rw [entry_star,star_one,diagonal_entry,mul_one,entry_mul,ite_eq_left rfl,one_mul]

variable [PartialOrder A] [StarOrderedRing A]

def vector (η : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] η.GNS :=
  UniformSpace.Completion.toComplL.toLinearMap.comp η.toPreGNS.toLinearMap

@[simp] lemma vector_apply (η : A →ₚ[ℂ] ℂ) (a : A) : vector η a=(η.toPreGNS a : η.GNS) := rfl

lemma inner_vector (η : A →ₚ[ℂ] ℂ) (a b : A) :
    ⟪vector η a,vector η b⟫_ℂ=η (star a*b) := by
  simp [vector_apply,UniformSpace.Completion.inner_coe,PositiveLinearMap.preGNS_inner_def]

lemma representation_vector (η : A →ₚ[ℂ] ℂ) (a b : A) :
    η.gnsStarAlgHom a (vector η b)=vector η (a*b) := by
  simp [vector_apply,PositiveLinearMap.gnsStarAlgHom]

end Kadison.ChoiGNS

end

end
end

end OAI
