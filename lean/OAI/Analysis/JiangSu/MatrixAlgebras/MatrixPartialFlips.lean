import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.MatrixTensorDecomposition
import OAI.Analysis.JiangSu.Absorption.RealUnitaryFlow

namespace OAI


noncomputable section
namespace MatrixTensor
open JiangSuConstruction
open scoped CStarAlgebra Kronecker ComplexOrder

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
abbrev Four (I J : Type*) := (I×J)×(I×J)

def swapP : Equiv.Perm (Four I J) where
  toFun z := ((z.2.1,z.1.2),(z.1.1,z.2.2))
  invFun z := ((z.2.1,z.1.2),(z.1.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def swapQ : Equiv.Perm (Four I J) where
  toFun z := ((z.1.1,z.2.2),(z.2.1,z.1.2))
  invFun z := ((z.1.1,z.2.2),(z.2.1,z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def partialP : unitary (Mat (Four I J)) := permutationUnitary swapP
def partialQ : unitary (Mat (Four I J)) := permutationUnitary swapQ

lemma partialP_sq : (partialP : unitary (Mat (Four I J)))*partialP=1 := by
  rw [partialP,←permutationUnitary_mul]
  have h : (swapP : Equiv.Perm (Four I J))*swapP=1 := by apply Equiv.ext; intro z; rfl
  rw [h,permutationUnitary_one]
lemma partialQ_sq : (partialQ : unitary (Mat (Four I J)))*partialQ=1 := by
  rw [partialQ,←permutationUnitary_mul]
  have h : (swapQ : Equiv.Perm (Four I J))*swapQ=1 := by apply Equiv.ext; intro z; rfl
  rw [h,permutationUnitary_one]
lemma partial_commute : Commute (partialP : unitary (Mat (Four I J))) partialQ := by
  change permutationUnitary swapP*permutationUnitary swapQ=permutationUnitary swapQ*permutationUnitary swapP
  rw [←permutationUnitary_mul,←permutationUnitary_mul]
  congr 1
lemma partial_product : (partialP : unitary (Mat (Four I J)))*partialQ=
    permutationUnitary (Equiv.prodComm (I×J) (I×J)) := by
  rw [partialP,partialQ,←permutationUnitary_mul]
  congr 1

lemma partial_flip (a : Mat (I×J)) :
    unitaryConjugation (partialP (I := I) (J := J)*partialQ) (left (J := I×J) a)=right (I := I×J) a := by
  rw [partial_product]
  exact finite_matrix_tensor_flip a

def entryHom (i k : I) : Mat I →+ ℂ where
  toFun x := x i k
  map_zero' := rfl
  map_add' _ _ := rfl

lemma partialP_expansion : (partialP (I := I) (J := J) : Mat (Four I J))=
    ∑ i : I,∑ k : I,left (left (single i k 1) : Mat (I×J))*right (left (single k i 1)) := by
  simp_rw [left_mul_right]
  change ((swapP (I := I) (J := J))⁻¹).permMatrix ℂ =
    ∑ i : I,∑ k : I,(Matrix.single i k (1:ℂ) ⊗ₖ (1 : Matrix J J ℂ)) ⊗ₖ (Matrix.single k i (1:ℂ) ⊗ₖ (1 : Matrix J J ℂ))
  apply Matrix.ext
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨e,f⟩,⟨g,h⟩⟩
  simp only [Matrix.sum_apply,Matrix.kroneckerMap_apply]
  change (permutationUnitary (swapP (I := I) (J := J)) : Mat (Four I J)) ((a,b),(c,d)) ((e,f),(g,h))=_
  rw [permutationUnitary_apply]
  simp [swapP,Matrix.single,Matrix.one_apply,eq_comm,and_assoc,and_left_comm,and_comm,ite_and]
  split_ifs <;> rfl

lemma partialQ_expansion : (partialQ (I := I) (J := J) : Mat (Four I J))=
    ∑ i : J,∑ k : J,left (right (single i k 1) : Mat (I×J))*right (right (single k i 1)) := by
  simp_rw [left_mul_right]
  change ((swapQ (I := I) (J := J))⁻¹).permMatrix ℂ =
    ∑ i : J,∑ k : J,((1 : Matrix I I ℂ) ⊗ₖ Matrix.single i k (1:ℂ)) ⊗ₖ ((1 : Matrix I I ℂ) ⊗ₖ Matrix.single k i (1:ℂ))
  apply Matrix.ext
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨e,f⟩,⟨g,h⟩⟩
  simp only [Matrix.sum_apply,Matrix.kroneckerMap_apply]
  change (permutationUnitary (swapQ (I := I) (J := J)) : Mat (Four I J)) ((a,b),(c,d)) ((e,f),(g,h))=_
  rw [permutationUnitary_apply]
  simp [swapQ,Matrix.single,Matrix.one_apply,eq_comm,and_assoc,and_left_comm,and_comm,ite_and]
  split_ifs <;> rfl

lemma partialP_mem : (partialP (I := I) (J := J) : Mat (Four I J))∈
    fiberAlgebra (left (I := I) (J := J)).range (left (I := I) (J := J)).range := by
  rw [partialP_expansion]
  exact (fiberAlgebra _ _).sum_mem (fun i _ => (fiberAlgebra _ _).sum_mem
    (fun k _ => mul_mem_fiber _ _ ⟨_,rfl⟩ ⟨_,rfl⟩))
lemma partialQ_mem : (partialQ (I := I) (J := J) : Mat (Four I J))∈
    fiberAlgebra (right (I := I) (J := J)).range (right (I := I) (J := J)).range := by
  rw [partialQ_expansion]
  exact (fiberAlgebra _ _).sum_mem (fun j _ => (fiberAlgebra _ _).sum_mem
    (fun l _ => mul_mem_fiber _ _ ⟨_,rfl⟩ ⟨_,rfl⟩))

lemma partialQ_conjugate_right_tensor (a : Mat I) (b : Mat J) :
    unitaryConjugation (partialQ (I := I) (J := J))
      (right (I := I×J) (left (J := J) a*right (I := I) b))=
      left (J := I×J) (right (I := I) b)*right (I := I×J) (left (J := J) a) := by
  rw [partialQ,permutationUnitary_conjugation]
  ext ⟨⟨i,j⟩,⟨k,l⟩⟩ ⟨⟨i',j'⟩,⟨k',l'⟩⟩
  change (1 : Matrix (I×J) (I×J) ℂ) (i,l) (i',l')*(left (J := J) a*right (I := I) b : Mat (I×J)) (k,j) (k',j')=
    (left (J := I×J) (right (I := I) b)*right (I := I×J) (left (J := J) a) : Mat (Four I J)) ((i,j),(k,l)) ((i',j'),(k',l'))
  rw [left_mul_right_apply,left_mul_right_apply]
  change _=((1 : Matrix I I ℂ) i i'*b j j')*(a k k'*(1 : Matrix J J ℂ) l l')
  simp only [Matrix.one_apply,Prod.mk.injEq]
  by_cases hi : i=i' <;> by_cases hl : l=l' <;> simp [hi,hl]; ring

lemma partialP_conjugate_right_tensor (a : Mat I) (b : Mat J) :
    unitaryConjugation (partialP (I := I) (J := J))
      (right (I := I×J) (left (J := J) a*right (I := I) b))=
      left (J := I×J) (left (J := J) a)*right (I := I×J) (right (I := I) b) := by
  rw [partialP,permutationUnitary_conjugation]
  ext ⟨⟨i,j⟩,⟨k,l⟩⟩ ⟨⟨i',j'⟩,⟨k',l'⟩⟩
  change (1 : Matrix (I×J) (I×J) ℂ) (k,j) (k',j')*(left (J := J) a*right (I := I) b : Mat (I×J)) (i,l) (i',l')=
    (left (J := I×J) (left (J := J) a)*right (I := I×J) (right (I := I) b) : Mat (Four I J)) ((i,j),(k,l)) ((i',j'),(k',l'))
  rw [left_mul_right_apply,left_mul_right_apply]
  change _=(a i i'*(1 : Matrix J J ℂ) j j')*((1 : Matrix I I ℂ) k k'*b l l')
  simp only [Matrix.one_apply,Prod.mk.injEq]
  by_cases hj : j=j' <;> by_cases hk : k=k' <;> simp [hj,hk]

end MatrixTensor

end


noncomputable section
namespace MatrixTensor
open JiangSuConstruction FourEdgeSurgery
open scoped CStarAlgebra ComplexOrder

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma partialP_star : star (partialP (I := I) (J := J) : Mat (Four I J))= (partialP (I := I) (J := J) : Mat (Four I J)) := by
  have h : (partialP (I := I) (J := J))⁻¹=partialP (I := I) (J := J) := inv_eq_of_mul_eq_one_left partialP_sq
  exact congrArg Subtype.val h
lemma partialQ_star : star (partialQ (I := I) (J := J) : Mat (Four I J))= (partialQ (I := I) (J := J) : Mat (Four I J)) := by
  have h : (partialQ (I := I) (J := J))⁻¹=partialQ (I := I) (J := J) := inv_eq_of_mul_eq_one_left partialQ_sq
  exact congrArg Subtype.val h

lemma partialQ_conjugate_right_mem (x : Mat (I×J)) :
    unitaryConjugation (partialQ (I := I) (J := J)) (right (I := I×J) x)∈
      fiberAlgebra (right (I := I) (J := J)).range (left (I := I) (J := J)).range := by
  let H : Mat (I×J) →⋆ₐ[ℂ] Mat (Four I J) :=
    (unitaryConjugation (partialQ (I := I) (J := J))).comp right
  let S := fiberAlgebra (right (I := I) (J := J)).range (left (I := I) (J := J)).range
  apply mem_of_pure_tensors (S.comap H) _ x
  intro a b
  change unitaryConjugation (partialQ (I := I) (J := J)) (right (left a*right b))∈S
  rw [partialQ_conjugate_right_tensor]
  exact mul_mem_fiber _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
lemma partialP_conjugate_right_mem (x : Mat (I×J)) :
    unitaryConjugation (partialP (I := I) (J := J)) (right (I := I×J) x)∈
      fiberAlgebra (left (I := I) (J := J)).range (right (I := I) (J := J)).range := by
  let H : Mat (I×J) →⋆ₐ[ℂ] Mat (Four I J) :=
    (unitaryConjugation (partialP (I := I) (J := J))).comp right
  let S := fiberAlgebra (left (I := I) (J := J)).range (right (I := I) (J := J)).range
  apply mem_of_pure_tensors (S.comap H) _ x
  intro a b
  change unitaryConjugation (partialP (I := I) (J := J)) (right (left a*right b))∈S
  rw [partialP_conjugate_right_tensor]
  exact mul_mem_fiber _ _ ⟨_,rfl⟩ ⟨_,rfl⟩

def pFlow : Flow (unitary (Mat (Four I J))) :=
  ⟨realUnitaryFlow (partialP (I := I) (J := J)),realUnitaryFlow_zero (partialP (I := I) (J := J)),realUnitaryFlow_add (partialP (I := I) (J := J))⟩
def qFlow : Flow (unitary (Mat (Four I J))) :=
  ⟨realUnitaryFlow (partialQ (I := I) (J := J)),realUnitaryFlow_zero (partialQ (I := I) (J := J)),realUnitaryFlow_add (partialQ (I := I) (J := J))⟩
lemma pFlow_continuous : Continuous (pFlow (I := I) (J := J)) := realUnitaryFlow_continuous _
lemma qFlow_continuous : Continuous (qFlow (I := I) (J := J)) := realUnitaryFlow_continuous _
@[simp] lemma pFlow_one : pFlow (I := I) (J := J) 1=partialP (I := I) (J := J) :=
  realUnitaryFlow_one _ (matrix_finite_spectrum _)
@[simp] lemma qFlow_one : qFlow (I := I) (J := J) 1=partialQ (I := I) (J := J) :=
  realUnitaryFlow_one _ (matrix_finite_spectrum _)
lemma flows_commute (r s : ℝ) : Commute (pFlow (I := I) (J := J) r) ((qFlow (I := I) (J := J)) s) :=
  realUnitaryFlow_commute_flow (partialP (I := I) (J := J)) (partialQ (I := I) (J := J)) partial_commute r s
lemma pFlow_mem (r : ℝ) : (pFlow (I := I) (J := J) r : Mat (Four I J))∈
    fiberAlgebra (left (I := I) (J := J)).range (left (I := I) (J := J)).range :=
  realUnitaryFlow_mem (partialP (I := I) (J := J)) (fiberAlgebra (left (I := I) (J := J)).range (left (I := I) (J := J)).range) partialP_mem r
lemma qFlow_mem (r : ℝ) : (qFlow (I := I) (J := J) r : Mat (Four I J))∈
    fiberAlgebra (right (I := I) (J := J)).range (right (I := I) (J := J)).range :=
  realUnitaryFlow_mem (partialQ (I := I) (J := J)) (fiberAlgebra (right (I := I) (J := J)).range (right (I := I) (J := J)).range) partialQ_mem r
lemma pFlow_period (r : ℝ) : pFlow (I := I) (J := J) (r+2)=(pFlow (I := I) (J := J)) r :=
  realUnitaryFlow_period_two (partialP (I := I) (J := J)) (matrix_finite_spectrum _) partialP_sq r
lemma qFlow_period (r : ℝ) : qFlow (I := I) (J := J) (r+2)=(qFlow (I := I) (J := J)) r :=
  realUnitaryFlow_period_two (partialQ (I := I) (J := J)) (matrix_finite_spectrum _) partialQ_sq r

end MatrixTensor

end

end OAI
