import Mathlib
import OAI.Analysis.Commutator.MatrixUnits

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.MatrixTensor

open Matrix

variable {A I J : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hc : ∀ x y,Commute (φ x) (ψ y))

omit [StarModule ℂ A] in
include hc in
lemma units_mul (i j k l : I×J) :
    (φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))*(φ (single k.1 l.1 1)*ψ (single k.2 l.2 1))=
      if j=k then φ (single i.1 l.1 1)*ψ (single i.2 l.2 1) else 0 := by
  have he : (φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))*(φ (single k.1 l.1 1)*ψ (single k.2 l.2 1))=
      (φ (single i.1 j.1 1)*φ (single k.1 l.1 1))*(ψ (single i.2 j.2 1)*ψ (single k.2 l.2 1)) := by
    simp only [mul_assoc]
    rw [←mul_assoc (ψ (single i.2 j.2 1)),(hc (single k.1 l.1 1) (single i.2 j.2 1)).eq.symm]
    simp only [mul_assoc]
  rw [he,←map_mul,←map_mul]
  by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2
  · have hjk : j=k := Prod.ext h1 h2
    subst k
    simp only [single_mul_single_same,one_mul,ite_true]
  · have hjk : j≠k := fun h => h2 (congrArg Prod.snd h)
    rw [single_mul_single_of_ne 1 i.2 j.2 k.2 h2 1,map_zero,mul_zero,ite_eq_right hjk]
  · have hjk : j≠k := fun h => h1 (congrArg Prod.fst h)
    rw [single_mul_single_of_ne 1 i.1 j.1 k.1 h1 1,map_zero,zero_mul,ite_eq_right hjk]
  · have hjk : j≠k := fun h => h1 (congrArg Prod.fst h)
    rw [single_mul_single_of_ne 1 i.1 j.1 k.1 h1 1,map_zero,zero_mul,ite_eq_right hjk]

omit [StarModule ℂ A] in
include hc in
lemma units_star (i j : I×J) :
    star (φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))=
      φ (single j.1 i.1 1)*ψ (single j.2 i.2 1) := by
  simp only [star_mul,←map_star,Matrix.star_eq_conjTranspose,conjTranspose_single,star_one]
  exact (hc _ _).eq.symm

omit [StarModule ℂ A] in
lemma units_one : (∑ i : I×J,φ (single i.1 i.1 1)*ψ (single i.2 i.2 1))=1 := by
  rw [Fintype.sum_prod_type]
  simp only [←Finset.mul_sum,←map_sum,sum_single_one,map_one,mul_one]

def representation : Matrix (I×J) (I×J) ℂ →⋆ₐ[ℂ] A :=
  MatrixUnits.representation (fun i j => φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))
    (units_mul φ ψ hc) (units_star φ ψ hc) (units_one φ ψ)

@[simp] lemma representation_single (i j : I×J) :
    representation φ ψ hc (single i j 1)=φ (single i.1 j.1 1)*ψ (single i.2 j.2 1) := by
  simp [representation,MatrixUnits.representation,Matrix.single_apply,ite_and]

lemma left_mem (x : Matrix I I ℂ) : φ x∈(representation φ ψ hc).range := by
  have hu (i j : I) : φ (single i j 1)∈(representation φ ψ hc).range := by
    have he : φ (single i j 1)=∑ k : J,representation φ ψ hc (single (i,k) (j,k) 1) := by
      simp only [representation_single,←Finset.mul_sum,←map_sum,sum_single_one,map_one,mul_one]
    rw [he]
    exact (representation φ ψ hc).range.sum_mem (fun k _ => ⟨single (i,k) (j,k) 1,rfl⟩)
  rw [Matrix.matrix_eq_sum_single x,map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro i hi
  rw [map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro j hj
  have he : single i j (x i j)=x i j • single i j 1 := by simp
  rw [he,map_smul]
  exact (representation φ ψ hc).range.smul_mem (hu i j) _

lemma right_mem (x : Matrix J J ℂ) : ψ x∈(representation φ ψ hc).range := by
  have hu (i j : J) : ψ (single i j 1)∈(representation φ ψ hc).range := by
    have he : ψ (single i j 1)=∑ k : I,representation φ ψ hc (single (k,i) (k,j) 1) := by
      simp only [representation_single,←Finset.sum_mul,←map_sum,sum_single_one,map_one,one_mul]
    rw [he]
    exact (representation φ ψ hc).range.sum_mem (fun k _ => ⟨single (k,i) (k,j) 1,rfl⟩)
  rw [Matrix.matrix_eq_sum_single x,map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro i hi
  rw [map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro j hj
  have he : single i j (x i j)=x i j • single i j 1 := by simp
  rw [he,map_smul]
  exact (representation φ ψ hc).range.smul_mem (hu i j) _

end Kadison.MatrixTensor

end

end
end

end OAI
