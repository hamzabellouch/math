import Mathlib
import OAI.Analysis.Commutator.MatrixFlatten

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.MatrixScalar

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {ι : Type*} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

def scalarHom : ℂ →⋆ₐ[ℂ] A where
  __ := Algebra.ofId ℂ A
  map_star' c := by simp [Algebra.algebraMap_eq_smul_one]

def amplify (φ : A →⋆ₐ[ℂ] B) : CStarMatrix ι ι A →⋆ₐ[ℂ] CStarMatrix ι ι B where
  __ := CStarMatrix.mapₙₐ φ.toNonUnitalStarAlgHom
  map_one' := by
    ext i j
    change φ (if i=j then 1 else 0)=(if i=j then 1 else 0)
    by_cases h : i=j <;> simp [h]
  commutes' c := by
    ext i j
    change φ (if i=j then algebraMap ℂ A c else 0)=(if i=j then algebraMap ℂ B c else 0)
    by_cases h : i=j <;> simp [h,Algebra.algebraMap_eq_smul_one]

@[simp] lemma amplify_apply (φ : A →⋆ₐ[ℂ] B) (X : CStarMatrix ι ι A) (i j : ι) :
    amplify φ X i j=φ (X i j) := rfl

def scalarMatrix : CStarMatrix ι ι ℂ →⋆ₐ[ℂ] CStarMatrix ι ι A := amplify scalarHom

@[simp] lemma scalarMatrix_apply (X : CStarMatrix ι ι ℂ) (i j : ι) :
    scalarMatrix (A:=A) X i j=algebraMap ℂ A (X i j) := rfl

lemma scalarMatrix_injective [Nontrivial A] : Function.Injective (scalarMatrix (ι:=ι) (A:=A)) := by
  intro X Y h
  ext i j
  apply (algebraMap ℂ A).injective
  exact congrArg (fun Z : CStarMatrix ι ι A => Z i j) h

lemma map_scalar_left (f : A →ₗ[ℂ] B) (p : CStarMatrix ι ι ℂ) (X : CStarMatrix ι ι A) :
    CStarMatrix.mapₗ f (scalarMatrix p*X)=scalarMatrix p*CStarMatrix.mapₗ f X := by
  ext i j
  change f (∑ k,algebraMap ℂ A (p i k)*X k j)=∑ k,algebraMap ℂ B (p i k)*f (X k j)
  simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,map_sum,map_smul]

lemma map_scalar_right (f : A →ₗ[ℂ] B) (p : CStarMatrix ι ι ℂ) (X : CStarMatrix ι ι A) :
    CStarMatrix.mapₗ f (X*scalarMatrix p)=CStarMatrix.mapₗ f X*scalarMatrix p := by
  ext i j
  change f (∑ k,X i k*algebraMap ℂ A (p k j))=∑ k,f (X i k)*algebraMap ℂ B (p k j)
  simp only [Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,map_sum,map_smul]

lemma map_scalar_bimodule (f : A →ₗ[ℂ] B) (p q : CStarMatrix ι ι ℂ) (X : CStarMatrix ι ι A) :
    CStarMatrix.mapₗ f (scalarMatrix p*X*scalarMatrix q)=
      scalarMatrix p*CStarMatrix.mapₗ f X*scalarMatrix q := by
  rw [map_scalar_right,map_scalar_left]

end Kadison.MatrixScalar

namespace Kadison.MatrixGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance : DecidableEq ι := Classical.decEq ι

local instance : DecidableEq κ := Classical.decEq κ

local instance : DecidableEq (κ×ι) := Classical.decEq (κ×ι)

local instance : DecidableEq (ι×κ) := Classical.decEq (ι×κ)

omit [PartialOrder A] [StarOrderedRing A] in
lemma flatten_symm_apply (X : CStarMatrix (κ×ι) (κ×ι) A) (i j : κ) (k l : ι) :
    (flatten ι κ).symm X i j k l=X (i,k) (j,l) := by
  exact congrArg (fun Z : CStarMatrix (κ×ι) (κ×ι) A => Z (i,k) (j,l))
    ((flatten ι κ).apply_symm_apply X)

def shuffle : CStarMatrix ι ι (CStarMatrix κ κ A) ≃⋆ₐ[ℂ] CStarMatrix κ κ (CStarMatrix ι ι A) :=
  ((flatten κ ι).trans (CStarMatrix.reindexₐ ℂ A (Equiv.prodComm ι κ))).trans (flatten ι κ).symm

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma shuffle_apply (X : CStarMatrix ι ι (CStarMatrix κ κ A)) (i j : κ) (k l : ι) :
    shuffle ι κ X i j k l=X k l i j := by
  simp only [shuffle,StarAlgEquiv.trans_apply,flatten_symm_apply]
  rfl

end Kadison.MatrixGNS

end

end
end

end OAI
