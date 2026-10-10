import Mathlib
import OAI.Analysis.WeakInfiniteness.RectangularCStar

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

open scoped CStarAlgebra ComplexOrder

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

def rectangularMap (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) : CStarMatrix m n B := M.map φ

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype m] [Fintype n] in
@[simp] lemma rectangularMap_apply (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) (i : m) (j : n) :
    rectangularMap φ M i j = φ (M i j) := rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype m] [Fintype k] in
lemma rectangularMap_mul (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    rectangularMap φ (M*N)=rectangularMap φ M*rectangularMap φ N := by
  ext i j
  simp only [rectangularMap_apply, CStarMatrix.mul_apply, map_sum, map_mul]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype m] [Fintype n] in
lemma rectangularMap_star (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) :
    rectangularMap φ M.conjTranspose=(rectangularMap φ M).conjTranspose := by
  ext i j
  simp only [rectangularMap_apply, CStarMatrix.conjTranspose_apply, map_star]

lemma rectangularMap_norm_le (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) :
    ‖rectangularMap φ M‖ ≤ ‖M‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le (CStarMatrix.mapₙₐ φ) (M.conjTranspose*M)
  change ‖rectangularMap φ (M.conjTranspose*M)‖ ≤ ‖M.conjTranspose*M‖ at h
  rw [rectangularMap_mul, rectangularMap_star, rectangular_norm_initial, rectangular_norm_initial] at h
  nlinarith [norm_nonneg M, norm_nonneg (rectangularMap φ M)]

lemma rectangularMap_norm (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) (M : CStarMatrix m n A) :
    ‖rectangularMap φ M‖ = ‖M‖ := by
  have hi : Function.Injective (CStarMatrix.mapₙₐ (n := n) φ) := by
    intro u v h
    ext i j
    apply hφ
    exact congrArg (fun X : CStarMatrix n n B => X i j) h
  have h := NonUnitalStarAlgHom.norm_map (CStarMatrix.mapₙₐ φ) hi (M.conjTranspose*M)
  change ‖rectangularMap φ (M.conjTranspose*M)‖ = ‖M.conjTranspose*M‖ at h
  rw [rectangularMap_mul, rectangularMap_star, rectangular_norm_initial, rectangular_norm_initial] at h
  nlinarith [norm_nonneg M, norm_nonneg (rectangularMap φ M)]

def matrixScalarRight (M : CStarMatrix m n A) (D : CStarMatrix n k ℂ) : CStarMatrix m k A :=
  fun i j => ∑ l, D l j • M i l

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
@[simp] lemma matrixScalarRight_apply (M : CStarMatrix m n A) (D : CStarMatrix n k ℂ) (i : m) (j : k) :
    matrixScalarRight M D i j = ∑ l, D l j • M i l := rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype m] [Fintype k] in
lemma rectangularMap_scalarRight (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) (D : CStarMatrix n k ℂ) :
    rectangularMap φ (matrixScalarRight M D)=matrixScalarRight (rectangularMap φ M) D := by
  ext i j
  simp only [rectangularMap_apply, matrixScalarRight_apply, map_sum, map_smul]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
lemma matrixScalarRight_inr (M : CStarMatrix m n A) (D : CStarMatrix n k ℂ) :
    rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) (matrixScalarRight M D) =
      rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) M*
        rectangularMap (StarAlgHom.ofId ℂ (Unitization ℂ A)).toNonUnitalStarAlgHom D := by
  apply CStarMatrix.ext
  intro i j
  simp only [rectangularMap_apply, matrixScalarRight_apply, CStarMatrix.mul_apply,
    map_sum, map_smul, StarAlgHom.coe_toNonUnitalStarAlgHom, StarAlgHom.ofId_apply,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

lemma matrixScalarRight_norm_le (M : CStarMatrix m n A) (D : CStarMatrix n k ℂ) :
    ‖matrixScalarRight M D‖ ≤ ‖M‖*‖D‖ := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  let κ := (StarAlgHom.ofId ℂ (Unitization ℂ A)).toNonUnitalStarAlgHom
  have hi : Function.Injective ι := Unitization.inr_injective
  calc
    ‖matrixScalarRight M D‖ = ‖rectangularMap ι (matrixScalarRight M D)‖ := (rectangularMap_norm ι hi _).symm
    _ = ‖rectangularMap ι M*rectangularMap κ D‖ := by rw [matrixScalarRight_inr]
    _ ≤ ‖rectangularMap ι M‖*‖rectangularMap κ D‖ := rectangular_norm_mul_le _ _
    _ ≤ ‖M‖*‖D‖ := by rw [rectangularMap_norm ι hi]; gcongr; exact rectangularMap_norm_le κ D

omit [PartialOrder A] [StarOrderedRing A] [Fintype k] in
lemma matrixScalarRight_mul_left (X : CStarMatrix m m A) (M : CStarMatrix m n A)
    (D : CStarMatrix n k ℂ) : X*matrixScalarRight M D=matrixScalarRight (X*M) D := by
  ext i j
  simp only [CStarMatrix.mul_apply, matrixScalarRight_apply, Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  rw [Finset.sum_comm]

end

end WeakPureInfiniteness
end

end OAI
