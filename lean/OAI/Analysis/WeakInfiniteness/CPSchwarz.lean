import Mathlib
import OAI.Analysis.WeakInfiniteness.CentralCuntzWords
import OAI.Analysis.WeakInfiniteness.NuclearCP

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

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



open scoped CStarAlgebra ComplexOrder

universe u v

section Star

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma completelyPositive_map_nonneg {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ)
    {a : A} (ha : 0≤a) : 0≤φ a := by
  exact map_nonneg hφ.toMap ha

lemma completelyPositive_map_star {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ)
    (a : A) : φ (star a)=star (φ a) := by
  obtain ⟨x,hx,_,rfl⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hxstar (i : Fin 4) : star (x i)=x i := (IsSelfAdjoint.of_nonneg (hx i)).star_eq
  have hy (i : Fin 4) : star (φ (x i))=φ (x i) :=
    (IsSelfAdjoint.of_nonneg (completelyPositive_map_nonneg hφ (hx i))).star_eq
  simp only [star_sum,star_smul,map_sum,map_smul,hxstar,hy]

end Star

section Diagonal

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance schwarzMatrixRealModule {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n B) := Module.complexToReal _

lemma cstarMatrix_diagonal_nonneg {n : Type*} [Fintype n]
    (M : CStarMatrix n n B) (hM : 0≤M) (i : n) : 0≤M i i := by
  let X := CFC.sqrt M
  have he : star X*X=M := by
    rw [show star X=X from (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq]
    exact CFC.sqrt_mul_sqrt_self M hM
  rw [← he,CStarMatrix.mul_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg (X j i)

end Diagonal


variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma completelyPositive_one_le_one {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ)
    (hφn : ‖φ‖≤1) : φ 1≤1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (completelyPositive_map_nonneg hφ zero_le_one)).mp
  exact (φ.le_opNorm 1).trans ((mul_le_mul hφn cstar_norm_one_le_one
    (norm_nonneg _) zero_le_one).trans (by norm_num))

lemma completelyPositive_schwarz {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ)
    (hφn : ‖φ‖≤1) (a : A) : star (φ a)*φ a≤φ (star a*a) := by
  let R : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![a,1;0,0]
  let M := matrixLinearMap φ (star R*R)
  have hM : 0≤M := matrixLinearMap_nonneg hφ (star_mul_self_nonneg R)
  let V : CStarMatrix (Fin 2) (Fin 2) B := CStarMatrix.ofMatrix !![1,0;-φ a,0]
  have hN := cstarMatrix_diagonal_nonneg (star V*M*V) (star_left_conjugate_nonneg hM V) 0
  have he : (star V*M*V) 0 0=
      φ (star a*a)-star (φ a)*φ a-star (φ a)*φ a+star (φ a)*φ 1*φ a := by
    simp [V,M,R,CStarMatrix.mul_apply,CStarMatrix.star_apply,Fin.sum_univ_two,
      completelyPositive_map_star hφ]
    noncomm_ring
  rw [he] at hN
  have hp := star_left_conjugate_nonneg (sub_nonneg.mpr (completelyPositive_one_le_one hφ hφn)) (φ a)
  apply sub_nonneg.mp
  have h := add_nonneg hN hp
  convert h using 1; noncomm_ring




end WeakPureInfiniteness

end

end OAI
