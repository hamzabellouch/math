import Mathlib
import OAI.Analysis.WeakInfiniteness.CPSchwarz
import OAI.Analysis.WeakInfiniteness.MatrixTensorExact

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

universe u

section CoefficientMap

variable {A : Type u} [CStarAlgebra A]

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixCoefficientMap (v : n → A) : CStarMatrix n n ℂ →ₗ[ℂ] A :=
  ∑ i,∑ j,(matrixEntryLinear i j).smulRight (star (v i)*v j)

omit [DecidableEq n] in
lemma matrixCoefficientMap_apply (v : n → A) (M : CStarMatrix n n ℂ) :
    matrixCoefficientMap v M=∑ i,∑ j,M i j • (star (v i)*v j) := by
  simp only [matrixCoefficientMap, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rfl

def matrixCoefficientAction (M : CStarMatrix n n ℂ) (v : n → A) (i : n) : A :=
  ∑ j,M i j • v j

lemma matrixCoefficientMap_initial (v : n → A) :
    matrixCoefficientMap v 1=∑ i,star (v i)*v i := by
  rw [matrixCoefficientMap_apply]
  simp [CStarMatrix.one_apply]

omit [DecidableEq n] in
lemma matrixCoefficientMap_mixed (v : n → A) (M : CStarMatrix n n ℂ) :
    matrixCoefficientMap v M=∑ i,star (v i)*matrixCoefficientAction M v i := by
  simp only [matrixCoefficientMap_apply,matrixCoefficientAction,Finset.mul_sum,mul_smul_comm]

omit [DecidableEq n] in
lemma matrixCoefficientMap_square (v : n → A) (M : CStarMatrix n n ℂ) :
    matrixCoefficientMap v (star M*M)=
      ∑ i,star (matrixCoefficientAction M v i)*matrixCoefficientAction M v i := by
  simp only [matrixCoefficientMap_apply,CStarMatrix.mul_apply,CStarMatrix.star_apply,
    Finset.sum_smul,matrixCoefficientAction,star_sum,Finset.sum_mul,Finset.mul_sum,
    star_smul,smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul, mul_comm (M _ _)]
  calc
    (∑ i,∑ j,∑ k,(star (M k i)*M k j) • (star (v i)*v j)) =
        ∑ i,∑ k,∑ j,(star (M k i)*M k j) • (star (v i)*v j) := by
      congr 1; ext i; rw [Finset.sum_comm]
    _ = ∑ k,∑ i,∑ j,(star (M k i)*M k j) • (star (v i)*v j) := Finset.sum_comm
    _ = _ := by congr 1; ext k; rw [Finset.sum_comm]

lemma matrixCoefficient_defect_identity (v : n → A) (M : CStarMatrix n n ℂ) (a : A) :
    (∑ i,star (matrixCoefficientAction M v i-v i*a)*(matrixCoefficientAction M v i-v i*a)) =
      matrixCoefficientMap v (star M*M)-star (matrixCoefficientMap v M)*a-
        star a*matrixCoefficientMap v M+star a*matrixCoefficientMap v 1*a := by
  have he (i : n) :
      star (matrixCoefficientAction M v i-v i*a)*(matrixCoefficientAction M v i-v i*a)=
        star (matrixCoefficientAction M v i)*matrixCoefficientAction M v i-
        (star (matrixCoefficientAction M v i)*v i)*a-
        star a*(star (v i)*matrixCoefficientAction M v i)+
        star a*(star (v i)*v i)*a := by
    simp only [star_sub,star_mul]
    noncomm_ring
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,← Finset.mul_sum]
  rw [matrixCoefficientMap_square,matrixCoefficientMap_initial,matrixCoefficientMap_mixed]
  simp only [star_sum,star_mul,star_star]

end CoefficientMap

section Positivity

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma matrixCoefficientMap_nonneg (v : n → A) (k : n)
    (M : CStarMatrix n n ℂ) (hM : 0≤M) : 0 ≤ matrixCoefficientMap v M := by
  let ι : CStarMatrix n n ℂ →⋆ₙₐ[ℂ] CStarMatrix n n A :=
    CStarMatrix.mapₙₐ (StarAlgHom.ofId ℂ A).toNonUnitalStarAlgHom
  let V : CStarMatrix n n A := CStarMatrix.ofMatrix (fun i j => if j=k then v i else 0)
  have h := cstarMatrix_diagonal_nonneg (star V*ι M*V)
    (star_left_conjugate_nonneg (map_nonneg ι hM) V) k
  have he : (star V*ι M*V) k k=matrixCoefficientMap v M := by
    change (∑ j, (∑ i, star (if k=k then v i else 0) *
      (StarAlgHom.ofId ℂ A) (M i j)) * (if k=k then v j else 0)) = _
    simp only [ite_true, Finset.sum_mul]
    rw [matrixCoefficientMap_apply]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    rw [StarAlgHom.ofId_apply, Algebra.algebraMap_eq_smul_one]
    simp only [mul_smul_comm,mul_one,smul_mul_assoc]
  rwa [he] at h

lemma matrixCoefficientMap_mono (v : n → A) (k : n) : Monotone (matrixCoefficientMap v) := by
  intro M N hMN
  have h := matrixCoefficientMap_nonneg v k (N-M) (sub_nonneg.mpr hMN)
  simpa only [map_sub,sub_nonneg] using h

lemma matrixCoefficient_defect_le (v : n → A) (k : n)
    (φ : A →L[ℂ] CStarMatrix n n ℂ) (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1)
    (hv : matrixCoefficientMap v 1≤1) (a : A) :
    (∑ i,star (matrixCoefficientAction (φ a) v i-v i*a)*
      (matrixCoefficientAction (φ a) v i-v i*a)) ≤
      matrixCoefficientMap v (φ (star a*a))-star a*a+
        star a*(a-matrixCoefficientMap v (φ a))+
        star (a-matrixCoefficientMap v (φ a))*a := by
  have h1 := sub_nonneg.mpr (matrixCoefficientMap_mono v k (completelyPositive_schwarz hφ hφn a))
  have h2 := star_left_conjugate_nonneg (sub_nonneg.mpr hv) a
  apply sub_nonneg.mp
  rw [matrixCoefficient_defect_identity]
  have h := add_nonneg h1 h2
  convert h using 1
  simp only [star_sub]
  noncomm_ring

lemma matrixCoefficient_defect_norm_le (v : n → A) (k : n)
    (φ : A →L[ℂ] CStarMatrix n n ℂ) (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1)
    (hv : matrixCoefficientMap v 1≤1) (a : A) :
    ‖∑ i,star (matrixCoefficientAction (φ a) v i-v i*a)*
      (matrixCoefficientAction (φ a) v i-v i*a)‖ ≤
      ‖matrixCoefficientMap v (φ (star a*a))-star a*a‖+
        2*‖a‖*‖matrixCoefficientMap v (φ a)-a‖ := by
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (matrixCoefficient_defect_le v k φ hφ hφn hv a)
    (Finset.sum_nonneg fun i _ => star_mul_self_nonneg _)
  refine h.trans ?_
  calc
    _ ≤ (‖matrixCoefficientMap v (φ (star a*a))-star a*a‖+
        ‖star a*(a-matrixCoefficientMap v (φ a))‖)+
        ‖star (a-matrixCoefficientMap v (φ a))*a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖matrixCoefficientMap v (φ (star a*a))-star a*a‖+
        ‖a‖*‖a-matrixCoefficientMap v (φ a)‖)+
        ‖a-matrixCoefficientMap v (φ a)‖*‖a‖ := by
      gcongr
      · simpa only [norm_star] using norm_mul_le (star a) (a-matrixCoefficientMap v (φ a))
      · simpa only [norm_star] using norm_mul_le (star (a-matrixCoefficientMap v (φ a))) a
    _ = _ := by rw [norm_sub_rev a]; ring

end Positivity

end

end WeakPureInfiniteness
end

end OAI
