import Mathlib
import OAI.Analysis.WeakInfiniteness.MatrixTensorExact
import OAI.Analysis.WeakInfiniteness.NonunitalSchwarz

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

variable {A : Type u} [NonUnitalCStarAlgebra A]

variable {n : Type*} [Fintype n] [DecidableEq n]

def nonunitalCoefficientMap (v : n → A) : CStarMatrix n n ℂ →ₗ[ℂ] A :=
  ∑ i,∑ j,(matrixEntryLinear i j).smulRight (star (v i)*v j)

omit [DecidableEq n] in
lemma nonunitalCoefficientMap_apply (v : n → A) (M : CStarMatrix n n ℂ) :
    nonunitalCoefficientMap v M=∑ i,∑ j,M i j • (star (v i)*v j) := by
  simp only [nonunitalCoefficientMap, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rfl

def nonunitalCoefficientAction (M : CStarMatrix n n ℂ) (v : n → A) (i : n) : A :=
  ∑ j,M i j • v j

lemma nonunitalCoefficientMap_initial (v : n → A) :
    nonunitalCoefficientMap v 1=∑ i,star (v i)*v i := by
  rw [nonunitalCoefficientMap_apply]
  simp [CStarMatrix.one_apply]

omit [DecidableEq n] in
lemma nonunitalCoefficientMap_mixed (v : n → A) (M : CStarMatrix n n ℂ) :
    nonunitalCoefficientMap v M=∑ i,star (v i)*nonunitalCoefficientAction M v i := by
  simp only [nonunitalCoefficientMap_apply,nonunitalCoefficientAction,Finset.mul_sum,mul_smul_comm]

omit [DecidableEq n] in
lemma nonunitalCoefficientMap_square (v : n → A) (M : CStarMatrix n n ℂ) :
    nonunitalCoefficientMap v (star M*M)=
      ∑ i,star (nonunitalCoefficientAction M v i)*nonunitalCoefficientAction M v i := by
  simp only [nonunitalCoefficientMap_apply,CStarMatrix.mul_apply,CStarMatrix.star_apply,
    Finset.sum_smul,nonunitalCoefficientAction,star_sum,Finset.sum_mul,Finset.mul_sum,
    star_smul,smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul, mul_comm (M _ _)]
  calc
    (∑ i,∑ j,∑ k,(star (M k i)*M k j) • (star (v i)*v j)) =
        ∑ i,∑ k,∑ j,(star (M k i)*M k j) • (star (v i)*v j) := by
      congr 1; ext i; rw [Finset.sum_comm]
    _ = ∑ k,∑ i,∑ j,(star (M k i)*M k j) • (star (v i)*v j) := Finset.sum_comm
    _ = _ := by congr 1; ext k; rw [Finset.sum_comm]

lemma nonunitalCoefficient_defect_identity (v : n → A) (M : CStarMatrix n n ℂ) (a : A) :
    (∑ i,star (nonunitalCoefficientAction M v i-v i*a)*(nonunitalCoefficientAction M v i-v i*a)) =
      nonunitalCoefficientMap v (star M*M)-star (nonunitalCoefficientMap v M)*a-
        star a*nonunitalCoefficientMap v M+star a*nonunitalCoefficientMap v 1*a := by
  have he (i : n) :
      star (nonunitalCoefficientAction M v i-v i*a)*(nonunitalCoefficientAction M v i-v i*a)=
        star (nonunitalCoefficientAction M v i)*nonunitalCoefficientAction M v i-
        (star (nonunitalCoefficientAction M v i)*v i)*a-
        star a*(star (v i)*nonunitalCoefficientAction M v i)+
        star a*(star (v i)*v i)*a := by
    simp only [star_sub,star_mul]
    noncomm_ring
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,← Finset.mul_sum]
  rw [nonunitalCoefficientMap_square,nonunitalCoefficientMap_initial,nonunitalCoefficientMap_mixed]
  simp only [star_sum,star_mul,star_star]

end CoefficientMap

section Positivity

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance nonunitalCoefficientMatrixRealModule : Module ℝ (CStarMatrix n n ℂ) :=
  Module.complexToReal _

lemma nonunitalCoefficientMap_nonneg (v : n → A)
    (M : CStarMatrix n n ℂ) (hM : 0≤M) : 0 ≤ nonunitalCoefficientMap v M := by
  let X := CFC.sqrt M
  have hX : star X*X=M := by
    rw [show star X=X from (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq]
    exact CFC.sqrt_mul_sqrt_self M hM
  rw [← hX,nonunitalCoefficientMap_square]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

lemma nonunitalCoefficientMap_mono (v : n → A) : Monotone (nonunitalCoefficientMap v) := by
  intro M N hMN
  have h := nonunitalCoefficientMap_nonneg v (N-M) (sub_nonneg.mpr hMN)
  simpa only [map_sub,sub_nonneg] using h

omit [Fintype n] [DecidableEq n] in
lemma nonunital_contraction_conjugate_le_self (p a : A) (hp : 0≤p) (hpn : ‖p‖≤1) :
    star a*p*a ≤ star a*a := by
  have hpU : 0≤(p:Unitization ℂ A) := Unitization.inr_nonneg_iff.mpr hp
  have hp1 : (p:Unitization ℂ A)≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpU).mp (by
      simpa only [Unitization.norm_inr] using hpn)
  have h := star_left_conjugate_nonneg (sub_nonneg.mpr hp1) (a:Unitization ℂ A)
  apply sub_nonneg.mp
  apply Unitization.inr_nonneg_iff.mp
  convert h using 1
  simp only [Unitization.inr_sub,Unitization.inr_mul,Unitization.inr_star]
  noncomm_ring

lemma nonunitalCoefficient_defect_le (v : n → A)
    (φ : A →L[ℂ] CStarMatrix n n ℂ) (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1)
    (hv : ‖nonunitalCoefficientMap v 1‖≤1) (a : A) :
    (∑ i,star (nonunitalCoefficientAction (φ a) v i-v i*a)*
      (nonunitalCoefficientAction (φ a) v i-v i*a)) ≤
      nonunitalCoefficientMap v (φ (star a*a))-star a*a+
        star a*(a-nonunitalCoefficientMap v (φ a))+
        star (a-nonunitalCoefficientMap v (φ a))*a := by
  have h1 := sub_nonneg.mpr (nonunitalCoefficientMap_mono v (completelyPositive_schwarz_nonunital_domain hφ hφn a))
  have h2 := sub_nonneg.mpr (nonunital_contraction_conjugate_le_self
    (nonunitalCoefficientMap v 1) a (nonunitalCoefficientMap_nonneg v 1 zero_le_one) hv)
  apply sub_nonneg.mp
  rw [nonunitalCoefficient_defect_identity]
  have h := add_nonneg h1 h2
  convert h using 1
  simp only [star_sub]
  noncomm_ring

lemma nonunitalCoefficient_defect_norm_le (v : n → A)
    (φ : A →L[ℂ] CStarMatrix n n ℂ) (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1)
    (hv : ‖nonunitalCoefficientMap v 1‖≤1) (a : A) :
    ‖∑ i,star (nonunitalCoefficientAction (φ a) v i-v i*a)*
      (nonunitalCoefficientAction (φ a) v i-v i*a)‖ ≤
      ‖nonunitalCoefficientMap v (φ (star a*a))-star a*a‖+
        2*‖a‖*‖nonunitalCoefficientMap v (φ a)-a‖ := by
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (nonunitalCoefficient_defect_le v φ hφ hφn hv a)
    (Finset.sum_nonneg fun i _ => star_mul_self_nonneg _)
  refine h.trans ?_
  calc
    _ ≤ (‖nonunitalCoefficientMap v (φ (star a*a))-star a*a‖+
        ‖star a*(a-nonunitalCoefficientMap v (φ a))‖)+
        ‖star (a-nonunitalCoefficientMap v (φ a))*a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖nonunitalCoefficientMap v (φ (star a*a))-star a*a‖+
        ‖a‖*‖a-nonunitalCoefficientMap v (φ a)‖)+
        ‖a-nonunitalCoefficientMap v (φ a)‖*‖a‖ := by
      gcongr
      · simpa only [norm_star] using norm_mul_le (star a) (a-nonunitalCoefficientMap v (φ a))
      · simpa only [norm_star] using norm_mul_le (star (a-nonunitalCoefficientMap v (φ a))) a
    _ = _ := by rw [norm_sub_rev a]; ring

end Positivity

end

end WeakPureInfiniteness
end

end OAI
