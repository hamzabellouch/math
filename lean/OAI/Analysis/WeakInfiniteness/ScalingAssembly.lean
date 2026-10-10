import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzComparison

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

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma stronglyPurelyInfinite_of_contractive
    (hc : ∀ a b : A,0 ≤ a → 0 ≤ b → ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ∀ ε : ℝ,0 < ε → ∃ s t : A, ‖star s*(a*a)*s-a*a‖ < ε ∧
        ‖star t*(b*b)*t-b*b‖ < ε ∧ ‖star s*a*b*t‖ < ε) :
    StronglyPurelyInfinite A := by
  intro a b ha hb ε hε
  let M := max 1 (max ‖a‖ ‖b‖)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hMa : ‖a‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMb : ‖b‖ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  let a' := M⁻¹ • a
  let b' := M⁻¹ • b
  have ha' : 0 ≤ a' := smul_nonneg (inv_nonneg.mpr hM.le) ha
  have hb' : 0 ≤ b' := smul_nonneg (inv_nonneg.mpr hM.le) hb
  have han : ‖a'‖ ≤ 1 := by
    rw [show a'=M⁻¹ • a from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hM),inv_mul_eq_div]
    exact (div_le_one₀ hM).mpr hMa
  have hbn : ‖b'‖ ≤ 1 := by
    rw [show b'=M⁻¹ • b from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hM),inv_mul_eq_div]
    exact (div_le_one₀ hM).mpr hMb
  obtain ⟨s,t,hs,ht,hst⟩ := hc a' b' ha' hb' han hbn (ε/M^2) (by positivity)
  have he (x y : A) : M^2 • ((M⁻¹ • x)*(M⁻¹ • y))=x*y := by
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,smul_smul]
    have : M^2*M⁻¹*M⁻¹=1 := by field_simp
    rw [this,one_smul]
  have hes : M^2 • (star s*(a'*a')*s-a'*a')=star s*(a*a)*s-a*a := by
    calc
      _=star s*(M^2 • (a'*a'))*s-M^2 • (a'*a') := by
        simp only [smul_sub,smul_mul_assoc,mul_smul_comm]
      _=_ := by rw [he]
  have het : M^2 • (star t*(b'*b')*t-b'*b')=star t*(b*b)*t-b*b := by
    calc
      _=star t*(M^2 • (b'*b'))*t-M^2 • (b'*b') := by
        simp only [smul_sub,smul_mul_assoc,mul_smul_comm]
      _=_ := by rw [he]
  have hest : M^2 • (star s*a'*b'*t)=star s*a*b*t := by
    calc
      _=star s*(M^2 • (a'*b'))*t := by simp only [smul_mul_assoc,mul_smul_comm,mul_assoc]
      _=_ := by rw [he]; simp only [mul_assoc]
  refine ⟨s,t,?_,?_,?_⟩
  · rw [← hes,norm_smul,Real.norm_eq_abs,abs_of_pos (sq_pos_of_pos hM)]
    exact (mul_lt_mul_of_pos_left hs (sq_pos_of_pos hM)).trans_le (by field_simp; rfl)
  · rw [← het,norm_smul,Real.norm_eq_abs,abs_of_pos (sq_pos_of_pos hM)]
    exact (mul_lt_mul_of_pos_left ht (sq_pos_of_pos hM)).trans_le (by field_simp; rfl)
  · rw [← hest,norm_smul,Real.norm_eq_abs,abs_of_pos (sq_pos_of_pos hM)]
    exact (mul_lt_mul_of_pos_left hst (sq_pos_of_pos hM)).trans_le (by field_simp; rfl)

end

end WeakPureInfiniteness
end

end OAI
