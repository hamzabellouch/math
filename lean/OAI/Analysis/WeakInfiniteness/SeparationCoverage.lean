import Mathlib
import OAI.Analysis.WeakInfiniteness.PolarCFC

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

def separationJ (l s : ℝ) : ℝ := Real.sqrt (separationFloor l s)/Real.sqrt l

lemma continuous_separationJ (l : ℝ) : Continuous (separationJ l) :=
  (Real.continuous_sqrt.comp (continuous_separationFloor l)).div_const _

lemma separationRJ {l : ℝ} (hl : 0 < l) (s : ℝ) : separationR l s*separationJ l s=1 := by
  unfold separationR separationJ
  have h1 : Real.sqrt l ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hl)
  have h2 : Real.sqrt (separationFloor l s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (separationFloor_pos hl s))
  field_simp

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma separation_second_coverage_identity (b X : B) {l : ℝ} (hl : 0 < l) :
    (b*cfc (separationR l) (star X*X))*cfc (separationN l) (star X*X)*
      cfc (separationJ l) (star X*X)=b*cfc (separationN l) (star X*X) := by
  have he : (b*cfc (separationR l) (star X*X))*cfc (separationN l) (star X*X)*
      cfc (separationJ l) (star X*X)=
      b*(cfc (separationR l) (star X*X)*cfc (separationN l) (star X*X)*cfc (separationJ l) (star X*X)) := by
    simp only [mul_assoc]
  rw [he,cfc_real_mul_three _ (IsSelfAdjoint.star_mul_self X) _ _ _
    (continuous_separationR hl) (continuous_separationN l) (continuous_separationJ l)]
  congr 1
  apply cfc_congr
  intro s _
  calc
    _=(separationR l s*separationJ l s)*separationN l s := by ring
    _=_ := by rw [separationRJ hl,one_mul]

lemma norm_separationJ (X : B) (hX : ‖X‖ ≤ 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    ‖cfc (separationJ l) (star X*X)‖ ≤ (Real.sqrt l)⁻¹ := by
  nontriviality B
  apply norm_cfc_le (by positivity)
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  have hs1 : s ≤ 1 := by
    have hn : s ≤ ‖star X*X‖ := by
      have h := spectrum.norm_le_norm_of_mem hs
      simpa only [Real.norm_eq_abs,abs_of_nonneg hs0] using h
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg X]
  have hfloor : separationFloor l s ≤ 1 := by
    apply max_le hl1
    nlinarith [Real.sq_sqrt hs0,Real.sqrt_nonneg s]
  have hroot : Real.sqrt (separationFloor l s) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hfloor
    simpa using h
  rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp only [separationJ]; positivity),separationJ,div_eq_mul_inv]
  calc
    _≤1*(Real.sqrt l)⁻¹ := mul_le_mul_of_nonneg_right hroot (by positivity)
    _=_ := one_mul _

omit [PartialOrder B] [StarOrderedRing B] in
lemma norm_separationN_le_one (X : B) (l : ℝ) :
    ‖cfc (separationN l) (star X*X)‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro s _
  change ‖spectralRamp (4*l) (Real.sqrt s)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg _ _)]
  exact spectralRamp_le_one _ _

lemma separationN_eq_zero_of_norm_le (X : B) {l : ℝ} (hl : 0 < l) (hX : ‖X‖ ≤ 4*l) :
    cfc (separationN l) (star X*X)=0 := by
  nontriviality B
  rw [← cfc_zero ℝ (star X*X)]
  apply cfc_congr
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  have hn : s ≤ ‖X‖^2 := by
    have h := spectrum.norm_le_norm_of_mem hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg hs0,CStarRing.norm_star_mul_self,pow_two] using h
  exact spectralRamp_eq_zero (by positivity) (by nlinarith [Real.sq_sqrt hs0,Real.sqrt_nonneg s,norm_nonneg X])

end

end

end WeakPureInfiniteness
end

end OAI
