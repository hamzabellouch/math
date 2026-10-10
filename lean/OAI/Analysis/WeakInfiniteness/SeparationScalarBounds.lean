import Mathlib
import OAI.Analysis.WeakInfiniteness.SeparationScalar

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

lemma separationK_sq {l : ℝ} (hl : 0 < l) (s : ℝ) :
    (separationK l s)^2=(l*separationFloor l s)⁻¹ := by
  rw [separationK,inv_pow,mul_pow,Real.sq_sqrt hl.le,Real.sq_sqrt (separationFloor_pos hl s).le]

lemma separation_low_square_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*(separationL l s)^4 ≤ 64*l^2 := by
  by_cases h : 8*l ≤ Real.sqrt s
  · rw [separation_low_support hl h]; nlinarith [sq_nonneg l]
  · have hsqrt : Real.sqrt s ≤ 8*l := (lt_of_not_ge h).le
    have hL := separationL_bounds l s
    have hL2 : (separationL l s)^2 ≤ 1 := by nlinarith
    have hL4 : (separationL l s)^4 ≤ 1 := by nlinarith [sq_nonneg ((separationL l s)^2)]
    have hs' : s ≤ 64*l^2 := by nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s]
    nlinarith

lemma separation_mixed_R_square_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*(separationR l s)^2*(separationL l s)^2 ≤ 9*l^2 := by
  by_cases h : 8*l ≤ Real.sqrt s
  · rw [separation_low_support hl h]; nlinarith [sq_nonneg l]
  · have hu : Real.sqrt s ≤ 8*l := (lt_of_not_ge h).le
    have hm := separationFloor_pos hl s
    have hu0 := Real.sqrt_nonneg s
    have hum := separation_floor_ge_sqrt l s
    have hsq : s ≤ Real.sqrt s*separationFloor l s := by
      nlinarith [Real.sq_sqrt hs,mul_nonneg hu0 (sub_nonneg.mpr hum)]
    have hbase : s*(separationR l s)^2 ≤ 8*l^2 := by
      rw [separationR_sq hl,← mul_div_assoc]
      apply (div_le_iff₀ hm).mpr
      have hmul := mul_le_mul_of_nonneg_right hsq hl.le
      have hmul2 := mul_le_mul_of_nonneg_right hu (mul_nonneg hl.le hm.le)
      nlinarith
    have hL := separationL_bounds l s
    have hL2 : (separationL l s)^2 ≤ 1 := by nlinarith
    have hbase0 : 0 ≤ s*(separationR l s)^2 := by positivity
    nlinarith [mul_nonneg hbase0 (sub_nonneg.mpr hL2)]

lemma separation_mixed_V_square_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s^2*(separationV l s)^2*(separationL l s)^2 ≤ 9*l^2 := by
  have hm := separationFloor_pos hl s
  have hum := separation_floor_ge_sqrt l s
  have hs2 : s ≤ (separationFloor l s)^2 := by nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s]
  have hbase : s^2*(separationV l s)^2 ≤ s*(separationR l s)^2 := by
    rw [separationV,div_pow]
    have he : s^2*((separationR l s)^2/(separationFloor l s)^2)=
        (s^2*(separationR l s)^2)/(separationFloor l s)^2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    have h := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hs (sq_nonneg (separationR l s)))
    nlinarith
  exact (mul_le_mul_of_nonneg_right hbase (sq_nonneg _)).trans (separation_mixed_R_square_bound hl hs)

lemma separation_coverage_VKN {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*separationV l s*separationK l s*separationN l s=separationN l s := by
  by_cases h : Real.sqrt s ≤ 4*l
  · rw [show separationN l s=0 from spectralRamp_eq_zero (by positivity) h,mul_zero]
  · have hu : 0 < Real.sqrt s := by linarith [lt_of_not_ge h]
    have hm : separationFloor l s=Real.sqrt s := separation_floor_eq (by linarith [lt_of_not_ge h])
    have he : s*separationV l s*separationK l s=1 := by
      unfold separationV separationR separationK
      rw [hm]
      have hl' : Real.sqrt l ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hl)
      have hu' : Real.sqrt (Real.sqrt s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
      field_simp
      nlinarith [Real.sq_sqrt hs,Real.sq_sqrt hu.le]
    rw [he,one_mul]

lemma separation_coverage_K_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s*(separationK l s)^2 ≤ l⁻¹ := by
  have hm := separationFloor_pos hl s
  have hum := separation_floor_ge_sqrt l s
  have hu0 := Real.sqrt_nonneg s
  have hu1 : Real.sqrt s ≤ 1 := by nlinarith [Real.sq_sqrt hs]
  have hsle : s ≤ separationFloor l s := by nlinarith [Real.sq_sqrt hs,mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  rw [separationK_sq hl,← div_eq_mul_inv]
  apply (div_le_iff₀ (mul_pos hl hm)).mpr
  rw [show l⁻¹*(l*separationFloor l s)=separationFloor l s by field_simp]
  exact hsle

end

end WeakPureInfiniteness
end

end OAI
