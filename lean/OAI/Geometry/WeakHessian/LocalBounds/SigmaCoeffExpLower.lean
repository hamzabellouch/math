import Mathlib
import OAI.Geometry.WeakHessian.Model
import OAI.Geometry.WeakHessian.Calculus.DerivSinSubMul

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open scoped ENNReal

lemma sigmaCoeff_exp_lower {K N t θ : ℝ} (hN : 0 < N)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (t*Real.exp (K*θ^2*(1-t^2)/(6*N))) ≤ sigmaCoeff K N t θ := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [sigmaCoeff]
  rcases ht1.eq_or_lt with rfl | ht1
  · norm_num [sigmaCoeff]
  unfold sigmaCoeff
  simp only [not_le_of_gt ht,not_le_of_gt ht1,ite_false]
  split_ifs with hzero hK hcut hKzero
  · simp [hzero]
  · apply ENNReal.ofReal_le_ofReal
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (K/N) := Real.sqrt_pos.mpr (div_pos hK hN)
    have hx : 0 < θ * Real.sqrt (K/N) := mul_pos hθpos hroot
    have hsq : (θ * Real.sqrt (K/N))^2 * N = K*θ^2 := by
      rw [mul_pow, Real.sq_sqrt (div_pos hK hN).le]
      field_simp
    have hslt : (θ * Real.sqrt (K/N))^2 < Real.pi^2 := by
      apply (mul_lt_mul_iff_left₀ hN).mp
      rw [hsq]
      nlinarith [hcut]
    have hpi : θ * Real.sqrt (K/N) < Real.pi := by nlinarith [Real.pi_pos]
    have he : (1-t^2)*(θ*Real.sqrt (K/N))^2/6 = K*θ^2*(1-t^2)/(6*N) := by
      rw [mul_pow,Real.sq_sqrt (div_pos hK hN).le]
      field_simp
    simpa only [he,mul_assoc] using sin_ratio_exp_lower ht ht1.le hx hpi
  · exact le_top
  · simp [hKzero]
  · apply ENNReal.ofReal_le_ofReal
    have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hK) hKzero
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (-K/N) := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) hN)
    have hx : 0 < θ * Real.sqrt (-K/N) := mul_pos hθpos hroot
    have hsq : (θ * Real.sqrt (-K/N))^2 * N = -K*θ^2 := by
      rw [mul_pow, Real.sq_sqrt (div_pos (neg_pos.mpr hKneg) hN).le]
      field_simp
    have he : -((1-t^2)*(θ*Real.sqrt (-K/N))^2/6) = K*θ^2*(1-t^2)/(6*N) := by
      rw [mul_pow,Real.sq_sqrt (div_pos (neg_pos.mpr hKneg) hN).le]
      field_simp
    simpa only [he,mul_assoc] using sinh_ratio_exp_lower ht ht1.le hx

lemma tauCoeff_exp_lower {K N t θ : ℝ} (hN : 1 < N)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (t*Real.exp (K*θ^2*(1-t^2)/(6*N))) ≤ tauCoeff K N t θ := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [zero_mul,ENNReal.ofReal_zero]
    exact bot_le
  have hN0 : 0 < N := by linarith
  have hNm : 0 < N-1 := by linarith
  have hq : 0 ≤ (N-1)/N := (div_pos hNm hN0).le
  have H := mul_le_mul_right
    (ENNReal.rpow_le_rpow (sigmaCoeff_exp_lower (K := K) hNm ht.le ht1 hθ) hq)
    ((ENNReal.ofReal t)^(1/N))
  change _ ≤ tauCoeff K N t θ at H
  have he : (t:ℝ)^(1/N) *
      (t*Real.exp (K*θ^2*(1-t^2)/(6*(N-1))))^((N-1)/N) =
      t*Real.exp (K*θ^2*(1-t^2)/(6*N)) := by
    rw [Real.mul_rpow ht.le (Real.exp_pos _).le,← mul_assoc,← Real.rpow_add ht,
      show 1/N+(N-1)/N=1 by field_simp; ring,Real.rpow_one,← Real.exp_mul]
    congr 2
    field_simp
  rw [ENNReal.ofReal_rpow_of_pos ht,
    ENNReal.ofReal_rpow_of_pos (mul_pos ht (Real.exp_pos _)),
    ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos ht _).le,he] at H
  exact H
end WeakHessian

end
end InlinedFile0

end OAI
