import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.MidpointSigmaLower

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
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

def compressionRate (K N : ℝ) : ℝ := (N-1)*Real.sqrt (|K|/(N-1))

lemma compressionRate_nonneg {K N : ℝ} (hN : 1 < N) : 0 ≤ compressionRate K N := by
  exact mul_nonneg (sub_nonneg.mpr hN.le) (Real.sqrt_nonneg _)

lemma midpoint_cap_factor {K N D : ℝ} (hN : 1 < N) :
    ((2:ℝ≥0∞)*midpointTauLower K N D)^N =
      ENNReal.ofReal (Real.exp (-compressionRate K N*D)) := by
  have hNp : 0 < N := by linarith
  have hp : 0 ≤ 1/N := by positivity
  have hq : 0 ≤ (N-1)/N := div_nonneg (by linarith) hNp.le
  have hs := midpointSigmaLower_pos K (N-1) D
  rw [midpointTauLower,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hp,
    ENNReal.ofReal_rpow_of_nonneg hs.le hq]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity) hNp.le]
  congr 1
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  rw [Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num : (0:ℝ) < 1/2),Real.log_rpow hs]
  simp only [midpointSigmaLower, one_div, Real.log_inv, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  simp only [compressionRate]
  field_simp
  ring

lemma midpoint_cap_eq {K N D : ℝ} (hN : 1 < N) (C : ℝ≥0∞) :
    C/((2:ℝ≥0∞)*midpointTauLower K N D)^N =
      C*ENNReal.ofReal (Real.exp (compressionRate K N*D)) := by
  rw [midpoint_cap_factor hN,div_eq_mul_inv]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),← Real.exp_neg]
  congr 2
  ring

end WeakHessian
end
end InlinedFile0

end OAI
