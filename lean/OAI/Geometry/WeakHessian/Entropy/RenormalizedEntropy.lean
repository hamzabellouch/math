import Mathlib
import OAI.Geometry.WeakHessian.Entropy.TruncatedLog

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
open Set Filter
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
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

noncomputable def renormalizedEntropy (a x : ℝ) : ℝ :=
  regularizedEntropy a x+Real.log a*x

lemma renormalizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    renormalizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-x := by
  rw [renormalizedEntropy,regularizedEntropy_eq ha hx]
  ring

lemma renormalizedEntropy_lower {a x w : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hw : 0 < w) :
    x*Real.log w-w ≤ renormalizedEntropy a x := by
  by_cases hz : x = 0
  · simp only [hz,renormalizedEntropy,regularizedEntropy_zero,mul_zero,zero_add,zero_mul,zero_sub]
    linarith
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have H := Real.log_le_sub_one_of_pos (div_pos hw hxp)
  rw [Real.log_div hw.ne' hxp.ne'] at H
  have HH := mul_le_mul_of_nonneg_left H hx
  have hdiv : x*(w/x-1)=w-x := by field_simp
  rw [hdiv] at HH
  have hxlog := mul_le_mul_of_nonneg_left (Real.log_le_log hxp (le_add_of_nonneg_right ha.le)) hx
  have halog := mul_le_mul_of_nonneg_left (Real.log_le_log ha (le_add_of_nonneg_left hx)) ha.le
  rw [renormalizedEntropy_eq ha hx]
  nlinarith

lemma renormalizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (renormalizedEntropy a) (regularizedLog a x+Real.log a) x := by
  simpa only [renormalizedEntropy,Pi.add_apply,id_eq,mul_one] using! (regularizedEntropy_hasDeriv ha x).add
    ((hasDerivAt_id x).const_mul (Real.log a))

lemma renormalizedEntropy_upper {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    renormalizedEntropy a x ≤ x^2/2 := by
  let F (y : ℝ) := renormalizedEntropy a y-y^2/2
  have hd (y : ℝ) : HasDerivAt F (regularizedLog a y+Real.log a-y) y := by
    convert! (renormalizedEntropy_hasDeriv ha y).sub (((hasDerivAt_id y).pow 2).div_const 2) using 1
    first | rfl | (simp only [id_eq]; ring)
  have H : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Ici 0)
      rw [regularizedLog_eq ha hy0]
      have HH := Real.log_le_sub_one_of_pos (by linarith : 0 < y+a)
      linarith
  have HH := H (show (0:ℝ) ∈ Ici 0 from (by simp)) hx hx
  have hF0 : F 0 = 0 := by simp [F,renormalizedEntropy,regularizedEntropy_zero]
  rw [hF0] at HH
  dsimp [F] at HH
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
