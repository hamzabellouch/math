import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.AddConst
import OAI.Geometry.WeakHessian.Calculus.LipschitzDerivQuadraticRemainder

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
open scoped Topology NNReal

noncomputable def truncatedLog (a x : ℝ) : ℝ := Real.log a + ∫ s in a..x, (max a s)⁻¹

lemma truncatedLog_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (truncatedLog a) ((max a x)⁻¹) x := by
  have hc : Continuous (fun s : ℝ => (max a s)⁻¹) :=
    (continuous_const.max continuous_id).inv₀ (fun s => ne_of_gt (ha.trans_le (le_max_left _ _)))
  simpa only [truncatedLog] using! (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (Real.log a)

lemma truncatedLog_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (truncatedLog a) x = (max a x)⁻¹ := (truncatedLog_hasDeriv ha x).deriv

lemma truncatedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (truncatedLog a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (truncatedLog_hasDeriv ha x).differentiableAt,?_⟩
  rw [show deriv (truncatedLog a) = (fun x => (max a x)⁻¹) from funext (truncatedLog_deriv ha)]
  exact (continuous_const.max continuous_id).inv₀ (fun s => ne_of_gt (ha.trans_le (le_max_left _ _)))

lemma truncatedLog_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (truncatedLog a) x| ≤ a⁻¹ := by
  rw [truncatedLog_deriv ha,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a x)))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma truncatedLog_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith (⟨a⁻¹,inv_nonneg.mpr ha.le⟩ : ℝ≥0) (truncatedLog a) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (truncatedLog_hasDeriv ha x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  exact truncatedLog_deriv_bound ha x

lemma truncatedLog_eq {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    truncatedLog a x = Real.log x := by
  have H : (∫ s in a..x, (max a s)⁻¹) = Real.log x-Real.log a := by
    calc
      (∫ s in a..x, (max a s)⁻¹) = ∫ s in a..x, s⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hax] at hs
        exact congrArg Inv.inv (max_eq_right hs.1)
      _ = Real.log x-Real.log a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s hs
          rw [uIcc_of_le hax] at hs
          exact Real.hasDerivAt_log (ne_of_gt (ha.trans_le hs.1))
        · exact (continuousOn_id.inv₀ (fun s hs => ne_of_gt (ha.trans_le hs.1))).intervalIntegrable_of_Icc hax
  dsimp only [truncatedLog]
  rw [H]
  ring

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace

noncomputable def regularizedLog (a x : ℝ) : ℝ := truncatedLog a (x+a)-Real.log a
noncomputable def regularizedEntropy (a x : ℝ) : ℝ := ∫ s in 0..x, regularizedLog a s

lemma regularizedLog_zero (a : ℝ) : regularizedLog a 0 = 0 := by
  simp [regularizedLog,truncatedLog]
lemma regularizedEntropy_zero (a : ℝ) : regularizedEntropy a 0 = 0 := by
  simp [regularizedEntropy]
lemma regularizedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedLog a) :=
  ((truncatedLog_contDiff ha).comp (contDiff_id.add contDiff_const)).sub contDiff_const
lemma regularizedLog_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedLog a) ((max a (x+a))⁻¹) x := by
  simpa only [regularizedLog,Function.comp_def,mul_one] using!
    ((truncatedLog_hasDeriv ha (x+a)).comp x ((hasDerivAt_id x).add_const a)).sub_const (Real.log a)
lemma regularizedLog_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (regularizedLog a) x = (max a (x+a))⁻¹ := (regularizedLog_hasDeriv ha x).deriv
lemma regularizedLog_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith (⟨a⁻¹,inv_nonneg.mpr ha.le⟩ : ℝ≥0) (regularizedLog a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [regularizedLog,dist_sub_right,dist_add_right] using
    (truncatedLog_lipschitz ha).dist_le_mul (x+a) (y+a)
lemma regularizedLog_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedLog a x = Real.log (x+a)-Real.log a := by
  rw [regularizedLog,truncatedLog_eq ha (by linarith)]
lemma regularizedLog_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (regularizedLog a) x| ≤ a⁻¹ := by
  rw [regularizedLog_deriv ha,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a (x+a))))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma regularizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedEntropy a) (regularizedLog a x) x := by
  have hc := (regularizedLog_contDiff ha).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma regularizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-(Real.log a+1)*x := by
  let F : ℝ → ℝ := fun y => (y+a)*Real.log (y+a)-(Real.log a+1)*y
  have hF (y : ℝ) (hy : y ∈ uIcc 0 x) : HasDerivAt F (regularizedLog a y) y := by
    rw [uIcc_of_le hx] at hy
    have hypos : 0 < y+a := by linarith [hy.1]
    have H := ((Real.hasDerivAt_mul_log hypos.ne').comp y ((hasDerivAt_id y).add_const a)).sub
      ((hasDerivAt_id y).const_mul (Real.log a+1))
    convert! H using 1
    rw [regularizedLog_eq ha hy.1]
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((regularizedLog_contDiff ha).continuous.intervalIntegrable 0 x)
  change regularizedEntropy a x = F x-F 0 at H
  rw [H]
  dsimp [F]
  ring_nf

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma regularizedLog_memLp {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    MemLp (fun x => regularizedLog a (u x)) 2 m :=
  (regularizedLog_lipschitz ha).comp_memLp (regularizedLog_zero a) (Lp.memLp u)

lemma regularizedEntropy_hasFDeriv {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    HasFDerivAt (fun v : Lp ℝ 2 m => ∫ x, regularizedEntropy a (v x) ∂m)
      (innerSL ℝ ((regularizedLog_memLp ha u).toLp (fun x => regularizedLog a (u x)))) u :=
  hasFDerivAt_integral_quadratic (regularizedEntropy_hasDeriv ha) (regularizedLog_lipschitz ha)
    (regularizedEntropy_zero a) (regularizedLog_zero a) u

end WeakHessian

end
end InlinedFile0

end OAI
