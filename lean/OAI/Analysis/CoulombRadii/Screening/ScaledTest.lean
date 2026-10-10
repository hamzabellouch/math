import Mathlib
import OAI.Analysis.CoulombRadii.Localization.RadialCut
import OAI.Analysis.CoulombRadii.FieldAnalysis.CoulombTest

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

lemma dirPartial_scaled {f : Space → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (y x v : Space) :
    dirPartial (fun z => f (c • (z-y))) v x = c*dirPartial f v (c • (x-y)) := by
  have ht : HasFDerivAt (fun z : Space => c • (z-y))
      (c • ContinuousLinearMap.id ℝ Space) x := by
    convert ((hasFDerivAt_id x).sub_const y).const_smul c using 1
    rfl
  have h := ((hf (c • (x-y))).hasFDerivAt.comp x ht).fderiv
  simp only [Function.comp_def] at h
  unfold dirPartial
  rw [h]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]

lemma dirPartial_const_mul {f : Space → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x v : Space) :
    dirPartial (fun z => c*f z) v x = c*dirPartial f v x := by
  unfold dirPartial
  rw [((hf x).hasFDerivAt.const_mul c).fderiv]
  rfl

lemma coordinateLaplacian_scaled {f : Space → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (y x : Space) :
    coordinateLaplacian (fun z => f (c • (z-y))) x = c^2*coordinateLaplacian f (c • (x-y)) := by
  have hg : ContDiff ℝ 2 (fun z : Space => f (c • (z-y))) := hf.comp (by fun_prop)
  rw [NeutralAtom.coordinateLaplacian_eq_partials hg.contDiffAt,
    NeutralAtom.coordinateLaplacian_eq_partials hf.contDiffAt,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : dirPartial (fun z => f (c • (z-y))) (axis i) =
      fun z => c*dirPartial f (axis i) (c • (z-y)) := by
    funext z; exact dirPartial_scaled (hf.differentiable (by norm_num)) c y z _
  rw [he]
  have hp : Differentiable ℝ (dirPartial f (axis i)) :=
    (NeutralAtom.contDiff_partial (n := 1) hf (axis i)).differentiable (by norm_num)
  have hpc : Differentiable ℝ (fun z : Space => dirPartial f (axis i) (c • (z-y))) := hp.comp (by fun_prop)
  rw [dirPartial_const_mul hpc c,
    dirPartial_scaled hp c]
  ring

def countTest (y : Space) (a : ℝ) (x : Space) : ℝ := cutSeed (a⁻¹ • (x-y))
lemma countTest_smooth (y : Space) (a : ℝ) : ContDiff ℝ ∞ (countTest y a) := cutSeed_smooth.comp (by fun_prop)
lemma countTest_nonneg (y : Space) (a : ℝ) (x : Space) : 0≤countTest y a x := Real.smoothTransition.nonneg _
lemma countTest_le_one (y : Space) (a : ℝ) (x : Space) : countTest y a x≤1 := Real.smoothTransition.le_one _
lemma countTest_one (y : Space) {a : ℝ} (ha : 0<a) {x : Space} (hx : ‖x-y‖≤a) : countTest y a x=1 := by
  apply cutSeed_one
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),←div_eq_inv_mul]
  exact (div_le_one ha).mpr hx
lemma countTest_zero (y : Space) {a : ℝ} (ha : 0<a) {x : Space} (hx : 2*a≤‖x-y‖) : countTest y a x=0 := by
  apply cutSeed_zero
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),←div_eq_inv_mul]
  exact (le_div_iff₀ ha).mpr hx
lemma countTest_support (y : Space) {a : ℝ} (ha : 0<a) :
    tsupport (countTest y a)⊆Metric.closedBall y (2*a) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  have hh : 2*a≤‖x-y‖ := le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hn)
  exact hx (countTest_zero y ha hh)
lemma countTest_compact (y : Space) {a : ℝ} (ha : 0<a) : HasCompactSupport (countTest y a) :=
  (isCompact_closedBall y (2*a)).of_isClosed_subset isClosed_closure (countTest_support y ha)

lemma testCharge_countTest (y : Space) (a : ℝ) (x : Space) :
    testCharge (countTest y a) x=a⁻¹^2*testCharge cutSeed (a⁻¹ • (x-y)) := by
  unfold testCharge countTest
  rw [coordinateLaplacian_scaled (cutSeed_smooth.of_le (by exact WithTop.coe_le_coe.mpr le_top))]
  ring

def countTestEnergy : ℝ := ∫ x, testCharge cutSeed x*cutSeed x

lemma countTest_energy (y : Space) {a : ℝ} (ha : 0<a) :
    (∫ x, testCharge (countTest y a) x*countTest y a x)=a*countTestEnergy := by
  simp only [testCharge_countTest,countTest,mul_assoc,integral_const_mul]
  rw [←integral_add_right_eq_self (fun x : Space => (testCharge cutSeed (a⁻¹ • (x-y))*cutSeed (a⁻¹ • (x-y)))) y]
  simp only [add_sub_cancel_right]
  rw [Measure.integral_comp_inv_smul (volume : Measure Space) (fun x => testCharge cutSeed x*cutSeed x) a]
  simp only [show Module.finrank ℝ Space=3 from by simp [Space],smul_eq_mul,abs_of_pos (pow_pos ha _)]
  dsimp only [countTestEnergy]
  field_simp

end Coulomb

end

end
end

end OAI
