import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKernelAnalytic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! The concrete cusp cutoff and compact support of its derivatives. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace CubicFirstMoment

def cubicThetaCuspCutoff (v : ℝ) : ℂ := Real.smoothTransition (v-1)

lemma cubicThetaCuspCutoff_zero {v : ℝ} (hv : v ≤ 1) : cubicThetaCuspCutoff v=0 := by
  simp only [cubicThetaCuspCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : v-1 ≤ 0),
    Complex.ofReal_zero]

lemma cubicThetaCuspCutoff_one {v : ℝ} (hv : 2 ≤ v) : cubicThetaCuspCutoff v=1 := by
  simp only [cubicThetaCuspCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ v-1),
    Complex.ofReal_one]

lemma cubicThetaCuspCutoff_smooth : ContDiff ℝ ∞ cubicThetaCuspCutoff :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))

lemma cubicThetaCuspCutoff_derivatives_zero {v : ℝ} (hv : v<1 ∨ 2<v) :
    deriv cubicThetaCuspCutoff v=0 ∧ deriv (deriv cubicThetaCuspCutoff) v=0 := by
  have he : ∃ C : ℂ, cubicThetaCuspCutoff =ᶠ[𝓝 v] (fun _ => C) := by
    rcases hv with hv | hv
    · refine ⟨0,?_⟩
      filter_upwards [eventually_lt_nhds hv] with t ht
      exact cubicThetaCuspCutoff_zero ht.le
    · refine ⟨1,?_⟩
      filter_upwards [eventually_gt_nhds hv] with t ht
      exact cubicThetaCuspCutoff_one ht.le
  obtain ⟨C,hC⟩ := he
  refine ⟨?_,?_⟩
  · simpa only [deriv_const] using hC.deriv_eq
  · simpa only [deriv_const',deriv_const] using hC.deriv.deriv_eq

lemma cubicThetaCuspCutoff_deriv_compact : HasCompactSupport (deriv cubicThetaCuspCutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra h
  have he : v<1 ∨ 2<v := by simpa only [mem_Icc,not_and_or,not_le] using h
  exact hv (cubicThetaCuspCutoff_derivatives_zero he).1

lemma cubicThetaCuspCutoff_second_compact : HasCompactSupport (deriv (deriv cubicThetaCuspCutoff)) :=
  cubicThetaCuspCutoff_deriv_compact.deriv

end CubicFirstMoment

end

end OAI
