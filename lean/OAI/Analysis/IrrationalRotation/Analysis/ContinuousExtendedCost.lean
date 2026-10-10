import OAI.Analysis.IrrationalRotation.Model.ContinuousExtendedCost
import OAI.Analysis.IrrationalRotation.Rotation.ContinuousWeightAssembly
import OAI.Analysis.IrrationalRotation.Analysis.ExtendedExponential

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.CircleParameterData

variable (p : CircleParameterData) (θ : ℝ) (d : BackgroundBumpData θ)

@[simp] theorem extendedContinuousCost_zero : p.extendedContinuousCost θ d 0 = ∞ := by
  classical
  simp [extendedContinuousCost]

theorem extendedContinuousCost_of_ne_zero {x : Circle} (hx : x ≠ 0) :
    p.extendedContinuousCost θ d x = ENNReal.ofReal (p.continuousCost θ d x) := by
  classical
  exact Function.update_of_ne hx _ _

theorem extendedContinuousCost_eq_top_iff (x : Circle) :
    p.extendedContinuousCost θ d x = ∞ ↔ x = 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  · simp [extendedContinuousCost_of_ne_zero p θ d hx, hx]

theorem negLogCost_continuousWeight (x : Circle) :
    negLogCost (p.continuousWeight θ d x) = p.extendedContinuousCost θ d x := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [continuousWeight, negLogCost]
  · rw [extendedContinuousCost_of_ne_zero p θ d hx]
    unfold continuousWeight
    rw [Function.update_of_ne hx]
    simp [negLogCost, Real.exp_ne_zero, abs_of_pos (Real.exp_pos _), Real.log_exp]

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem continuous_extendedContinuousCost (d : BackgroundBumpData θ) :
    Continuous (p.extendedContinuousCost θ d) := by
  classical
  unfold CircleParameterData.extendedContinuousCost
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [continuousAt_update_same]
    exact ENNReal.tendsto_ofReal_atTop.comp (hp.tendsto_continuousCost_atTop d)
  · rw [continuousAt_update_of_ne hx]
    have hc : ContinuousAt (p.continuousCost θ d) x :=
      (hp.continuousOn_continuousCost d x hx).continuousAt
        (isOpen_compl_singleton.mem_nhds hx)
    exact ENNReal.continuous_ofReal.continuousAt.comp hc

theorem extendedContinuousCost_ge_half (d : BackgroundBumpData θ) (x : Circle) :
    ENNReal.ofReal (1 / 2) ≤ p.extendedContinuousCost θ d x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [p.extendedContinuousCost_of_ne_zero θ d hx]
    exact ENNReal.ofReal_le_ofReal (hp.continuousCost_ge_half d x)

theorem continuousWeight_eq_extendedExpNeg (d : BackgroundBumpData θ) (x : Circle) :
    p.continuousWeight θ d x =
      (EReal.exp (-(p.extendedContinuousCost θ d x : EReal))).toReal := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [CircleParameterData.continuousWeight]
  · rw [p.extendedContinuousCost_of_ne_zero θ d hx,
      extendedExpNeg_eq_exp_toReal _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal]
    · exact Function.update_of_ne hx _ _
    · exact (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans (hp.continuousCost_ge_half d x)

theorem lintegral_extendedContinuousCost_eq_top (d : BackgroundBumpData θ) :
    (∫⁻ x, p.extendedContinuousCost θ d x ∂circleMeasure) = ∞ := by
  simp_rw [← p.negLogCost_continuousWeight θ d]
  exact (hp.isContinuousCircleWeight_continuousWeight d).2.2.2

theorem extendedContinuousCost_ae_coboundary (d : BackgroundBumpData θ) :
    p.extendedContinuousCost θ d =ᵐ[circleMeasure] fun x => ENNReal.ofReal
      (p.rawCost θ x + 1 + p.continuousTransfer θ d (x + (θ : Circle)) -
        p.continuousTransfer θ d x) := by
  have hne : ∀ᵐ x ∂circleMeasure, x ≠ (0 : Circle) := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using circleMeasure_singleton 0
  filter_upwards [hne, hp.continuousCost_ae_coboundary d] with x hx hc
  rw [p.extendedContinuousCost_of_ne_zero θ d hx, hc]

end Invariant233.CircleParameterLaws

end

end OAI
