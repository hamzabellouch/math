import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.TimeChainOnAnalytic
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Locking.NarrowTimeBlocks
import OAI.Probability.SKBarriers.Locking.NarrowMomentBound
import OAI.Probability.SKBarriers.Parisi.CDFJointBridge

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowJointMoment_eq (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    narrowJointMoment c w t=scalarIncrementAverage (weightedUnderlying c)
      (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal))
      (fun x => rootHessian 0 (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)) x*
        scalarIncrementAverage (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)
          (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) x) 0 := by
  dsimp only [narrowJointMoment]
  simp_rw [weightedBranch_average]
  simp_rw [mul_comm]
  exact congrFun (weightedBranch_average c
    (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal))
    (fun x => scalarIncrementAverage (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)
      (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) x*
      rootHessian 0 (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)) x)) (0,0)

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (B : NarrowTimeBlocks α r h q)

theorem full_mass (a : ℝ) : ∀ p∈weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t,p.1∈Icc (0:ℝ) 1 := by
  rw [← B.full_raw a]; exact B.full.raw_mass

theorem full_sorted (hm : Monotone α) (a : ℝ) :
    (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t).Pairwise (fun p q => p.1≤q.1) := by
  rw [← B.full_raw a]; exact B.full.raw_sorted hm

theorem scalar_parisi (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (a : ℝ) :
    scalarIncrementChain (scaleIncrementChain β (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t)) scalarSpinTerminal 0-
      β^2/4*rawPenalty (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t) 0=scalarCDFParisi β α := by
  rw [← B.full_raw a,B.full.scalar_value β ha hm (by norm_num),B.full.penalty hm]
  simp only [sub_zero,Real.toNNReal_one,scalarCDFParisi,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  ring

theorem scalar_susceptibility (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hq : q∈Icc (0:ℝ) 1) (a : ℝ) :
    narrowSusceptibility (scaleIncrementChain β (B.c a)) (scaleIncrementChain β (B.w a)) (scaleIncrementChain β B.t)=
      scalarCDFSusceptibilityAverage β α q := by
  rw [narrowSusceptibility_eq,weightedUnderlying_append,weightedUnderlying_scale,weightedUnderlying_scale,
    ← scaleIncrementChain_append,← B.front_raw a]
  exact B.front.scalar_susceptibility β ha hm hq B.tail

theorem scalar_joint (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1) (a : ℝ) :
    narrowJointMoment (scaleIncrementChain β (B.c a)) (scaleIncrementChain β (B.w a)) (scaleIncrementChain β B.t)=
      scalarCDFJointSusceptibility β α r q := by
  rw [narrowJointMoment_eq,weightedUnderlying_scale,weightedUnderlying_scale,← B.common_raw a,← B.middle_raw a]
  simp only [t,scalarIncrementChain_rawTimeChain,scalarIncrementAverage_rawTimeChain]
  exact timeChainJointHessian_eq_cdf β ha hm hr hrq hq B.common B.middle B.tail

theorem tail_area (hm : Monotone α) : rawArea B.t=∫ x in q..1,α x := B.tail.area hm

theorem right_area (hm : Monotone α) : rawArea B.j=∫ x in r..r+h,α x := B.right.area hm

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
