import Mathlib
import OAI.Probability.SKSupport.Control.ExpectedControlPayoff
import OAI.Probability.SKSupport.Foundations.IntegralIoiMulExpSq

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma BrownianSystem.abs_increment (W : BrownianSystem Ω) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ ω, |W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) =
      Real.sqrt (2*(1-t)/Real.pi) := by
  have h := (W.brownian.hasLaw_sub 1 (Real.toNNReal t)).integral_comp
    (f := abs) (continuous_abs.measurable.aestronglyMeasurable)
  change (∫ ω, |W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) = _ at h
  rw [h, Gaussian.gaussian_abs_moment]
  congr 1
  rw [coe_nndist, Real.dist_eq]
  change 2 * |(1:ℝ) - (Real.toNNReal t : ℝ)| / Real.pi = _
  rw [Real.coe_toNNReal _ ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]

theorem value_terminal_uniform (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ value W γ t x - |x| ∧
    value W γ t x - |x| ≤ Real.sqrt (2*(1-t)/Real.pi) +
      (1/2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  let := W.isProbability
  refine ⟨sub_nonneg.mpr (abs_le_value W γ t x ht1), ?_⟩
  have hi : Integrable (fun ω => W.B 1 ω - W.B (Real.toNNReal t) ω) W.law :=
    (W.brownian.integrable_eval 1).sub (W.brownian.integrable_eval _)
  have hbound : (∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) ≤
      |x| + Real.sqrt (2*(1-t)/Real.pi) := by
    calc
      _ ≤ ∫ ω, (|x| + |W.B 1 ω - W.B (Real.toNNReal t) ω|) ∂W.law := by
        apply integral_mono (((integrable_const x).add
          (W.brownian.integrable_eval 1)).sub (W.brownian.integrable_eval _)).abs
          ((integrable_const _).add hi.abs)
        intro ω
        change |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ≤
          |x| + |W.B 1 ω - W.B (Real.toNNReal t) ω|
        simpa only [add_sub_assoc] using abs_add_le x (W.B 1 ω - W.B (Real.toNNReal t) ω)
      _ = _ := by rw [integral_add (integrable_const _) hi.abs]; simp [W.abs_increment t ht0 ht1]
  have := value_le_expected_abs W γ t x ht1
  linarith

end ZeroTemperatureSK

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

end
end
end

end OAI
