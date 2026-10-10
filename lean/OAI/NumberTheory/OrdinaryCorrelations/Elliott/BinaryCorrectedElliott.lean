import OAI.NumberTheory.OrdinaryCorrelations.Elliott.RelativeErrorTendsto

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators ContDiff
open Finset Filter Classical
open scoped BigOperators ContDiff Topology
open scoped BigOperators Topology

namespace OrdinaryCorrelations
open ElliottReductions

theorem binary_corrected_elliott
    (f₁ f₂ : ℕ → ℂ) (hf₁ : OneBounded f₁) (hf₂ : OneBounded f₂)
    (hm₁ : Multiplicative f₁) (hm₂ : Multiplicative f₂)
    (hNP : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (h₁ h₂ : ℕ) (hne : h₁ ≠ h₂) :
    Tendsto (shiftAverage f₁ f₂ h₁ h₂) atTop (nhds 0) := by
  rcases lt_or_gt_of_ne hne with hh | hh
  · exact shiftAverage_of_anchored f₁ f₂ hf₁ hf₂ h₁ h₂ hh.le
      (ElliottCompletion.anchored f₁ f₂ hf₁ hf₂ hm₁ hm₂ hNP (h₂-h₁) (Nat.sub_pos_of_lt hh))
  · have ht := shiftAverage_of_anchored f₂ f₁ hf₂ hf₁ h₂ h₁ hh.le
      (ElliottCompletion.anchored f₂ f₁ hf₂ hf₁ hm₂ hm₁ hNP.symm (h₁-h₂) (Nat.sub_pos_of_lt hh))
    have he : shiftAverage f₂ f₁ h₂ h₁=shiftAverage f₁ f₂ h₁ h₂ :=
      funext (fun N=>shiftAverage_swap f₂ f₁ h₂ h₁ N)
    rwa [he] at ht

end OrdinaryCorrelations

end

end OAI
