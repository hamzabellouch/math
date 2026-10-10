import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightStats
import OAI.Probability.SKBarriers.Hierarchy.WeightedListMean

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem weightedMean_constantWeight (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedMean (constantWeightChain κ l)=κ*rawArea l := by
  induction l with
  | nil => simp [weightedMean,rawArea,constantWeightChain]
  | cons p l ih =>
    change κ*p.2*p.2*p.1+weightedMean (constantWeightChain κ l)=κ*(p.1*p.2^2+rawArea l)
    rw [ih]; ring

@[simp] theorem weightedMean_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedMean (scaleIncrementChain β w)=β^2*weightedMean w := by
  induction w with
  | nil => simp [weightedMean,scaleIncrementChain]
  | cons p w ih =>
    change β*p.2.2*(β*p.2.1)*p.1+weightedMean (scaleIncrementChain β w)=β^2*(p.2.2*p.2.1*p.1+weightedMean w)
    rw [ih]; ring

theorem rawPenalty_shift (l : List (ℝ × ℝ)) (q s : ℝ) :
    rawPenalty l (q+s)=rawPenalty l q+2*s*rawArea l := by
  induction l generalizing q with
  | nil => simp [rawPenalty,rawArea,chainPotentialPenalty]
  | cons p l ih =>
    change p.1*((q+s+p.2^2)^2-(q+s)^2)+rawPenalty l (q+s+p.2^2)=
      p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2)+2*s*(p.1*p.2^2+rawArea l)
    rw [show q+s+p.2^2=(q+p.2^2)+s by ring,ih]
    ring

theorem constantWeightChain_penalty_offset (κ : ℝ) (l : List (ℝ × ℝ)) (x : ℝ) :
    weightedCrossPenalty (constantWeightChain κ l) x=κ^2*rawPenalty l 0+2*x*κ*rawArea l := by
  induction l generalizing x with
  | nil => simp [weightedCrossPenalty,rawPenalty,rawArea,constantWeightChain,chainPotentialPenalty]
  | cons p l ih =>
    change p.1*((x+p.2*(κ*p.2))^2-x^2)+weightedCrossPenalty (constantWeightChain κ l) (x+p.2*(κ*p.2))=
      κ^2*(p.1*((0+p.2^2)^2-0^2)+rawPenalty l (0+p.2^2))+2*x*κ*(p.1*p.2^2+rawArea l)
    rw [ih]
    have H := rawPenalty_shift l 0 (p.2^2)
    simp only [zero_add] at *
    rw [H]
    ring

end SK.Analytic

end
end

end OAI
