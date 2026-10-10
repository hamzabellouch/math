import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats
import OAI.Probability.SKBarriers.Replicas.TripleScheduleScale

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem rawVariance_scale (β : ℝ) (l : List (ℝ × ℝ)) :
    rawVariance (scaleIncrementChain β l)=β^2*rawVariance l := by
  induction l with
  | nil => simp [rawVariance,scaleIncrementChain]
  | cons p l ih =>
    change (β*p.2)^2+rawVariance (scaleIncrementChain β l)=β^2*(p.2^2+rawVariance l)
    rw [ih]; ring

@[simp] theorem rawArea_scale (β : ℝ) (l : List (ℝ × ℝ)) :
    rawArea (scaleIncrementChain β l)=β^2*rawArea l := by
  induction l with
  | nil => simp [rawArea,scaleIncrementChain]
  | cons p l ih =>
    change p.1*(β*p.2)^2+rawArea (scaleIncrementChain β l)=β^2*(p.1*p.2^2+rawArea l)
    rw [ih]; ring

@[simp] theorem weightedVariance_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedVariance (scaleIncrementChain β w)=β^2*weightedVariance w := by
  induction w with
  | nil => simp [weightedVariance,scaleIncrementChain]
  | cons p w ih =>
    change (β*p.2.2)^2+weightedVariance (scaleIncrementChain β w)=β^2*(p.2.2^2+weightedVariance w)
    rw [ih]; ring

@[simp] theorem weightedCross_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedCross (scaleIncrementChain β w)=β^2*weightedCross w := by
  induction w with
  | nil => simp [weightedCross,scaleIncrementChain]
  | cons p w ih =>
    change (β*p.2.1)*(β*p.2.2)+weightedCross (scaleIncrementChain β w)=β^2*(p.2.1*p.2.2+weightedCross w)
    rw [ih]; ring

@[simp] theorem weightedAbsCross_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedAbsCross (scaleIncrementChain β w)=β^2*weightedAbsCross w := by
  induction w with
  | nil => simp [weightedAbsCross,scaleIncrementChain]
  | cons p w ih =>
    change |β*p.2.2| * |β*p.2.1|+weightedAbsCross (scaleIncrementChain β w)=β^2*(|p.2.2| * |p.2.1|+weightedAbsCross w)
    rw [ih,abs_mul,abs_mul,← sq_abs β]; ring

theorem weightedCrossPenalty_scale (β g : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedCrossPenalty (scaleIncrementChain β w) (β^2*g)=β^4*weightedCrossPenalty w g := by
  induction w generalizing g with
  | nil => simp [weightedCrossPenalty,scaleIncrementChain,chainPotentialPenalty]
  | cons p w ih =>
    change p.1*((β^2*g+(β*p.2.1)*(β*p.2.2))^2-(β^2*g)^2)+
      weightedCrossPenalty (scaleIncrementChain β w) (β^2*g+(β*p.2.1)*(β*p.2.2))=
        β^4*(p.1*((g+p.2.1*p.2.2)^2-g^2)+weightedCrossPenalty w (g+p.2.1*p.2.2))
    rw [show β^2*g+(β*p.2.1)*(β*p.2.2)=β^2*(g+p.2.1*p.2.2) by ring,ih]
    ring

@[simp] theorem weightedCrossPenalty_scale_zero (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedCrossPenalty (scaleIncrementChain β w) 0=β^4*weightedCrossPenalty w 0 := by
  simpa only [mul_zero] using weightedCrossPenalty_scale β 0 w

theorem scaleIncrementChain_mass {E : Type} [SMul ℝ E] (β : ℝ) (l : List (ℝ × E)) {P : ℝ → Prop}
    (hm : ∀ p∈l,P p.1) : ∀ p∈scaleIncrementChain β l,P p.1 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hm q hq

theorem scaleIncrementChain_sorted {E : Type} [SMul ℝ E] (β : ℝ) (l : List (ℝ × E))
    (hs : l.Pairwise (fun p q => p.1≤q.1)) : (scaleIncrementChain β l).Pairwise (fun p q => p.1≤q.1) := by
  simpa only [scaleIncrementChain,List.pairwise_map] using hs

end SK.Analytic

end
end

end OAI
