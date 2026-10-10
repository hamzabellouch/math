import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleSchedule

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleTailBlock_covariance (p : ℝ × ℝ) (a b c r q δ g G : ℝ) :
    tripleClockPerturbed a b c r q δ g G+matrixChainCovariance (tripleTailBlock p)=
      tripleClockPerturbed (a+p.2^2) (b+p.2^2) (c+p.2^2) r q δ g G := by
  simp only [tripleTailBlock,matrixChainCovariance_cons,matrixChainCovariance_nil,add_zero,← add_assoc]
  have h0 := tripleClockPerturbed_tail0 a b c r q δ g G p.2
  have h1 := tripleClockPerturbed_tail1 (a+p.2^2) b c r q δ g G p.2
  have h2 := tripleClockPerturbed_tail2 (a+p.2^2) (b+p.2^2) c r q δ g G p.2
  change tripleClockPerturbed a b c r q δ g G+rankOneMatrix ![p.2,0,0]=_ at h0
  change tripleClockPerturbed (a+p.2^2) b c r q δ g G+rankOneMatrix ![0,p.2,0]=_ at h1
  change tripleClockPerturbed (a+p.2^2) (b+p.2^2) c r q δ g G+rankOneMatrix ![0,0,p.2]=_ at h2
  rw [h0,h1,h2]

theorem tripleTailBlock_penalty (p : ℝ × ℝ) (a b c r q δ g G : ℝ) :
    matrixChainPenalty (tripleTailBlock p) (tripleClockPerturbed a b c r q δ g G)=
      p.1*((a+p.2^2)^2-a^2)+p.1*((b+p.2^2)^2-b^2)+p.1*((c+p.2^2)^2-c^2)+4*p.1*δ^2*G*p.2^2 := by
  simp only [tripleTailBlock,matrixChainPenalty_cons,matrixChainPenalty_nil,add_zero]
  have h0 := tripleClockPerturbed_tail0 a b c r q δ g G p.2
  have h1 := tripleClockPerturbed_tail1 (a+p.2^2) b c r q δ g G p.2
  have h2 := tripleClockPerturbed_tail2 (a+p.2^2) (b+p.2^2) c r q δ g G p.2
  change tripleClockPerturbed a b c r q δ g G+rankOneMatrix ![p.2,0,0]=_ at h0
  change tripleClockPerturbed (a+p.2^2) b c r q δ g G+rankOneMatrix ![0,p.2,0]=_ at h1
  change tripleClockPerturbed (a+p.2^2) (b+p.2^2) c r q δ g G+rankOneMatrix ![0,0,p.2]=_ at h2
  rw [h0,h1,h2]
  have H := tripleClockPerturbed_tail_penalty a b c r q δ g G p.1 p.2
  linear_combination H

theorem tripleTailSchedule_covariance (l : List (ℝ × ℝ)) (a b c r q δ g G : ℝ) :
    tripleClockPerturbed a b c r q δ g G+matrixChainCovariance (tripleTailSchedule l)=
      tripleClockPerturbed (a+rawVariance l) (b+rawVariance l) (c+rawVariance l) r q δ g G := by
  induction l generalizing a b c with
  | nil => simp [tripleTailSchedule,rawVariance]
  | cons p l ih =>
    simp only [tripleTailSchedule] at ih
    simp only [tripleTailSchedule,List.flatMap_cons,matrixChainCovariance_append,← add_assoc,
      tripleTailBlock_covariance,ih]
    simp only [rawVariance,List.map_cons,List.sum_cons,add_assoc]

theorem tripleTailSchedule_penalty (l : List (ℝ × ℝ)) (a b c r q δ g G : ℝ) :
    matrixChainPenalty (tripleTailSchedule l) (tripleClockPerturbed a b c r q δ g G)=
      rawPenalty l a+rawPenalty l b+rawPenalty l c+4*δ^2*G*rawArea l := by
  induction l generalizing a b c with
  | nil => simp [tripleTailSchedule,rawPenalty,rawArea,chainPotentialPenalty]
  | cons p l ih =>
    simp only [tripleTailSchedule] at ih
    simp only [tripleTailSchedule,List.flatMap_cons,matrixChainPenalty_append,
      tripleTailBlock_covariance,tripleTailBlock_penalty,ih]
    simp only [rawPenalty,rawArea,List.map_cons,List.sum_cons,chainPotentialPenalty]
    ring

end SK.Analytic

end
end

end OAI
