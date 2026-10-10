import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleSchedule
import OAI.Probability.SKBarriers.Locking.NarrowClockAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

abbrev NarrowMiddleIncrement := ProductIncrement (E:=ℝ × ℝ) (F:=ℝ × ℝ)

def narrowCommonSchedule (δ : ℝ) (l : List (ℝ × (ℝ × ℝ))) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (p.1/3,![p.2.1,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2]))

def narrowMiddleVector (δ : ℝ) : NarrowMiddleIncrement → Fin 3 → ℝ
  | .inl p => ![p.2.1,δ*p.2.2,-δ*p.2.2]
  | .inr p => ![0,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2]

def narrowMiddleSchedule (δ : ℝ) (l : List NarrowMiddleIncrement) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (productMass p,narrowMiddleVector δ p))

def narrowMiddleNoise : NarrowMiddleIncrement → ℝ
  | .inl p => p.2.2
  | .inr p => p.2.2

def narrowNoisePenalty (l : List NarrowMiddleIncrement) (K : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (productMass p,(narrowMiddleNoise p)^2))) K

theorem narrowCommonSchedule_covariance (δ : ℝ) (l : List (ℝ × (ℝ × ℝ))) (r g K : ℝ) :
    narrowClockPerturbed r r r r r δ g g K+matrixChainCovariance (narrowCommonSchedule δ l)=
      narrowClockPerturbed (r+rawVariance (weightedUnderlying l)) (r+rawVariance (weightedUnderlying l))
        (r+rawVariance (weightedUnderlying l)) (r+rawVariance (weightedUnderlying l))
        (r+rawVariance (weightedUnderlying l)) δ (g+weightedCross l) (g+weightedCross l) (K+weightedVariance l) := by
  induction l generalizing r g K with
  | nil => simp [narrowCommonSchedule,rawVariance,weightedUnderlying,weightedCross,weightedVariance]
  | cons p l ih =>
    simp only [narrowCommonSchedule] at ih
    simp only [narrowCommonSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
    change (fun i j => narrowClockPerturbed r r r r r δ g g K i j+
      (![p.2.1,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2] : Fin 3 → ℝ) i*
      (![p.2.1,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2] : Fin 3 → ℝ) j)+_=_
    rw [narrowClockPerturbed_common,ih]
    simp only [weightedUnderlying,rawVariance,weightedCross,weightedVariance,List.map_cons,List.sum_cons,add_assoc]

theorem narrowCommonSchedule_penalty (δ : ℝ) (l : List (ℝ × (ℝ × ℝ))) (r g K : ℝ) :
    matrixChainPenalty (narrowCommonSchedule δ l) (narrowClockPerturbed r r r r r δ g g K)=
      3*rawPenalty (weightedUnderlying l) r+4*δ^2*weightedCrossPenalty l g+
        4/3*δ^4*weightedVariancePenalty l K := by
  induction l generalizing r g K with
  | nil => simp [narrowCommonSchedule,rawPenalty,weightedUnderlying,weightedCrossPenalty,weightedVariancePenalty,chainPotentialPenalty]
  | cons p l ih =>
    simp only [narrowCommonSchedule] at ih
    simp only [narrowCommonSchedule,List.map_cons,matrixChainPenalty_cons]
    have he := narrowClockPerturbed_common r δ g K p.2.1 p.2.2
    change narrowClockPerturbed r r r r r δ g g K+
      rankOneMatrix (![p.2.1,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2] : Fin 3 → ℝ)=_ at he
    rw [he]
    change p.1/3*(_-_)+_=_
    rw [narrowClockPerturbed_common_penalty,ih]
    simp only [weightedUnderlying,rawPenalty,weightedCrossPenalty,weightedVariancePenalty,List.map_cons,chainPotentialPenalty]
    ring

theorem narrowMiddleSchedule_covariance (δ : ℝ) (l : List NarrowMiddleIncrement) (a b r g y K : ℝ) :
    narrowClockPerturbed a b b r b δ g y K+matrixChainCovariance (narrowMiddleSchedule δ l)=
      narrowClockPerturbed (a+rawVariance (weightedUnderlying (productLeft l)))
        (b+rawVariance (weightedUnderlying (productRight l))) (b+rawVariance (weightedUnderlying (productRight l)))
        r (b+rawVariance (weightedUnderlying (productRight l))) δ
        (g+weightedCross (productLeft l)) (y+weightedCross (productRight l))
        (K+weightedVariance (productLeft l)+weightedVariance (productRight l)) := by
  induction l generalizing a b g y K with
  | nil => simp [narrowMiddleSchedule,productLeft,productRight,rawVariance,weightedUnderlying,weightedCross,weightedVariance]
  | cons p l ih =>
    simp only [narrowMiddleSchedule] at ih
    cases p with
    | inl p =>
      simp only [narrowMiddleSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
      change (fun i j => narrowClockPerturbed a b b r b δ g y K i j+
        (![p.2.1,δ*p.2.2,-δ*p.2.2] : Fin 3 → ℝ) i*(![p.2.1,δ*p.2.2,-δ*p.2.2] : Fin 3 → ℝ) j)+_=_
      rw [narrowClockPerturbed_singleton,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawVariance,weightedCross,weightedVariance,List.map_cons,List.sum_cons,add_assoc]
    | inr p =>
      simp only [narrowMiddleSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
      change (fun i j => narrowClockPerturbed a b b r b δ g y K i j+
        (![0,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2] : Fin 3 → ℝ) i*(![0,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2] : Fin 3 → ℝ) j)+_=_
      rw [narrowClockPerturbed_pair,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawVariance,weightedCross,weightedVariance,List.map_cons,List.sum_cons,add_assoc]
      congr 1
      ring

theorem narrowMiddleSchedule_penalty (δ : ℝ) (l : List NarrowMiddleIncrement) (a b r g y K : ℝ) :
    matrixChainPenalty (narrowMiddleSchedule δ l) (narrowClockPerturbed a b b r b δ g y K)=
      rawPenalty (weightedUnderlying (productLeft l)) a+2*rawPenalty (weightedUnderlying (productRight l)) b+
      4*δ^2*weightedCrossPenalty (productLeft l) g+4*δ^2*weightedCrossPenalty (productRight l) y+
      4*δ^4*narrowNoisePenalty l K := by
  induction l generalizing a b g y K with
  | nil => simp [narrowMiddleSchedule,productLeft,productRight,weightedUnderlying,rawPenalty,
      weightedCrossPenalty,narrowNoisePenalty,chainPotentialPenalty]
  | cons p l ih =>
    simp only [narrowMiddleSchedule] at ih
    cases p with
    | inl p =>
      simp only [narrowMiddleSchedule,List.map_cons,matrixChainPenalty_cons]
      have he := narrowClockPerturbed_singleton a b r δ g y K p.2.1 p.2.2
      change narrowClockPerturbed a b b r b δ g y K+rankOneMatrix (narrowMiddleVector δ (.inl p))=_ at he
      rw [he]
      change p.1*(_-_)+_=_
      rw [narrowClockPerturbed_singleton_penalty,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawPenalty,
        weightedCrossPenalty,narrowNoisePenalty,narrowMiddleNoise,productMass,List.map_cons,chainPotentialPenalty]
      ring
    | inr p =>
      simp only [narrowMiddleSchedule,List.map_cons,matrixChainPenalty_cons]
      have he := narrowClockPerturbed_pair a b r δ g y K p.2.1 p.2.2
      change narrowClockPerturbed a b b r b δ g y K+rankOneMatrix (narrowMiddleVector δ (.inr p))=_ at he
      rw [he]
      change p.1/2*(_-_)+_=_
      rw [narrowClockPerturbed_pair_penalty,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawPenalty,
        weightedCrossPenalty,narrowNoisePenalty,narrowMiddleNoise,productMass,List.map_cons,chainPotentialPenalty]
      ring

end SK.Analytic

end
end

end OAI
