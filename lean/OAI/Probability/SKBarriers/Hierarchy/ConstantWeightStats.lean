import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedListBridge
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats
import OAI.Probability.SKBarriers.Replicas.TripleScheduleScale

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def constantWeightChain (κ : ℝ) (l : List (ℝ × ℝ)) : List (ℝ × (ℝ × ℝ)) := l.map (fun p => (p.1,(p.2,κ*p.2)))

@[simp] theorem constantWeightChain_underlying (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedUnderlying (constantWeightChain κ l)=l := by
  simp only [weightedUnderlying,constantWeightChain,List.map_map,Function.comp_def,Prod.mk.eta]
  exact List.map_id _

@[simp] theorem constantWeightChain_variance (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedVariance (constantWeightChain κ l)=κ^2*rawVariance l := by
  induction l with
  | nil => simp [weightedVariance,rawVariance,constantWeightChain]
  | cons p l ih =>
    change (κ*p.2)^2+weightedVariance (constantWeightChain κ l)=κ^2*(p.2^2+rawVariance l)
    rw [ih]; ring

@[simp] theorem constantWeightChain_cross (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedCross (constantWeightChain κ l)=κ*rawVariance l := by
  induction l with
  | nil => simp [weightedCross,rawVariance,constantWeightChain]
  | cons p l ih =>
    change p.2*(κ*p.2)+weightedCross (constantWeightChain κ l)=κ*(p.2^2+rawVariance l)
    rw [ih]; ring

@[simp] theorem constantWeightChain_absCross (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedAbsCross (constantWeightChain κ l)=|κ| *rawVariance l := by
  induction l with
  | nil => simp [weightedAbsCross,rawVariance,constantWeightChain]
  | cons p l ih =>
    change |κ*p.2| * |p.2|+weightedAbsCross (constantWeightChain κ l)=|κ| *(p.2^2+rawVariance l)
    rw [abs_mul,ih,mul_assoc,show |p.2| * |p.2|=p.2^2 by rw [← sq,sq_abs]]
    ring

theorem constantWeightChain_penalty (κ : ℝ) (l : List (ℝ × ℝ)) (q : ℝ) :
    weightedCrossPenalty (constantWeightChain κ l) (κ*q)=κ^2*rawPenalty l q := by
  induction l generalizing q with
  | nil => simp [weightedCrossPenalty,rawPenalty,constantWeightChain,chainPotentialPenalty]
  | cons p l ih =>
    change p.1*((κ*q+p.2*(κ*p.2))^2-(κ*q)^2)+weightedCrossPenalty (constantWeightChain κ l) (κ*q+p.2*(κ*p.2))=
      κ^2*(p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2))
    rw [show κ*q+p.2*(κ*p.2)=κ*(q+p.2^2) by ring,ih]
    ring

@[simp] theorem constantWeightChain_penalty_zero (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedCrossPenalty (constantWeightChain κ l) 0=κ^2*rawPenalty l 0 := by
  simpa only [mul_zero] using constantWeightChain_penalty κ l 0

@[simp] theorem zeroWeightChain_append (l r : List (ℝ × ℝ)) : zeroWeightChain (l++r)=zeroWeightChain l++zeroWeightChain r := by
  simp only [zeroWeightChain,List.map_append]

@[simp] theorem weightedAbsCross_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedAbsCross (l++r)=weightedAbsCross l+weightedAbsCross r := by
  simp only [weightedAbsCross,List.map_append,List.sum_append]

@[simp] theorem weightedAbsCross_zeroWeight (l : List (ℝ × ℝ)) : weightedAbsCross (zeroWeightChain l)=0 := by
  simp [weightedAbsCross,zeroWeightChain,List.map_map,Function.comp_def]

@[simp] theorem zeroWeightChain_scale (β : ℝ) (l : List (ℝ × ℝ)) : scaleIncrementChain β (zeroWeightChain l)=zeroWeightChain (scaleIncrementChain β l) := by
  simp only [scaleIncrementChain,zeroWeightChain,List.map_map,Function.comp_def,Prod.smul_mk,smul_zero]

@[simp] theorem constantWeightChain_scale (β κ : ℝ) (l : List (ℝ × ℝ)) :
    scaleIncrementChain β (constantWeightChain κ l)=constantWeightChain κ (scaleIncrementChain β l) := by
  simp only [scaleIncrementChain,constantWeightChain,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  change β*(κ*p.2)=κ*(β*p.2)
  ring

theorem rawVariance_nonneg (l : List (ℝ × ℝ)) : 0 ≤ rawVariance l := by
  exact List.sum_nonneg (by intro a ha; obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha; exact sq_nonneg _)

theorem rawPenalty_bounds (l : List (ℝ × ℝ)) {a b q : ℝ}
    (hm : ∀ p∈l,p.1∈Icc a b) (hq : 0 ≤ q) :
    rawPenalty l q∈Icc (a*((q+rawVariance l)^2-q^2)) (b*((q+rawVariance l)^2-q^2)) := by
  induction l generalizing q with
  | nil => simp [rawPenalty,rawVariance,chainPotentialPenalty]
  | cons p l ih =>
    have hp := hm p (List.mem_cons_self ..)
    have H := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz)) (q:=q+p.2^2) (by positivity)
    have hΔ : 0 ≤ (q+p.2^2)^2-q^2 := by nlinarith [sq_nonneg p.2]
    change p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2)∈
      Icc (a*((q+(p.2^2+rawVariance l))^2-q^2)) (b*((q+(p.2^2+rawVariance l))^2-q^2))
    constructor
    · have H' := add_le_add (mul_le_mul_of_nonneg_right hp.1 hΔ) H.1
      convert H' using 1
      ring
    · have H' := add_le_add (mul_le_mul_of_nonneg_right hp.2 hΔ) H.2
      convert H' using 1
      ring

end SK.Analytic

end
end

end OAI
