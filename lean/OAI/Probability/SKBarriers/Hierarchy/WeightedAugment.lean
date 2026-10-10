import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedListBridge
import OAI.Probability.SKBarriers.Hierarchy.WeightedListResponse

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem weightedVariance_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedVariance (l++r)=weightedVariance l+weightedVariance r := by
  simp [weightedVariance,List.sum_append]

@[simp] theorem weightedCross_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedCross (l++r)=weightedCross l+weightedCross r := by
  simp [weightedCross,List.sum_append]

@[simp] theorem weightedVariance_zeroWeight (l : List (ℝ × ℝ)) : weightedVariance (zeroWeightChain l)=0 := by
  simp [weightedVariance,zeroWeightChain,List.map_map,Function.comp_def]

@[simp] theorem weightedCross_zeroWeight (l : List (ℝ × ℝ)) : weightedCross (zeroWeightChain l)=0 := by
  simp [weightedCross,zeroWeightChain,List.map_map,Function.comp_def]

theorem weightedCrossPenalty_append (l r : List (ℝ × (ℝ × ℝ))) (g : ℝ) :
    weightedCrossPenalty (l++r) g=weightedCrossPenalty l g+weightedCrossPenalty r (g+weightedCross l) := by
  simp only [weightedCrossPenalty,List.map_append,chainPotentialPenalty_append,chainSum,
    List.map_map,weightedCross,Function.comp_def]

@[simp] theorem weightedCrossPenalty_zeroWeight (l : List (ℝ × ℝ)) (g : ℝ) :
    weightedCrossPenalty (zeroWeightChain l) g=0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change p.1*((g+p.2*0)^2-g^2)+weightedCrossPenalty (zeroWeightChain l) (g+p.2*0)=0
    simp only [mul_zero,add_zero,sub_self,ih]

@[simp] theorem weightedVariance_full (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    weightedVariance (zeroWeightChain c++w++zeroWeightChain t)=weightedVariance w := by simp

@[simp] theorem weightedCrossPenalty_full (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    weightedCrossPenalty (zeroWeightChain c++w++zeroWeightChain t) 0=weightedCrossPenalty w 0 := by
  simp [weightedCrossPenalty_append]

theorem weighted_mass_iff (w : List (ℝ × (ℝ × ℝ))) {P : ℝ → Prop} :
    (∀ p∈w,P p.1) ↔ ∀ p∈weightedUnderlying w,P p.1 := by
  constructor
  · intro H p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact H q hq
  · intro H p hp; exact H _ (List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem weighted_sorted_iff (w : List (ℝ × (ℝ × ℝ))) :
    w.Pairwise (fun p q => p.1≤q.1) ↔ (weightedUnderlying w).Pairwise (fun p q => p.1≤q.1) := by
  simp only [weightedUnderlying,List.pairwise_map]

theorem weightedFull_spin_early_le (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (k : Fin (zeroWeightChain c++w++zeroWeightChain t).length → ℝ) (hk : ∀ i,0≤k i)
    (he : ∀ i,((zeroWeightChain c++w++zeroWeightChain t).get i).2.2=
      k i*((zeroWeightChain c++w++zeroWeightChain t).get i).2.1)
    {V : ℝ} (hV : 0≤V)
    (hactive : ∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain c++w++zeroWeightChain t).length
      (fun j => ((zeroWeightChain c++w++zeroWeightChain t).get j).2.1) i.castSucc≤V) :
    vectorIncrementAverage (zeroWeightChain c++w++zeroWeightChain t)
      (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)≤
      weightedVariance w+(rootHessian 0 (scalarIncrementChain (c++weightedUnderlying w++t) scalarSpinTerminal) 0+
        (2*V+4*V^2))*weightedCrossPenalty w 0 := by
  have H := weightedList_spin_early_le (zeroWeightChain c++w++zeroWeightChain t) k
    ((weighted_mass_iff _).mpr (by simpa using hm))
    ((weighted_sorted_iff _).mpr (by simpa using hs)) hk he hV hactive
  simpa only [weightedUnderlying_append,weightedUnderlying_zeroWeight,weightedVariance_full,
    weightedCrossPenalty_full] using H

end SK.Analytic

end
end

end OAI
