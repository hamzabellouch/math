import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedAugment
import OAI.Probability.SKBarriers.Locking.NarrowRetainedStats
import OAI.Probability.SKBarriers.Locking.NarrowMomentBound

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowTentSquare_eq (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    narrowTentSquare c w t=vectorIncrementAverage (c++w)
      (fun p : ℝ × ℝ => scalarIncrementChain t scalarSpinTerminal p.1)
      (fun p => p.2^2*rootHessian 0 (scalarIncrementChain t scalarSpinTerminal) p.1) (0,0) := by
  dsimp only [narrowTentSquare]
  rw [vectorIncrementAverage_append,weightedBranch_value]
  congr 3
  funext p
  ring

theorem narrowBaseQuadratic_tent_le (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈c++w,p.1∈Icc (0:ℝ) 1) (hs : (c++w).Pairwise (fun p q => p.1 ≤ q.1))
    (ht : ∀ p∈t,p.1∈Icc (0:ℝ) 1) (hst : t.Pairwise (fun p q => p.1 ≤ q.1))
    (hmv : ∀ p∈v,p.1∈Icc (0:ℝ) 1) (hsv : v.Pairwise (fun p q => p.1 ≤ q.1))
    (hmean : 0 ≤ weightedMean v)
    (l s : Fin ((c++w).length+1))
    (hlr : l ≤ ⟨c.length,by simp only [List.length_append]; omega⟩)
    (hrs : (⟨c.length,by simp only [List.length_append]; omega⟩ : Fin ((c++w).length+1)) ≤ s)
    {h B R : ℝ} (hh : 0<h) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hleft : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
      ⟨c.length,by simp only [List.length_append]; omega⟩-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) l=B*h)
    (hright : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) s-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
        ⟨c.length,by simp only [List.length_append]; omega⟩=B*h)
    (ha : (fun i => ((c++w).get i).2.2)=scalarTentVector (c++w).length
      (fun i => ((c++w).get i).2.1) l ⟨c.length,by simp only [List.length_append]; omega⟩ s h)
    (hprefix : ∀ j,|scalarLevelField v.length (fun i => (v.get i).2.1) j
      (coordinateVector v.length (fun i => (v.get i).2.2))| ≤ R) :
    narrowBaseQuadratic c v w t ≤ narrowVariance c v w*narrowSusceptibility c w t+
      2*weightedMean v*B*narrowJointMoment c w t+6*R^2+
      2*weightedMean v*B*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s+
      (B*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s)^2+
      B^2*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s := by
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  have hf : BoundedDerivs f := scalarIncrementChain_regular t scalarSpinTerminal_regular
  have hspin : ScalarSpinConvex f := scalarIncrementChain_spin_convex t ht
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ hf
  have hFspin : ScalarSpinConvex F := by
    dsimp only [F,f]
    rw [← scalarIncrementChain_append]
    apply scalarIncrementChain_spin_convex
    intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
      exact hm z (List.mem_append_right _ hz)
    · exact ht p hp
  have hχL := scalarIncrementChain_hessian_lipschitz t ht hst
  have hχb : ∀ y,|rootHessian 0 f y| ≤ 1 := fun y => (hspin.bounds y).2
  have HM := weightedSplit_tent_mixed_error c w hm hs hf hspin hF hFspin l s hlr hrs hh hB hleft hright ha hχL hχb 0
  change |narrowMixedMoment c w t-B*narrowJointMoment c w t| ≤ _ at HM
  have HT := weightedList_tent_square_error (c++w) hm hs hf hspin l
    ⟨c.length,by simp only [List.length_append]; omega⟩ s hlr hrs hh hB hleft hright ha hχL hχb 0
  rw [← narrowTentSquare_eq,← narrowSusceptibility_eq] at HT
  have HQ := narrowBaseQuadratic_ramp_le c v w t hv ht hmv hsv hR hprefix
  have HM' := mul_le_mul_of_nonneg_left (abs_le.mp HM).2 (show 0 ≤ 2*weightedMean v by positivity)
  have HT' := (abs_le.mp HT).2
  have HV : narrowVariance c v w=weightedVariance v+weightedVariance (c++w) := by
    rw [weightedVariance_append]
    unfold narrowVariance
    ring
  rw [HV]
  nlinarith

end SK.Analytic

end
end

end OAI
