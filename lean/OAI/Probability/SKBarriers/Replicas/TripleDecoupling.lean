import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedListBridge
import OAI.Probability.SKBarriers.Hierarchy.RootCovariance
import OAI.Probability.SKBarriers.Scalar.ScalarListBounds
import OAI.Probability.SKBarriers.Replicas.TripleFiniteExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleSusceptibility (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  scalarIncrementAverage (c++weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)
    (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) 0

def tripleCommonError (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) : ℝ :=
  2*weightedMomentBound w*((susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2)*
    Real.sqrt (2*rawVariance c+4*(rawVariance c)^2)

theorem tripleBaseQuadratic_decoupling (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1)) :
    |tripleBaseQuadratic c w t-tripleSusceptibility c w t*
      vectorIncrementAverage (zeroWeightChain c++w++zeroWeightChain t)
        (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)|≤tripleCommonError c w := by
  have hmc : ∀ p∈c,p.1∈Icc (0:ℝ) 1 := fun p hp => hm p (List.mem_append_left _ (List.mem_append_left _ hp))
  have hmw : ∀ p∈weightedUnderlying w,p.1∈Icc (0:ℝ) 1 := fun p hp => hm p (List.mem_append_left _ (List.mem_append_right _ hp))
  have hmt : ∀ p∈t,p.1∈Icc (0:ℝ) 1 := fun p hp => hm p (List.mem_append_right _ hp)
  have hs0 := List.pairwise_append.mp hs
  have hs1 := List.pairwise_append.mp hs0.1
  have hww : ∀ p∈w,p.1∈Icc (0:ℝ) 1 := fun p hp => hmw _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hsw : w.Pairwise (fun p q => p.1≤q.1) := by
    simpa only [weightedUnderlying,List.pairwise_map] using hs1.2.1
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  let A := scalarIncrementAverage (weightedUnderlying w) f (rootHessian 0 f)
  let B := fun x => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)
  have hf : BoundedDerivs f := scalarIncrementChain_regular _ scalarSpinTerminal_regular
  have hfL : LipschitzWith 1 f := scalarIncrementChain_lipschitz t (fun p hp => (hmt p hp).1)
    scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ hf
  have hFL : LipschitzWith 1 F := scalarIncrementChain_lipschitz _ (fun p hp => (hmw p hp).1) hf hfL
  have hfc : ScalarSpinConvex f := scalarIncrementChain_spin_convex t hmt
  have hA : BoundedScalar A := scalarIncrementAverage_bounded _ hf (hfc.hessian_bounded hf)
  have hB : BoundedScalar B := weightedAverage_bounded w hww hsw hf hfL
  have hAL (x : ℝ) : |A x-A 0|≤((susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2)*|x| := by
    have H := scalarHierarchyAverage_spatial_bound (weightedUnderlying w).length
      (fun i => ((weightedUnderlying w).get i).1) (fun i => ((weightedUnderlying w).get i).2)
      (fun i => hmw _ (List.get_mem _ i)) (mass_get_monotone hs1.2.1) hf hfL
      (scalarIncrementChain_hessian_lipschitz t hmt hs0.2.1) (C:=1) (fun z => (hfc.bounds z).2) x 0
    simpa only [← scalarIncrementAverage_get,NNReal.coe_one,mul_one,sub_zero,A] using H
  have H := scalarHierarchyAverage_covariance_small c.length (fun i => (c.get i).1) (fun i => (c.get i).2)
    (fun i => hmc _ (List.get_mem c i)) (mass_get_monotone hs1.1) hF hFL hA hB
    (weightedMomentBound_nonneg w) (show 0≤(susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2 by positivity)
    (weightedAverage_abs_le w hww hsw hf hfL) hAL
  rw [sum_get_map c (fun p => p.2^2)] at H
  simp only [← scalarIncrementAverage_get] at H
  rw [weightedFull_average c w t scalarSpinTerminal_regular]
  unfold tripleBaseQuadratic tripleSusceptibility tripleCommonError
  rw [scalarIncrementAverage_append]
  simpa only [A,B,F,f,rawVariance,mul_comm] using H

end SK.Analytic

end
end

end OAI
