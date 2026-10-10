import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarListBounds
import OAI.Probability.SKBarriers.Hierarchy.WeightedListMean
import OAI.Probability.SKBarriers.Hierarchy.WeightedRampBridge
import OAI.Probability.SKBarriers.Scalar.VectorAverageProduct
import OAI.Probability.SKBarriers.Locking.NarrowBaseFactor

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowSusceptibility (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  vectorIncrementAverage c (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) f p.1)
    (vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1)) (0,0)

def narrowMixedMoment (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  vectorIncrementAverage c (fun p : ℝ × ℝ => F p.1)
    (fun p => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1*p.2) p*rootGradient 0 F p.1) (0,0)

def narrowJointMoment (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  vectorIncrementAverage c (fun p : ℝ × ℝ => F p.1)
    (fun p => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1) p*rootHessian 0 F p.1) (0,0)

def narrowTentSquare (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  vectorIncrementAverage c (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) f p.1)
    (vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1*p.2^2)) (0,0)

theorem narrowSusceptibility_eq (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    narrowSusceptibility c w t=scalarIncrementAverage (weightedUnderlying (c++w))
      (scalarIncrementChain t scalarSpinTerminal) (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) 0 := by
  dsimp only [narrowSusceptibility]
  rw [weightedBranch_average,weightedBranch_average,weightedUnderlying_append,scalarIncrementAverage_append]

theorem narrowSusceptibility_abs_le (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈t,p.1∈Icc (0:ℝ) 1) : |narrowSusceptibility c w t| ≤ 1 := by
  rw [narrowSusceptibility_eq]
  exact scalarIncrementAverage_abs_le _ (scalarIncrementChain_regular t scalarSpinTerminal_regular)
    (fun x => ((scalarIncrementChain_spin_convex t hm).bounds x).2) 0

theorem narrowBaseQuadratic_ramp_le (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (ht : ∀ p∈t,p.1∈Icc (0:ℝ) 1)
    (hmv : ∀ p∈v,p.1∈Icc (0:ℝ) 1) (hsv : v.Pairwise (fun p q => p.1 ≤ q.1))
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ j,|scalarLevelField v.length (fun i => (v.get i).2.1) j
      (coordinateVector v.length (fun i => (v.get i).2.2))| ≤ B) :
    narrowBaseQuadratic c v w t ≤ weightedVariance v*narrowSusceptibility c w t+6*B^2+
      2*weightedMean v*narrowMixedMoment c w t+narrowTentSquare c w t := by
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  have hf : BoundedDerivs f := scalarIncrementChain_regular t scalarSpinTerminal_regular
  have hspin : ScalarSpinConvex f := scalarIncrementChain_spin_convex t ht
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ hf
  let P : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let Z : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := P.prod 0
  let R : ℝ × ℝ → ℝ := fun p => vectorIncrementAverage v (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (p.1,0)
  let C : ℝ × ℝ → ℝ := vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1)
  let D : ℝ × ℝ → ℝ := fun p => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1)
    (fun p => rootHessian 0 f p.1*p.2) p*rootGradient 0 F p.1
  let T : ℝ × ℝ → ℝ := vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1*p.2^2)
  have hχ : HasExpGrowth (rootHessian 0 f) := HasExpGrowth.of_bounded zero_le_one
    (fun x => by simpa only [Real.norm_eq_abs] using (hspin.bounds x).2)
  have hχc : Continuous (fun p : ℝ × ℝ => rootHessian 0 f p.1) := (rootHessian_continuous 0 hf).comp continuous_fst
  have hχE := hχ.compCLM P
  have hR' := vectorIncrementAverage_regular v (hf.compCLM P)
    (g:=fun p : ℝ × ℝ => p.2^2) (continuous_snd.pow 2)
    ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2)
  have hR : Continuous R ∧ HasExpGrowth R := ⟨hR'.1.comp Z.continuous,hR'.2.compCLM Z⟩
  have hC : Continuous C ∧ HasExpGrowth C := vectorIncrementAverage_regular w (hf.compCLM P) hχc hχE
  have hT : Continuous T ∧ HasExpGrowth T := vectorIncrementAverage_regular w (hf.compCLM P)
    (hχc.mul (continuous_snd.pow 2)) (hχE.mul ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2))
  have hD' := vectorIncrementAverage_regular w (hf.compCLM P)
    (g:=fun p : ℝ × ℝ => rootHessian 0 f p.1*p.2) (hχc.mul continuous_snd)
    (hχE.mul (HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)))
  have hfull : ∀ p∈weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1 := by
    intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · rw [← hv] at hp
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
      exact hmv z hz
    · exact ht p hp
  have hFspin : ScalarSpinConvex F := by
    dsimp only [F,f]
    rw [← scalarIncrementChain_append]
    exact scalarIncrementChain_spin_convex _ hfull
  have hU : HasExpGrowth (rootGradient 0 F) := HasExpGrowth.of_bounded zero_le_one
    (fun x => by simpa only [Real.norm_eq_abs] using (hFspin.bounds x).1)
  have hD : Continuous D ∧ HasExpGrowth D := ⟨hD'.1.mul ((rootGradient_continuous 0 hF).comp continuous_fst),hD'.2.mul (hU.compCLM P)⟩
  have hC0 (p : ℝ × ℝ) : 0 ≤ C p := by
    dsimp only [C]
    rw [weightedBranch_average]
    exact scalarIncrementAverage_nonneg _ hf (hspin.hessian_bounded hf) (fun x => (hspin x).1) p.1
  have hRle (p : ℝ × ℝ) : R p ≤ weightedVariance v+6*B^2 := by
    have H := (abs_le.mp (weightedList_ramp_square_error v hmv hsv hf hspin hB hprefix p.1)).2
    dsimp only [R]; linarith
  have H := vectorIncrementAverage_product_plus_le c (hf:=hF.compCLM P) hR.1 hC.1 hD.1 hT.1
    hR.2 hC.2 hD.2 hT.2 hRle hC0 (2*weightedMean v) (0,0)
  have hM (x : ℝ) : vectorIncrementAverage v (fun p : ℝ × ℝ => f p.1) (fun p => p.2) (x,0)=weightedMean v*rootGradient 0 F x := by
    rw [weightedList_tail_mean,hv,scalarIncrementChain_append]
    rfl
  have HQ : narrowBaseQuadratic c v w t=vectorIncrementAverage c (fun p : ℝ × ℝ => F p.1)
      (fun p => R p*C p+(2*weightedMean v)*D p+T p) (0,0) := by
    rw [narrowBaseQuadratic,narrowRetainedPrefix_average c v w hv hf (rootHessian_continuous 0 hf) hχ]
    congr 2
    funext p
    rw [hM]
    dsimp only [R,C,D,T]
    ring
  rw [HQ]
  have Hs := (abs_le.mp (narrowSusceptibility_abs_le c w t ht)).2
  change _ ≤ (weightedVariance v+6*B^2)*narrowSusceptibility c w t+
    2*weightedMean v*narrowMixedMoment c w t+narrowTentSquare c w t at H
  exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left Hs (show 0 ≤ 6*B^2 by positivity)])

end SK.Analytic

end
end

end OAI
