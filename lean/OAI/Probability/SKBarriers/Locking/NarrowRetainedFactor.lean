import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleBaseFactor
import OAI.Probability.SKBarriers.Scalar.VectorAverageAlgebra
import OAI.Probability.SKBarriers.Locking.NarrowSchedule

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

abbrev NarrowRetainedState := (ℝ × ℝ) × (ℝ × ℝ)

def narrowRetainedCommon (c : List (ℝ × (ℝ × ℝ))) : List (ℝ × NarrowRetainedState) :=
  c.map (fun p => (p.1/3,((p.2.1,0),(p.2.1,p.2.2))))

def narrowRetainedMiddle (l : List NarrowMiddleIncrement) : List (ℝ × NarrowRetainedState) :=
  l.map (fun p => (productMass p,productVector p))

theorem narrowRetainedMiddle_value (v w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (narrowRetainedMiddle (mergedProductBranches v w))
      (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)=
      fun p => scalarIncrementChain (weightedUnderlying v) f p.1.1+
        2*scalarIncrementChain (weightedUnderlying w) f p.2.1 := by
  have hF : BoundedDerivs (fun p : ℝ × ℝ => f p.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  change productBranchChain _ (fun p => (fun q : ℝ × ℝ => f q.1) p.1+2*(fun q : ℝ × ℝ => f q.1) p.2)=_
  rw [productBranchChain_factor _ hF hF,mergedProductBranches_left,mergedProductBranches_right,
    weightedBranch_value,weightedBranch_value]

theorem narrowRetainedMiddle_moment (v w : List (ℝ × (ℝ × ℝ)))
    {f H : ℝ → ℝ} (hf : BoundedDerivs f) (hH : Continuous H) (hHE : HasExpGrowth H) :
    vectorIncrementAverage (narrowRetainedMiddle (mergedProductBranches v w))
      (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)
      (fun p => H p.2.1*(p.1.2+p.2.2)^2)=
      fun p =>
        vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) p.1*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1) p.2+
        2*(vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2) p.1*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2) p.2)+
        vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2^2) p.2 := by
  let A : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))
  let B : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))
  let X : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))
  let V : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))
  let L := narrowRetainedMiddle (mergedProductBranches v w)
  let F := fun p : NarrowRetainedState => f p.1.1+2*f p.2.1
  have hF : BoundedDerivs F := (hf.compCLM V).add ((hf.compCLM X).const_mul 2)
  have hc1 : Continuous (fun p : NarrowRetainedState => p.1.2^2*H p.2.1) := (A.continuous.pow 2).mul (hH.comp X.continuous)
  have he1 : HasExpGrowth (fun p : NarrowRetainedState => p.1.2^2*H p.2.1) := ((HasExpGrowth.linear A).pow 2).mul (hHE.compCLM X)
  have hc2 : Continuous (fun p : NarrowRetainedState => p.1.2*(H p.2.1*p.2.2)) := A.continuous.mul ((hH.comp X.continuous).mul B.continuous)
  have he2 : HasExpGrowth (fun p : NarrowRetainedState => p.1.2*(H p.2.1*p.2.2)) := (HasExpGrowth.linear A).mul ((hHE.compCLM X).mul (HasExpGrowth.linear B))
  have hc3 : Continuous (fun p : NarrowRetainedState => H p.2.1*p.2.2^2) := (hH.comp X.continuous).mul (B.continuous.pow 2)
  have he3 : HasExpGrowth (fun p : NarrowRetainedState => H p.2.1*p.2.2^2) := (hHE.compCLM X).mul ((HasExpGrowth.linear B).pow 2)
  have he : (fun p : NarrowRetainedState => H p.2.1*(p.1.2+p.2.2)^2)=
      fun p => (p.1.2^2*H p.2.1+2*(p.1.2*(H p.2.1*p.2.2)))+H p.2.1*p.2.2^2 := by funext p; ring
  have hc2m : Continuous (fun p : NarrowRetainedState => 2*(p.1.2*(H p.2.1*p.2.2))) := hc2.const_mul 2
  have he2m : HasExpGrowth (fun p : NarrowRetainedState => 2*(p.1.2*(H p.2.1*p.2.2))) := (HasExpGrowth.const 2).mul he2
  have hc12 : Continuous (fun p : NarrowRetainedState => p.1.2^2*H p.2.1+2*(p.1.2*(H p.2.1*p.2.2))) := hc1.add hc2m
  have he12 : HasExpGrowth (fun p : NarrowRetainedState => p.1.2^2*H p.2.1+2*(p.1.2*(H p.2.1*p.2.2))) := he1.add he2m
  rw [he,vectorIncrementAverage_add L hF hc12 hc3 he12 he3,
    vectorIncrementAverage_add L hF hc1 hc2m he1 he2m,
    vectorIncrementAverage_const_mul]
  have hsf : BoundedDerivs (fun p : ℝ × ℝ => f p.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hfac (a b : ℝ × ℝ → ℝ) := productBranchAverage_factor (mergedProductBranches v w) hsf hsf a b
  simp only [mergedProductBranches_left,mergedProductBranches_right] at hfac
  have hfac3 := hfac (fun _ => 1) (fun q => H q.1*q.2^2)
  simp only [one_mul,vectorIncrementAverage_const v hsf 1] at hfac3
  change (fun p => (productBranchAverage (mergedProductBranches v w) F (fun p : NarrowRetainedState => p.1.2^2*H p.2.1) p+
    2*productBranchAverage (mergedProductBranches v w) F (fun p : NarrowRetainedState => p.1.2*(H p.2.1*p.2.2)) p)+
    productBranchAverage (mergedProductBranches v w) F (fun p : NarrowRetainedState => H p.2.1*p.2.2^2) p)=_
  dsimp only [F]
  rw [hfac (fun q => q.2^2) (fun q => H q.1),hfac (fun q => q.2) (fun q => H q.1*q.2),hfac3]

end SK.Analytic

end
end

end OAI
