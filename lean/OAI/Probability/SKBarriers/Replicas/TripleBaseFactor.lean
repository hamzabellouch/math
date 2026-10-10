import Mathlib
import OAI.Probability.SKBarriers.Replicas.ProductMerge
import OAI.Probability.SKBarriers.Replicas.TripleRetained
import OAI.Probability.SKBarriers.Hierarchy.IncrementListAnalytic

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem list_commonBranch_value (c : List (ℝ × ℝ)) (f : ℝ → ℝ) (x : ℝ) :
    vectorIncrementChain (tripleRetainedCommon c)
      (fun p : TripleRetainedState => f p.1.1+2*f p.2) ((x,0),x)=3*scalarIncrementChain c f x := by
  have H := commonBranch_value c.length (fun i => (c.get i).1) (fun i => (c.get i).2) f x
  rw [← vectorIncrementChain_ofFn,← scalarIncrementChain_ofFn] at H
  have h1 : List.ofFn (fun i : Fin c.length => ((c.get i).1/3,(((c.get i).2,0),(c.get i).2)))=
      tripleRetainedCommon c := by
    unfold tripleRetainedCommon
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f:=c.get) (g:=fun p : ℝ × ℝ => (p.1/3,((p.2,0),p.2)))).symm
  simpa only [h1,Prod.mk.eta,List.ofFn_get] using H

theorem list_commonBranch_average (c : List (ℝ × ℝ)) (f b : ℝ → ℝ) (a : ℝ × ℝ → ℝ) (x : ℝ) :
    vectorIncrementAverage (tripleRetainedCommon c)
      (fun p : TripleRetainedState => f p.1.1+2*f p.2) (fun p => a p.1*b p.2) ((x,0),x)=
      scalarIncrementAverage c f (fun y => a (y,0)*b y) x := by
  have H := commonBranch_average c.length (fun i => (c.get i).1) (fun i => (c.get i).2) f b a x
  rw [← vectorIncrementAverage_ofFn,← scalarIncrementAverage_ofFn] at H
  have h1 : List.ofFn (fun i : Fin c.length => ((c.get i).1/3,(((c.get i).2,0),(c.get i).2)))=
      tripleRetainedCommon c := by
    unfold tripleRetainedCommon
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f:=c.get) (g:=fun p : ℝ × ℝ => (p.1/3,((p.2,0),p.2)))).symm
  simpa only [h1,Prod.mk.eta,List.ofFn_get] using H

theorem weightedBranch_value (w : List (ℝ × (ℝ × ℝ))) (f : ℝ → ℝ) :
    vectorIncrementChain w (fun p : ℝ × ℝ => f p.1)=fun p => scalarIncrementChain (weightedUnderlying w) f p.1 := by
  have H := vectorIncrementChain_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w f
  rw [vectorIncrementChain_real] at H
  exact H

theorem tripleRetainedMiddle_value (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (tripleRetainedMiddle (mergedProductBranches w (weightedUnderlying w)))
      (fun p : TripleRetainedState => f p.1.1+2*f p.2)=
      fun p => scalarIncrementChain (weightedUnderlying w) f p.1.1+2*scalarIncrementChain (weightedUnderlying w) f p.2 := by
  have hF : BoundedDerivs (fun q : ℝ × ℝ => f q.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  change productBranchChain _ (fun p => (fun q : ℝ × ℝ => f q.1) p.1+2*f p.2)=_
  rw [productBranchChain_factor _ hF hf,
    mergedProductBranches_left,mergedProductBranches_right,weightedBranch_value,vectorIncrementChain_real]

theorem tripleRetainedMiddle_average (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) :
    vectorIncrementAverage (tripleRetainedMiddle (mergedProductBranches w (weightedUnderlying w)))
      (fun p : TripleRetainedState => f p.1.1+2*f p.2) (fun p => g p.2*p.1.2^2)=
      fun p => vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) p.1*
        scalarIncrementAverage (weightedUnderlying w) f g p.2 := by
  have he : (fun p : TripleRetainedState => g p.2*p.1.2^2)=fun p => p.1.2^2*g p.2 := by funext p; ring
  rw [he]
  have hF : BoundedDerivs (fun q : ℝ × ℝ => f q.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  change productBranchAverage _ (fun p => (fun q : ℝ × ℝ => f q.1) p.1+2*f p.2) (fun p => (fun q : ℝ × ℝ => q.2^2) p.1*g p.2)=_
  rw [productBranchAverage_factor _ hF hf (fun q : ℝ × ℝ => q.2^2) g,
    mergedProductBranches_left,mergedProductBranches_right,vectorIncrementAverage_real]

def tripleRetainedPrefix (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) : List (ℝ × TripleRetainedState) :=
  tripleRetainedCommon c++tripleRetainedMiddle (mergedProductBranches w (weightedUnderlying w))

theorem tripleRetainedPrefix_value (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (tripleRetainedPrefix c w) (fun p => f p.1.1+2*f p.2) 0=
      3*scalarIncrementChain (c++weightedUnderlying w) f 0 := by
  rw [tripleRetainedPrefix,vectorIncrementChain_append,tripleRetainedMiddle_value w hf,scalarIncrementChain_append]
  exact list_commonBranch_value c _ 0

theorem tripleRetainedPrefix_average (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) :
    vectorIncrementAverage (tripleRetainedPrefix c w) (fun p => f p.1.1+2*f p.2) (fun p => g p.2*p.1.2^2) 0=
      scalarIncrementAverage c (scalarIncrementChain (weightedUnderlying w) f)
        (fun x => vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) (x,0)*
          scalarIncrementAverage (weightedUnderlying w) f g x) 0 := by
  rw [tripleRetainedPrefix,vectorIncrementAverage_append,tripleRetainedMiddle_value w hf,
    tripleRetainedMiddle_average w hf g]
  exact list_commonBranch_average c _ _ _ 0

end SK.Analytic

end
end

end OAI
