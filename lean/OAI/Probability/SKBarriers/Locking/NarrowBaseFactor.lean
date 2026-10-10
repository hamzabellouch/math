import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowRetainedCommon
import OAI.Probability.SKBarriers.Locking.NarrowRetainedExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowRetainedPrefix_value (c v w : List (ℝ × (ℝ × ℝ)))
    (hv : weightedUnderlying v=weightedUnderlying w) {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (narrowRetainedPrefix c v w) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1) 0=
      3*scalarIncrementChain (weightedUnderlying c++weightedUnderlying w) f 0 := by
  rw [narrowRetainedPrefix,vectorIncrementChain_append,narrowRetainedMiddle_value v w hf,hv]
  have H := narrowRetainedCommon_value c (scalarIncrementChain (weightedUnderlying w) f) 0
  simpa only [map_zero,Prod.fst_zero,scalarIncrementChain_append] using H

theorem narrowRetainedPrefix_average (c v w : List (ℝ × (ℝ × ℝ)))
    (hv : weightedUnderlying v=weightedUnderlying w) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {H : ℝ → ℝ} (hH : Continuous H) (hHE : HasExpGrowth H) :
    vectorIncrementAverage (narrowRetainedPrefix c v w) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)
      (fun p => H p.2.1*(p.1.2+p.2.2)^2) 0=
      vectorIncrementAverage c (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) f p.1)
      (fun p =>
        vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) (p.1,0)*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1) p+
        2*(vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2) (p.1,0)*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2) p)+
        vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2^2) p) (0,0) := by
  rw [narrowRetainedPrefix,vectorIncrementAverage_append,narrowRetainedMiddle_value v w hf,hv,
    narrowRetainedMiddle_moment v w hf hH hHE]
  exact narrowRetainedCommon_average c (scalarIncrementChain (weightedUnderlying w) f) _ 0

def narrowBaseQuadratic (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  vectorIncrementAverage (narrowRetainedPrefix c v w) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)
    (fun p => rootHessian 0 f p.2.1*(p.1.2+p.2.2)^2) 0

end SK.Analytic

end
end

end OAI
