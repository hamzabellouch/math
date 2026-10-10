import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowRetainedFactor

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Scale
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorIncrementChain_div_scale (l : List (ℝ × E)) (c : ℝ) (hc : c≠0) (f : E → ℝ) :
    vectorIncrementChain (l.map (fun p => (p.1/c,p.2))) (fun x => c*f x)=
      fun x => c*vectorIncrementChain l f x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementChain,ih,vectorStep_div_scale p.1 c hc]

theorem vectorIncrementAverage_div_scale (l : List (ℝ × E)) (c : ℝ) (hc : c≠0) (f g : E → ℝ) :
    vectorIncrementAverage (l.map (fun p => (p.1/c,p.2))) (fun x => c*f x) g=
      vectorIncrementAverage l f g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementAverage,ih,vectorIncrementChain_div_scale l c hc,
      vectorStepAverage_div_scale p.1 c hc]
end Scale

def narrowCommonEmbedding : (ℝ × ℝ) →L[ℝ] NarrowRetainedState :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))

@[simp] theorem narrowCommonEmbedding_apply (p : ℝ × ℝ) : narrowCommonEmbedding p=((p.1,0),p) := rfl

theorem narrowCommonBase_comp (f : ℝ → ℝ) :
    (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1) ∘ narrowCommonEmbedding=
      fun p => 3*f p.1 := by
  funext p
  simp only [Function.comp_def,narrowCommonEmbedding_apply]
  ring

theorem narrowCommon_image (c : List (ℝ × (ℝ × ℝ))) :
    (c.map (fun p => (p.1/3,p.2))).map (fun p => (p.1,narrowCommonEmbedding p.2))=narrowRetainedCommon c := by
  simp only [List.map_map,narrowRetainedCommon,Function.comp_def,narrowCommonEmbedding_apply,Prod.mk.eta]

theorem narrowRetainedCommon_value (c : List (ℝ × (ℝ × ℝ))) (f : ℝ → ℝ) (p : ℝ × ℝ) :
    vectorIncrementChain (narrowRetainedCommon c) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)
      (narrowCommonEmbedding p)=3*scalarIncrementChain (weightedUnderlying c) f p.1 := by
  have H := congrFun (vectorIncrementChain_pullback narrowCommonEmbedding
    (c.map (fun p => (p.1/3,p.2))) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)) p
  rw [narrowCommonBase_comp,narrowCommon_image,vectorIncrementChain_div_scale c 3 (by norm_num),weightedBranch_value] at H
  exact H.symm

theorem narrowRetainedCommon_average (c : List (ℝ × (ℝ × ℝ))) (f : ℝ → ℝ)
    (g : NarrowRetainedState → ℝ) (p : ℝ × ℝ) :
    vectorIncrementAverage (narrowRetainedCommon c) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1) g
      (narrowCommonEmbedding p)=vectorIncrementAverage c (fun p : ℝ × ℝ => f p.1) (g ∘ narrowCommonEmbedding) p := by
  have H := congrFun (vectorIncrementAverage_pullback narrowCommonEmbedding
    (c.map (fun p => (p.1/3,p.2))) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1) g) p
  rw [narrowCommonBase_comp,narrowCommon_image,vectorIncrementAverage_div_scale c 3 (by norm_num)] at H
  exact H.symm

end SK.Analytic

end
end

end OAI
