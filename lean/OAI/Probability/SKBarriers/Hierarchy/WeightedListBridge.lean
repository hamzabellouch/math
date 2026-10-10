import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleBaseFactor

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStepAverage_frozen {f : E → ℝ} (hf : BoundedDerivs f) (g : E → ℝ)
    (m : ℝ) (v : E) (hi : ∀ x (s : ℝ),g (x+s • v)=g x) :
    vectorStepAverage m v f g=g := by
  unfold vectorStepAverage
  have he : (fun z : E × ℝ => g (z.1+z.2 • v))=fun z => g z.1 := funext (fun z => hi z.1 z.2)
  rw [he]
  have hF : BoundedDerivs (fun z : E × ℝ => f (z.1+z.2 • v)) := hf.compCLM (vectorTranslation v)
  exact gaussianAverage_const_prefix hF m g
end Vector

def zeroWeightChain (l : List (ℝ × ℝ)) : List (ℝ × (ℝ × ℝ)) := l.map (fun p => (p.1,(p.2,0)))

def zeroNoiseEmbedding : ℝ →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.id ℝ ℝ).prod 0

@[simp] theorem zeroNoiseEmbedding_apply (x : ℝ) : zeroNoiseEmbedding x=(x,0) := rfl

@[simp] theorem weightedUnderlying_zeroWeight (l : List (ℝ × ℝ)) : weightedUnderlying (zeroWeightChain l)=l := by
  simp only [weightedUnderlying,zeroWeightChain,List.map_map,Function.comp_def,Prod.mk.eta]
  exact List.map_id _

@[simp] theorem weightedUnderlying_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedUnderlying (l++r)=weightedUnderlying l++weightedUnderlying r := by
  simp only [weightedUnderlying,List.map_append]

theorem zeroWeightChain_average {f : ℝ → ℝ} (hf : BoundedDerivs f) (t : List (ℝ × ℝ)) :
    vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2)=fun p => p.2^2 := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    change vectorStepAverage p.1 (p.2,0) (vectorIncrementChain (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1))
      (vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2))=_
    rw [ih]
    apply vectorStepAverage_frozen (vectorIncrementChain_regular _ (hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    intro x s
    simp only [Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]

theorem weightedFull_average (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementAverage (zeroWeightChain c++w++zeroWeightChain t)
      (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (0,0)=
      scalarIncrementAverage c (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t f))
        (fun x => vectorIncrementAverage w (fun p : ℝ × ℝ => scalarIncrementChain t f p.1) (fun p => p.2^2) (x,0)) 0 := by
  rw [vectorIncrementAverage_append,zeroWeightChain_average hf,weightedBranch_value,weightedUnderlying_zeroWeight,
    vectorIncrementAverage_append,weightedBranch_value]
  have H := congrFun (vectorIncrementAverage_pullback zeroNoiseEmbedding c
    (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t f) p.1)
    (vectorIncrementAverage w (fun p : ℝ × ℝ => scalarIncrementChain t f p.1) (fun p => p.2^2))) 0
  simp only [Function.comp_def,zeroNoiseEmbedding_apply,vectorIncrementAverage_real] at H
  exact H.symm

end SK.Analytic

end
end

end OAI
