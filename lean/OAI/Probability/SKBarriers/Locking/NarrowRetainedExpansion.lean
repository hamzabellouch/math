import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleFiniteExpansion
import OAI.Probability.SKBarriers.Locking.NarrowRetainedFactor

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowToTriple : NarrowRetainedState →L[ℝ] TripleRetainedState :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))+
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)))

@[simp] theorem narrowToTriple_apply (p : NarrowRetainedState) :
    narrowToTriple p=((p.1.1,p.1.2+p.2.2),p.2.1) := rfl

def narrowRetainedEmbedding (δ : ℝ) : NarrowRetainedState →L[ℝ] (Fin 3 → ℝ) :=
  (tripleRetainedEmbedding δ).comp narrowToTriple

@[simp] theorem narrowRetainedEmbedding_apply (δ : ℝ) (p : NarrowRetainedState) :
    narrowRetainedEmbedding δ p= ![p.1.1,p.2.1+δ*(p.1.2+p.2.2),p.2.1-δ*(p.1.2+p.2.2)] := by
  simp [narrowRetainedEmbedding,tripleRetainedEmbedding_apply,narrowToTriple_apply]

def narrowRetainedPrefix (c v w : List (ℝ × (ℝ × ℝ))) : List (ℝ × NarrowRetainedState) :=
  narrowRetainedCommon c++narrowRetainedMiddle (mergedProductBranches v w)

def narrowSchedule (δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  narrowCommonSchedule δ c++narrowMiddleSchedule δ (mergedProductBranches v w)++tripleTailSchedule t

theorem narrowRetainedCommon_image (δ : ℝ) (c : List (ℝ × (ℝ × ℝ))) :
    (narrowRetainedCommon c).map (fun p => (p.1,narrowRetainedEmbedding δ p.2))=narrowCommonSchedule δ c := by
  simp only [narrowRetainedCommon,List.map_map,Function.comp_def,narrowRetainedEmbedding_apply,zero_add,narrowCommonSchedule]

theorem narrowRetainedMiddle_image (δ : ℝ) (l : List NarrowMiddleIncrement) :
    (narrowRetainedMiddle l).map (fun p => (p.1,narrowRetainedEmbedding δ p.2))=narrowMiddleSchedule δ l := by
  simp only [narrowRetainedMiddle,List.map_map,narrowMiddleSchedule]
  apply List.map_congr_left
  intro p _
  cases p <;> simp [productVector,narrowRetainedEmbedding_apply,narrowMiddleVector]

theorem narrowRetainedPrefix_image (δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ)))
    {t : List (ℝ × ℝ)} :
    (narrowRetainedPrefix c v w).map (fun p => (p.1,narrowRetainedEmbedding δ p.2))++tripleTailSchedule t=
      narrowSchedule δ c v w t := by
  simp only [narrowRetainedPrefix,List.map_append,narrowRetainedCommon_image,narrowRetainedMiddle_image,narrowSchedule]

theorem narrowRetained_expansion (l : List (ℝ × NarrowRetainedState)) (t : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hs : l.Pairwise (fun p q => p.1≤q.1))
    (htm : ∀ p∈t,p.1∈Icc (0:ℝ) 1) (hts : t.Pairwise (fun p q => p.1≤q.1))
    {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*(l.map (fun p => (p.2.1.2+p.2.2.2)^2)).sum+
      (2*(l.map (fun p => |p.2.1.2+p.2.2.2| *(|p.2.1.1|+2*|p.2.2.1|))).sum)^2)≤1/2) :
    let f := scalarIncrementChain t scalarSpinTerminal
    vectorIncrementChain (l.map (fun p => (p.1,narrowRetainedEmbedding δ p.2)))
      (fun x : Fin 3 → ℝ => f (x 0)+f (x 1)+f (x 2)) 0≤
      vectorIncrementChain l (fun p => f p.1.1+2*f p.2.1) 0+
      δ^2*vectorIncrementAverage l (fun p => f p.1.1+2*f p.2.1)
        (fun p => rootHessian 0 f p.2.1*(p.1.2+p.2.2)^2) 0+tripleExpansionConstant a*|δ|^3 := by
  have hsmall' : a*(4*(∑ i : Fin l.length,((narrowToTriple (l.get i).2).1.2)^2)+
      (2*∑ i : Fin l.length, |(narrowToTriple (l.get i).2).1.2| *
        (|(narrowToTriple (l.get i).2).1.1|+2*|(narrowToTriple (l.get i).2).2|))^2)≤1/2 := by
    simp only [narrowToTriple_apply]
    rw [sum_get_map l (fun p => (p.2.1.2+p.2.2.2)^2),
      sum_get_map l (fun p => |p.2.1.2+p.2.2.2| * (|p.2.1.1|+2*|p.2.2.1|))]
    exact hsmall
  have H := tripleRetained_expansion l.length t.length (fun i => (l.get i).1)
    (fun i => narrowToTriple (l.get i).2) (fun i => (t.get i).1) (fun i => (t.get i).2)
    (fun i => hm _ (List.get_mem l i)) (mass_get_monotone hs)
    (fun i => htm _ (List.get_mem t i)) (mass_get_monotone hts) ha hδ hδ1 hsmall'
  dsimp only at H ⊢
  rw [← scalarIncrementChain_get] at H
  let f := scalarIncrementChain t scalarSpinTerminal
  have hval := congrFun (vectorHierarchy_pullback narrowToTriple l.length (fun i => (l.get i).1)
    (fun i => (l.get i).2) (fun p : TripleRetainedState => f p.1.1+2*f p.2)) 0
  have hav := congrFun (vectorHierarchyAverage_pullback narrowToTriple l.length (fun i => (l.get i).1)
    (fun i => (l.get i).2) (fun p : TripleRetainedState => f p.1.1+2*f p.2)
    (fun p => rootHessian 0 f p.2*p.1.2^2)) 0
  simp only [map_zero,Function.comp_def,narrowToTriple_apply] at hval hav
  dsimp only [f] at hval hav
  simp only [narrowToTriple_apply] at H
  rw [← hval,← hav,← vectorIncrementChain_get,← vectorIncrementAverage_get] at H
  have himage : List.ofFn (fun i : Fin l.length => ((l.get i).1,narrowRetainedEmbedding δ (l.get i).2))=
      l.map (fun p => (p.1,narrowRetainedEmbedding δ p.2)) := by
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,narrowRetainedEmbedding δ p.2))).symm
  change vectorHierarchy l.length (fun i => (l.get i).1)
    (fun i => narrowRetainedEmbedding δ (l.get i).2) _ 0≤_ at H
  rw [← vectorIncrementChain_ofFn,himage] at H
  exact H

end SK.Analytic

end
end

end OAI
