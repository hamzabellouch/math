import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFChainAverage
import OAI.Probability.SKBarriers.Hierarchy.TimeChainPressureAlgebra
import OAI.Probability.SKBarriers.Hierarchy.IncrementListAnalytic
import OAI.Probability.SKBarriers.Replicas.TripleScheduleScale

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def rawTimeChain (l : List (ℝ × ℝ≥0)) : List (ℝ × ℝ) := l.map (fun p => (p.1,Real.sqrt (p.2:ℝ)))

@[simp] theorem rawTimeChain_append (l r : List (ℝ × ℝ≥0)) : rawTimeChain (l++r)=rawTimeChain l++rawTimeChain r := by
  simp only [rawTimeChain,List.map_append]

@[simp] theorem rawVariance_rawTimeChain (l : List (ℝ × ℝ≥0)) : rawVariance (rawTimeChain l)=(chainDuration l:ℝ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change (Real.sqrt (p.2:ℝ))^2+rawVariance (rawTimeChain l)=((p.2+chainDuration l:ℝ≥0):ℝ)
    rw [Real.sq_sqrt p.2.coe_nonneg,ih,NNReal.coe_add]

@[simp] theorem rawArea_rawTimeChain (l : List (ℝ × ℝ≥0)) : rawArea (rawTimeChain l)=(l.map (fun p => p.1*(p.2:ℝ))).sum := by
  simp [rawArea,rawTimeChain,List.map_map,Function.comp_def,Real.sq_sqrt]

@[simp] theorem rawPenalty_rawTimeChain (l : List (ℝ × ℝ≥0)) (s : ℝ) : rawPenalty (rawTimeChain l) s=chainQuadraticPenalty s l := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    change p.1*((s+(Real.sqrt (p.2:ℝ))^2)^2-s^2)+rawPenalty (rawTimeChain l) (s+(Real.sqrt (p.2:ℝ))^2)=_
    rw [Real.sq_sqrt p.2.coe_nonneg,ih]
    rfl

theorem rawTimeChain_mass (l : List (ℝ × ℝ≥0)) {P : ℝ → Prop} (hm : ∀ p∈l,P p.1) :
    ∀ p∈rawTimeChain l,P p.1 := by
  intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact hm q hq

theorem rawTimeChain_sorted (l : List (ℝ × ℝ≥0)) (hs : l.Pairwise (fun p q => p.1≤q.1)) :
    (rawTimeChain l).Pairwise (fun p q => p.1≤q.1) := by
  simpa only [rawTimeChain,List.pairwise_map] using hs

theorem scalarIncrementChain_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f=scalarTimeChain β l f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change scalarStep p.1 (β*Real.sqrt (p.2:ℝ)) (scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f)=_
    rw [ih]
    rfl

theorem scalarIncrementAverage_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l)) f g=scalarTimeChainAverage β l f g := by
  have he : scaleIncrementChain β (rawTimeChain l)=List.ofFn (fun i : Fin l.length => ((l.get i).1,β*Real.sqrt ((l.get i).2:ℝ))) := by
    simp only [scaleIncrementChain,rawTimeChain,List.map_map]
    conv_lhs => rw [← List.ofFn_get l,List.map_ofFn]
    rfl
  rw [he,scalarIncrementAverage_ofFn]
  rfl

end SK.Analytic

end
end

end OAI
