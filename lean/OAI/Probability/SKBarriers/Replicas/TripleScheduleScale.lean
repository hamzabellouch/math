import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleScheduleMass
import OAI.Probability.SKBarriers.Scalar.ProductBranchMap

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SK.Analytic

section Scale
variable {E : Type} [SMul ℝ E]
def scaleIncrementChain (β : ℝ) (l : List (ℝ × E)) : List (ℝ × E) := l.map (fun p => (p.1,β • p.2))
end Scale

@[simp] theorem scaleIncrementChain_append {E : Type} [SMul ℝ E] (β : ℝ) (l r : List (ℝ × E)) :
    scaleIncrementChain β (l++r)=scaleIncrementChain β l++scaleIncrementChain β r := by
  simp only [scaleIncrementChain,List.map_append]

theorem weightedUnderlying_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedUnderlying (scaleIncrementChain β w)=scaleIncrementChain β (weightedUnderlying w) := by
  simp only [weightedUnderlying,scaleIncrementChain,List.map_map,Function.comp_def,Prod.smul_fst]

theorem tripleCommonSchedule_scale (β : ℝ) (c : List (ℝ × ℝ)) :
    scaleIncrementChain β (tripleCommonSchedule c)=tripleCommonSchedule (scaleIncrementChain β c) := by
  simp only [scaleIncrementChain,tripleCommonSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · rfl
  · funext i; fin_cases i <;> rfl

theorem tripleMiddleSchedule_scale (β δ : ℝ) (l : List TripleMiddleIncrement) :
    scaleIncrementChain β (tripleMiddleSchedule δ l)=
      tripleMiddleSchedule δ (l.map (mapProductIncrement (fun x : ℝ × ℝ => β • x) (fun x : ℝ => β • x))) := by
  simp only [scaleIncrementChain,tripleMiddleSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · simp only [Function.comp_def,productMass_map]
  · cases p <;> ext i <;> fin_cases i <;>
      norm_num [Function.comp_def,mapProductIncrement,tripleMiddleVector,smul_eq_mul] <;> ring

theorem tripleTailBlock_scale (β : ℝ) (p : ℝ × ℝ) :
    scaleIncrementChain β (tripleTailBlock p)=tripleTailBlock (p.1,β*p.2) := by
  simp only [scaleIncrementChain,tripleTailBlock,List.map_cons,List.map_nil]
  have h0 : β • ![p.2,0,0]=![β*p.2,0,0] := by ext i; fin_cases i <;> simp
  have h1 : β • ![0,p.2,0]=![0,β*p.2,0] := by ext i; fin_cases i <;> simp
  have h2 : β • ![0,0,p.2]=![0,0,β*p.2] := by ext i; fin_cases i <;> simp
  rw [h0,h1,h2]

theorem tripleTailSchedule_scale (β : ℝ) (t : List (ℝ × ℝ)) :
    scaleIncrementChain β (tripleTailSchedule t)=tripleTailSchedule (scaleIncrementChain β t) := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    change scaleIncrementChain β (tripleTailBlock p++tripleTailSchedule t)=
      tripleTailBlock (p.1,β*p.2)++tripleTailSchedule (scaleIncrementChain β t)
    rw [scaleIncrementChain_append,tripleTailBlock_scale,ih]

theorem tripleSchedule_scale (β δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    scaleIncrementChain β (tripleSchedule δ c w t)=
      tripleSchedule δ (scaleIncrementChain β c) (scaleIncrementChain β w) (scaleIncrementChain β t) := by
  simp only [tripleSchedule,scaleIncrementChain_append,tripleCommonSchedule_scale,tripleMiddleSchedule_scale,
    tripleTailSchedule_scale,mergedProductBranches_map,weightedUnderlying_scale]
  rfl

end SK.Analytic

end
end

end OAI
