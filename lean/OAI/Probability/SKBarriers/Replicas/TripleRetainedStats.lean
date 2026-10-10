import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleBaseFactor
import OAI.Probability.SKBarriers.Replicas.TripleScheduleMass

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem sum_get_map {α : Type} (l : List α) (f : α → ℝ) :
    (∑ i : Fin l.length,f (l.get i))=(l.map f).sum := by
  rw [← List.sum_ofFn]
  simpa only [List.ofFn_get,Function.comp_def] using
    congrArg List.sum (List.map_ofFn (f:=l.get) (g:=f)).symm

theorem mass_get_monotone {E : Type} {l : List (ℝ × E)}
    (hs : l.Pairwise (fun p q => p.1≤q.1)) : Monotone (fun i : Fin l.length => (l.get i).1) := by
  have H := hs
  rw [← List.ofFn_get l,List.pairwise_ofFn] at H
  intro i j hij
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact H hij
  · exact le_rfl

theorem tripleRetainedPrefix_image (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) :
    (tripleRetainedPrefix c w).map (fun p => (p.1,tripleRetainedEmbedding δ p.2))=tripleSchedule δ c w [] := by
  simp only [tripleRetainedPrefix,List.map_append,tripleRetainedCommon_image,tripleRetainedMiddle_image,
    tripleSchedule,tripleTailSchedule,List.flatMap_nil,List.append_nil]

theorem tripleRetainedPrefix_mass (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈c++weightedUnderlying w,p.1∈Icc (0:ℝ) 1) :
    ∀ p∈tripleRetainedPrefix c w,p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  have H := tripleSchedule_mass_bounds 0 c w [] (by simpa only [List.append_nil] using hm)
  rw [← tripleRetainedPrefix_image] at H
  exact H (p.1,tripleRetainedEmbedding 0 p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem tripleRetainedPrefix_monotone (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈c++weightedUnderlying w,0≤p.1)
    (hs : (c++weightedUnderlying w).Pairwise (fun p q => p.1≤q.1)) :
    (tripleRetainedPrefix c w).Pairwise (fun p q => p.1≤q.1) := by
  have H := tripleSchedule_monotone 0 c w [] (by simpa only [List.append_nil] using hm)
    (by simpa only [List.append_nil] using hs)
  rw [← tripleRetainedPrefix_image,List.pairwise_map] at H
  exact H

def weightedAbsCross (w : List (ℝ × (ℝ × ℝ))) : ℝ := (w.map (fun p => |p.2.2| * |p.2.1|)).sum

theorem tripleRetainedMiddle_variance (l : List TripleMiddleIncrement) :
    ((tripleRetainedMiddle l).map (fun p => p.2.1.2^2)).sum=weightedVariance (productLeft l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases p <;> (simp only [tripleRetainedMiddle,List.map_cons,List.map_map,Function.comp_def,
      List.sum_cons,productVector,productLeft,List.filterMap_cons,weightedVariance,List.map_cons,
      List.sum_cons] at ih ⊢; rw [ih] <;> simp)

theorem tripleRetainedMiddle_score (l : List TripleMiddleIncrement) :
    ((tripleRetainedMiddle l).map (fun p => |p.2.1.2| * (|p.2.1.1| + 2*|p.2.2|))).sum=
      weightedAbsCross (productLeft l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases p <;> (simp only [tripleRetainedMiddle,List.map_cons,List.map_map,Function.comp_def,
      List.sum_cons,productVector,productLeft,List.filterMap_cons,weightedAbsCross,List.map_cons,List.sum_cons,
      abs_zero,mul_zero,add_zero] at ih ⊢; rw [ih] <;> simp)

theorem tripleRetainedPrefix_variance (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) :
    ((tripleRetainedPrefix c w).map (fun p => p.2.1.2^2)).sum=weightedVariance w := by
  simp only [tripleRetainedPrefix,List.map_append,List.sum_append,tripleRetainedMiddle_variance,
    mergedProductBranches_left,tripleRetainedCommon,List.map_map,Function.comp_def,zero_pow (by norm_num : 2≠0),
    ]
  simp

theorem tripleRetainedPrefix_score (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) :
    ((tripleRetainedPrefix c w).map (fun p => |p.2.1.2| * (|p.2.1.1| + 2*|p.2.2|))).sum=weightedAbsCross w := by
  simp only [tripleRetainedPrefix,List.map_append,List.sum_append,tripleRetainedMiddle_score,
    mergedProductBranches_left,tripleRetainedCommon,List.map_map,Function.comp_def,abs_zero,zero_mul,
    ]
  simp

end SK.Analytic

end
end

end OAI
