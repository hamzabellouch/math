import OAI.Analysis.LipschitzHilbert.Trees.SourceRestrictedGram

namespace OAI

/-! Exact grouping of a finite Gram matrix by scale. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem sum_level_fibers {ι J A : Type*} [Fintype J] [DecidableEq J] [AddCommMonoid A]
    (S : Finset ι) (level : ι → J) (f : J → ι → A) :
    (∑ j, ∑ i∈S.filter (fun i => level i=j), f j i)=∑ i∈S, f (level i) i := by
  calc
    _ = ∑ j, ∑ i∈S.filter (fun i => level i=j), f (level i) i := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise S level (fun i => f (level i) i)

theorem gram_group_by_level {ι J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset ι) (level : ι → J) (v : ι → E)
    (near : J → J → Prop) [DecidableRel near] :
    (∑ a, ∑ b, if near a b then
      (inner ℂ (∑ i∈S.filter (fun i => level i=a), v i)
        (∑ j∈S.filter (fun j => level j=b), v j)).re else 0)=
      ∑ i∈S, ∑ j∈S, if near (level i) (level j) then (inner ℂ (v i) (v j)).re else 0 := by
  have he (a b : J) : (if near a b then
      (inner ℂ (∑ i∈S.filter (fun i => level i=a), v i)
        (∑ j∈S.filter (fun j => level j=b), v j)).re else 0)=
      ∑ i∈S.filter (fun i => level i=a), ∑ j∈S.filter (fun j => level j=b),
        if near a b then (inner ℂ (v i) (v j)).re else 0 := by
    by_cases h : near a b
    · simp only [h,ite_true]
      change RCLike.re (inner ℂ _ _)=_
      simp only [sum_inner,inner_sum,map_sum]
      exact Finset.sum_comm
    · simp only [h,ite_false,Finset.sum_const_zero]
  simp_rw [he]
  calc
    _ = ∑ a, ∑ i∈S.filter (fun i => level i=a),
        ∑ b, ∑ j∈S.filter (fun j => level j=b),
          if near a b then (inner ℂ (v i) (v j)).re else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i∈S.filter (fun i => level i=a),
        ∑ j∈S, if near a (level j) then (inner ℂ (v i) (v j)).re else 0 := by
      simp_rw [sum_level_fibers]
    _ = _ := sum_level_fibers S level _

end LipschitzHilbert

end

end OAI
