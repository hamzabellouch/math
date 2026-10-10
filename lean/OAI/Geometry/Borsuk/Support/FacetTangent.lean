import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped BigOperators
section FacetTangent
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "W" => EuclideanSpace ℝ (Fin k)
noncomputable def facetTangent {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : W →ₗ[ℝ] (ι → ℝ) where
  toFun v i := if hi : i ∈ I then Fin.cases (-∑ j, v j) (fun j => v j) (a.symm ⟨i,hi⟩) else 0
  map_add' x y := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.sum_add_distrib]; ring
      · rfl
    · simp
  map_smul' t x := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.mul_sum]
      · rfl
    · simp

omit [Fintype ι] in
lemma facetTangent_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : W) (j : Fin (k+1)) :
    facetTangent a v (a j).val = Fin.cases (-∑ j, v j) (fun j => v j) j := by
  simp [facetTangent]
omit [Fintype ι] in
lemma facetTangent_zero_outside {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : W) {i : ι} (hi : i ∉ I) :
    facetTangent a v i = 0 := by simp [facetTangent,hi]
omit [Fintype ι] in
lemma facetTangent_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : W) : ∑ i ∈ I, facetTangent a v i = 0 := by
  calc
    _ = ∑ i : ↥I, facetTangent a v i.val := (Finset.sum_coe_sort I _).symm
    _ = ∑ j : Fin (k+1), facetTangent a v (a j).val := (Equiv.sum_comp a _).symm
    _ = 0 := by simp only [facetTangent_apply,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]; ring
omit [Fintype ι] in
lemma facetTangent_injective {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : Function.Injective (facetTangent a) := by
  intro x y h
  ext j
  have hh := congrFun h (a j.succ).val
  simpa only [facetTangent_apply,Fin.cases_succ] using hh
end FacetTangent
end BorsukNine

end OAI
