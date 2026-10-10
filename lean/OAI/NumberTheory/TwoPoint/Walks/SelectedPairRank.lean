import OAI.NumberTheory.TwoPoint.Walks.HighRankMinor

namespace OAI

/-! A maximal jointly independent pair family yields independent blocks of
difference vectors and controlling coordinate vectors. -/

namespace TwoPointCorrelations

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem selected_label_pairs_independent (label : ι → α) (offset : ι → α → ℝ)
    (S : Finset (EqualLabelPairs label))
    (hind : LinearIndependent ℝ (pairFamily (labelPairVectors label offset) S)) :
    LinearIndependent ℝ (Sum.elim
      (fun p : S => offset p.val.val.2.1 - offset p.val.val.2.2)
      (fun p : S => Pi.basisFun ℝ α p.val.val.1)) := by
  apply pairFamily_sum_independent
  convert hind using 1
  funext z
  rcases z with ⟨p, j⟩
  fin_cases j <;> simp [pairFamily, labelPairVectors]

omit [Fintype ι] in
/-- The exact finite maximal-pair representation produces the disjoint
coordinate minor without introducing any additional rank premise. -/
theorem selected_label_pairs_disjoint_minor (label : ι → α) (offset : ι → α → ℝ)
    (S : Finset (EqualLabelPairs label))
    (hind : LinearIndependent ℝ (pairFamily (labelPairVectors label offset) S)) :
    Function.Injective (fun p : S => p.val.val.1) ∧
      ∃ pivot : S → α, Function.Injective pivot ∧
        (∀ (i j : S), pivot i ≠ j.val.val.1) ∧
        (Matrix.of fun (i j : S) =>
          (offset i.val.val.2.1 - offset i.val.val.2.2) (pivot j)).det ≠ 0 := by
  exact independent_pairs_disjoint_minor _ _
    (selected_label_pairs_independent label offset S hind)

end TwoPointCorrelations

end OAI
