import OAI.Analysis.CoulombTransport.BranchSeparation

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.BranchSeparation

/-- The disjointness assumptions supplied by the local branch construction
are exactly pairwise disjointness of the five labelled components. -/
lemma pairwise_components_of_disjoint_branches {B : Set E3} {H : Fin 4 → E3 → E3}
    (hcentral : ∀ i, Disjoint B (H i '' B))
    (houter : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) :
    Pairwise fun i j => Disjoint (components B H i) (components B H j) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact False.elim (h rfl)
    · intro _
      exact hcentral j
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      exact (hcentral i).symm
    · intro h
      exact houter (fun h' => h (congrArg Fin.succ h'))

/-- Compact support and uniform separation follow directly from the local
central/outer disjointness interface used by counterexample assembly. -/
theorem compact_support_and_separation_of_branches
    {nu : Measure E3} {K B : Set E3} (hK : IsCompact K) (hKB : K ⊆ B)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hcentral : ∀ i, Disjoint B (H i '' B))
    (houter : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) :
    (∃ S : Set E3, IsCompact S ∧
      ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ S) ∧
    (∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t) :=
  compact_support_and_separation hK hnu hH hcont
    (disjoint_components_mono hKB (pairwise_components_of_disjoint_branches hcentral houter))

end Problem356.BranchSeparation

end

end OAI
