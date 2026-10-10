import OAI.Analysis.CoulombTransport.SmoothBranchMarginal

namespace OAI

noncomputable section

namespace Problem356.SmoothBranchMarginal

/-- Component containment in the disjoint five certificate regions supplies
exactly the disjointness input of the smooth marginal construction. -/
theorem componentRegion_pairwise_of_subsets
    {B : Set E3} {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {U : Fin 5 → Set E3}
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hB : B ⊆ U 0) (he : ∀ i, e i '' B ⊆ U i.succ) :
    Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      exact (hU (Fin.succ_ne_zero j).symm).mono hB (he j)
  | some i =>
    cases j with
    | none =>
      exact (hU (Fin.succ_ne_zero i)).mono (he i) hB
    | some j =>
      exact (hU (fun h => hij (congrArg some (Fin.succ_injective 4 h)))).mono (he i) (he j)

end Problem356.SmoothBranchMarginal

end

end OAI
