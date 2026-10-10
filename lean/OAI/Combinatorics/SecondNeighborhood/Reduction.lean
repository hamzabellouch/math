import OAI.Combinatorics.SecondNeighborhood.MinimalCounterexample
import OAI.Combinatorics.SecondNeighborhood.SubsetDeficit
import OAI.Combinatorics.SecondNeighborhood.TransitiveBlowup

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem counterexample_reduction {r : V → V → Prop}
    (hr : IsOriented r) (hcounter : Counterexample r) :
    ∃ n : ℕ, 0 < n ∧
      ∃ g : (Fin n × Fin (n + 1)) → (Fin n × Fin (n + 1)) → Prop,
        IsOriented g ∧ PositiveIndegree g ∧ StrictSubsetGrowth g := by
  classical
  obtain ⟨n, hn, s, hs, hbad, hminimal, hboundary, hindegree⟩ :=
    exists_minimal_counterexample hr hcounter
  refine ⟨n, hn, blowup s (n + 1), blowup_isOriented hs (n + 1),
    blowup_positiveIndegree hindegree (n + 1), ?_⟩
  apply blowup_strictSubsetGrowth hs hindegree
    (subsetDeficit_of_minimal hs hbad hminimal hboundary)
  simpa only [Fintype.card_fin] using Nat.lt_succ_self n

end SeymourSecondNeighborhood

end OAI
