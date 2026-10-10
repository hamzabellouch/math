import OAI.Combinatorics.HadwigerMatching.SmallBranches
import OAI.Combinatorics.HadwigerMatching.BranchGeometry
import OAI.Combinatorics.HadwigerMatching.PairingExtension
import OAI.Combinatorics.HadwigerMatching.BasicMatching

namespace OAI

/-! The integral Hadwiger bound from pairwise touching matchings.

The small-branch counting argument is Proposition `matching-minor` of
*A counterexample to Hadwiger's conjecture*, following the connected-matching
approach of Cambie.
-/

namespace HadwigerMatching

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- The singleton and doubleton deficits of an actual clique-minor model are
controlled by a touching matching constructed from those very branches. -/
theorem small_branch_deficit_le {t : ℕ} (B : Fin t → Finset V)
    (hconn : ∀ i, (G.induce (B i : Set V)).Connected)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) :
    2 * singletonBranchCount B + doubletonBranchCount B ≤
      4 * connectedMatchingNumber G + 2 := by
  classical
  have hE := twoVertexBranches_isTouchingMatching G B hdisj htouch
    (fun i hi => connected_card_two_isClique (B i) hi (hconn i))
  obtain ⟨P, hP, hcard, hcover⟩ := extend_matching_by_clique_pairs G
    (twoVertexBranches B) (singletonVertices B) hE
    (singletonVertices_isClique G B htouch)
    (fun _ he => twoVertexBranches_disjoint_singletonVertices B hdisj he)
    (fun _ hv _ he => singletonVertices_touch_twoVertexBranches G B htouch hv he)
  have hbound := matching_card_le_number hP
  rw [hcard, card_twoVertexBranches B hne hdisj] at hbound
  rw [card_singletonVertices B hdisj] at hcover
  omega

/-- Every clique minor satisfies the integral matching bound. -/
theorem clique_minor_matching_bound {t : ℕ}
    (h : LinearListHadwiger.HasCliqueMinor G t) :
    3 * t ≤ Fintype.card V + 4 * connectedMatchingNumber G + 2 := by
  classical
  obtain ⟨B, hconn, hne, hdisj, htouch⟩ := finite_branch_model h
  have hcount := branch_counting B hne hdisj
  have hsmall := small_branch_deficit_le B hconn hne hdisj htouch
  omega

/-- The maximum is attained by an actual clique-minor branch model. This proves
the bound for the literal Hadwiger number, including the empty graph. -/
theorem hadwiger_matching_bound (G : SimpleGraph V) :
    3 * LinearListHadwiger.hadwigerNumber G ≤
      Fintype.card V + 4 * connectedMatchingNumber G + 2 :=
  clique_minor_matching_bound (LinearListHadwiger.hasCliqueMinor_hadwigerNumber G)

end HadwigerMatching

end OAI
