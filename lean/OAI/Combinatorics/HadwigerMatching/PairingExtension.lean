import OAI.Combinatorics.HadwigerMatching.Definitions
import OAI.Combinatorics.HadwigerMatching.FinitePairing

namespace OAI

namespace HadwigerMatching

/-- Disjoint pairs from a clique extend a touching matching when every clique vertex
is adjacent to a vertex in each existing matching edge. -/
theorem extend_matching_by_clique_pairs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (E : Finset (Finset V)) (S : Finset V)
    (hE : IsTouchingMatching G E) (hS : G.IsClique (S : Set V))
    (hdisj : ∀ e ∈ E, Disjoint e S)
    (htouch : ∀ v ∈ S, ∀ e ∈ E, ∃ w ∈ e, G.Adj v w) :
    ∃ P : Finset (Finset V), IsTouchingMatching G (E ∪ P) ∧
      (E ∪ P).card = E.card + P.card ∧ S.card ≤ 2 * P.card + 1 := by
  classical
  obtain ⟨P, hP, hPP, _hlo, hhi⟩ := exists_finite_pairing S
  have hnonempty : ∀ p ∈ P, p.Nonempty := by
    intro p hp
    exact Finset.card_pos.mp (by rw [(hP p hp).1]; decide)
  have hEP : ∀ e ∈ E, ∀ p ∈ P, Disjoint e p := by
    intro e he p hp
    apply Finset.disjoint_left.mpr
    intro x hxe hxp
    exact Finset.disjoint_left.mp (hdisj e he) hxe ((hP p hp).2 hxp)
  have hfamily : Disjoint E P := by
    apply Finset.disjoint_left.mpr
    intro e he hp
    obtain ⟨v, hv⟩ := hnonempty e hp
    exact Finset.disjoint_left.mp (hEP e he e hp) hv hv
  have hclique : ∀ p ∈ P, G.IsClique (p : Set V) := by
    intro p hp v hv w hw hne
    exact hS ((hP p hp).2 hv) ((hP p hp).2 hw) hne
  have hPT : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ∃ v ∈ p, ∃ w ∈ q, G.Adj v w := by
    intro p hp q hq hne
    obtain ⟨v, hv⟩ := hnonempty p hp
    obtain ⟨w, hw⟩ := hnonempty q hq
    have hvw : v ≠ w := by
      intro heq
      subst w
      exact Finset.disjoint_left.mp (hPP p hp q hq hne) hv hw
    exact ⟨v, hv, w, hw, hS ((hP p hp).2 hv) ((hP q hq).2 hw) hvw⟩
  have hPEtouch : ∀ p ∈ P, ∀ e ∈ E,
      ∃ v ∈ p, ∃ w ∈ e, G.Adj v w := by
    intro p hp e he
    obtain ⟨v, hv⟩ := hnonempty p hp
    obtain ⟨w, hw, hvw⟩ := htouch v ((hP p hp).2 hv) e he
    exact ⟨v, hv, w, hw, hvw⟩
  refine ⟨P, ?_, Finset.card_union_of_disjoint hfamily, hhi⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hE.1 e he
    · exact ⟨(hP e he).1, hclique e he⟩
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact hE.2.1 e he f hf hne
    · exact hEP e he f hf
    · exact (hEP f hf e he).symm
    · exact hPP e he f hf hne
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact hE.2.2 e he f hf hne
    · obtain ⟨v, hv, w, hw, hvw⟩ := hPEtouch f hf e he
      exact ⟨w, hw, v, hv, hvw.symm⟩
    · exact hPEtouch e he f hf
    · exact hPT e he f hf hne

end HadwigerMatching

end OAI
