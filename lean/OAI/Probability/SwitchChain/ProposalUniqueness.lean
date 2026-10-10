import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Problem315

theorem IsPerfectMatchingOn.mem_iff_exists_adj {n : Nat} {S : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hm : IsPerfectMatchingOn S M) (v : Fin n) :
    v ∈ S ↔ ∃ w, M.Adj v w := by
  constructor
  · intro hv
    obtain ⟨w, hw, _⟩ := (hm v).1 hv
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    by_contra hv
    exact (hm v).2 hv w hw

theorem IsPerfectMatchingOn.support_unique {n : Nat} {S T : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hS : IsPerfectMatchingOn S M)
    (hT : IsPerfectMatchingOn T M) : S = T := by
  ext v
  rw [hS.mem_iff_exists_adj v, hT.mem_iff_exists_adj v]

theorem SwitchProposal.ext_matchings {n : Nat} {p q : SwitchProposal n}
    (hM : removedMatching p = removedMatching q)
    (hN : addedMatching p = addedMatching q) : p = q := by
  rcases p with ⟨⟨S, hS⟩, ⟨⟨⟨M, hm⟩, ⟨N, hn⟩⟩, hmn⟩⟩
  rcases q with ⟨⟨T, hT⟩, ⟨⟨⟨M', hm'⟩, ⟨N', hn'⟩⟩, hmn'⟩⟩
  change M = M' at hM
  change N = N' at hN
  subst M'
  subst N'
  have hST : S = T := hm.support_unique hm'
  subst T
  rfl

theorem removedMatching_adj_iff {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) (u v : Fin n) :
    (removedMatching p).Adj u v ↔
      G.Adj u v ∧ ¬ (proposalResult G p).Adj u v := by
  classical
  rw [proposalResult, ite_eq_left hp]
  change (removedMatching p).Adj u v ↔ G.Adj u v ∧
    ¬ ((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨ (addedMatching p).Adj u v)
  constructor
  · intro hm
    refine ⟨hp.1 hm, ?_⟩
    rintro (⟨_, hnm⟩ | hn)
    · exact hnm hm
    · exact hp.2 hn (hp.1 hm)
  · rintro ⟨hg, hh⟩
    by_contra hnm
    exact hh (Or.inl ⟨hg, hnm⟩)

theorem addedMatching_adj_iff {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) (u v : Fin n) :
    (addedMatching p).Adj u v ↔
      (proposalResult G p).Adj u v ∧ ¬ G.Adj u v := by
  classical
  rw [proposalResult, ite_eq_left hp]
  change (addedMatching p).Adj u v ↔
    ((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨ (addedMatching p).Adj u v) ∧
      ¬ G.Adj u v
  constructor
  · intro hn
    exact ⟨Or.inr hn, hp.2 hn⟩
  · rintro ⟨⟨hg, _⟩ | hn, hng⟩
    · exact False.elim (hng hg)
    · exact hn

theorem proposalResult_injective_on_valid {n : Nat} {G : SimpleGraph (Fin n)}
    {p q : SwitchProposal n} (hp : validSwitch G p) (hq : validSwitch G q)
    (heq : proposalResult G p = proposalResult G q) : p = q := by
  apply SwitchProposal.ext_matchings
  · ext u v
    rw [removedMatching_adj_iff hp, removedMatching_adj_iff hq, heq]
  · ext u v
    rw [addedMatching_adj_iff hp, addedMatching_adj_iff hq, heq]

theorem validSwitch_of_proposalResult_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : proposalResult G p ≠ G) : validSwitch G p := by
  classical
  by_contra hn
  exact h (by simp [proposalResult, hn])

theorem proposalResult_ne_of_validSwitch {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) : proposalResult G p ≠ G := by
  have hs : p.1.val.Nonempty := Finset.card_pos.mp (by rw [p.1.property]; decide)
  obtain ⟨v, hv⟩ := hs
  obtain ⟨w, hw⟩ := (p.2.val.1.property.mem_iff_exists_adj v).mp hv
  have hh := (removedMatching_adj_iff hp v w).mp hw
  intro heq
  rw [heq] at hh
  exact hh.2 hh.1

theorem validSwitch_iff_proposalResult_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} : validSwitch G p ↔ proposalResult G p ≠ G :=
  ⟨proposalResult_ne_of_validSwitch, validSwitch_of_proposalResult_ne⟩

theorem proposal_count_eq_one {n : Nat} {G H : SimpleGraph (Fin n)}
    (hGH : G ≠ H) (hex : ∃ p : SwitchProposal n, proposalResult G p = H) :
    ((allProposals n).filter (fun p => proposalResult G p = H)).card = 1 := by
  classical
  obtain ⟨p, hp⟩ := hex
  apply Finset.card_eq_one.mpr
  refine ⟨p, ?_⟩
  ext q
  simp only [allProposals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hq
    apply proposalResult_injective_on_valid
    · apply validSwitch_of_proposalResult_ne
      rw [hq]
      exact Ne.symm hGH
    · apply validSwitch_of_proposalResult_ne
      rw [hp]
      exact Ne.symm hGH
    · exact hq.trans hp.symm
  · rintro rfl
    exact hp

theorem proposal_count_eq_zero {n : Nat} {G H : SimpleGraph (Fin n)}
    (hex : ¬ ∃ p : SwitchProposal n, proposalResult G p = H) :
    ((allProposals n).filter (fun p => proposalResult G p = H)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hex ⟨p, (Finset.mem_filter.mp hp).2⟩

theorem switchKernel_of_ne {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} (hGH : G ≠ H) :
    switchKernel n d G H =
      if SwitchStep n d G H then 1 / (12 * (Nat.choose n 4 : ℝ)) else 0 := by
  classical
  have hv : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
  have hiff : SwitchStep n d G H ↔
      ∃ p : SwitchProposal n, proposalResult G.val p = H.val := by
    constructor
    · rintro ⟨p, _, hp⟩
      exact ⟨p, hp⟩
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_, hp⟩
      apply validSwitch_of_proposalResult_ne
      rw [hp]
      exact Ne.symm hv
  by_cases hs : SwitchStep n d G H
  · rw [switchKernel, ite_eq_right hGH, ite_eq_left hs,
      proposal_count_eq_one hv (hiff.mp hs)]
    simp
  · rw [switchKernel, ite_eq_right hGH, ite_eq_right hs,
      proposal_count_eq_zero (fun h => hs (hiff.mpr h))]
    simp

end Problem315

end

end OAI
