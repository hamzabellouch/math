import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315

def reverseProposal {n : Nat} (p : SwitchProposal n) : SwitchProposal n :=
  ⟨p.1, ⟨(p.2.val.2, p.2.val.1), Ne.symm p.2.property⟩⟩

@[simp] theorem removedMatching_reverse {n : Nat} (p : SwitchProposal n) :
    removedMatching (reverseProposal p) = addedMatching p := rfl

@[simp] theorem addedMatching_reverse {n : Nat} (p : SwitchProposal n) :
    addedMatching (reverseProposal p) = removedMatching p := rfl

@[simp] theorem reverseProposal_reverse {n : Nat} (p : SwitchProposal n) :
    reverseProposal (reverseProposal p) = p := by
  rcases p with ⟨S, ⟨⟨M, N⟩, h⟩⟩
  rfl

theorem validSwitch_matchings_disjoint {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) {u v : Fin n}
    (hm : (removedMatching p).Adj u v) : ¬ (addedMatching p).Adj u v := by
  intro hn
  exact h.2 hn (h.1 hm)

theorem validSwitch_reverse_replace {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    validSwitch (replaceEdges G (removedMatching p) (addedMatching p))
      (reverseProposal p) := by
  constructor
  · intro u v hn
    exact Or.inr hn
  · intro u v hm he
    rcases he with he | hn
    · exact he.2 hm
    · exact validSwitch_matchings_disjoint h hm hn

theorem replaceEdges_reverse {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    replaceEdges (replaceEdges G (removedMatching p) (addedMatching p))
      (addedMatching p) (removedMatching p) = G := by
  ext u v
  change (((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨
    (addedMatching p).Adj u v) ∧ ¬ (addedMatching p).Adj u v) ∨
    (removedMatching p).Adj u v ↔ G.Adj u v
  constructor
  · rintro (⟨hG | hN, hn⟩ | hm)
    · exact hG.1
    · exact False.elim (hn hN)
    · exact h.1 hm
  · intro hG
    by_cases hm : (removedMatching p).Adj u v
    · exact Or.inr hm
    · exact Or.inl ⟨Or.inl ⟨hG, hm⟩, fun hn => h.2 hn hG⟩

theorem proposalResult_of_valid {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    proposalResult G p = replaceEdges G (removedMatching p) (addedMatching p) := by
  simp [proposalResult, h]

theorem proposalResult_reverse {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    proposalResult (proposalResult G p) (reverseProposal p) = G := by
  rw [proposalResult_of_valid h,
    proposalResult_of_valid (validSwitch_reverse_replace h)]
  exact replaceEdges_reverse h

theorem validSwitch_of_result_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : proposalResult G p ≠ G) : validSwitch G p := by
  classical
  by_contra hn
  exact h (by simp [proposalResult, hn])

theorem proposalResult_eq_reverse_of_ne {n : Nat} {G H : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hne : G ≠ H) (h : proposalResult G p = H) :
    proposalResult H (reverseProposal p) = G := by
  have hv : validSwitch G p := validSwitch_of_result_ne (by
    rw [h]
    exact Ne.symm hne)
  rw [← h]
  exact proposalResult_reverse hv

theorem switchStep_symm {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} (h : SwitchStep n d G H) : SwitchStep n d H G := by
  rcases h with ⟨p, hp, hresult⟩
  refine ⟨reverseProposal p, ?_, ?_⟩
  · rw [← hresult, proposalResult_of_valid hp]
    exact validSwitch_reverse_replace hp
  · rw [← hresult]
    exact proposalResult_reverse hp

theorem perfectMatching_degree {n : Nat} {S : FourSet n}
    (M : PerfectMatching S) (v : Fin n) :
    graphDegree M.val v = if v ∈ S.val then 1 else 0 := by
  classical
  by_cases hv : v ∈ S.val
  · obtain ⟨w, hw, hu⟩ := (M.property v).1 hv
    have hs : Finset.univ.filter (fun x => M.val.Adj v x) = {w} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hx => hu x hx, fun hx => hx ▸ hw⟩
    simp [graphDegree, hs, hv]
  · have hs : Finset.univ.filter (fun x => M.val.Adj v x) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact (M.property v).2 hv x
    simp [graphDegree, hs, hv]

theorem matchings_degree_eq {n : Nat} (p : SwitchProposal n) (v : Fin n) :
    graphDegree (removedMatching p) v = graphDegree (addedMatching p) v := by
  exact (perfectMatching_degree p.2.val.1 v).trans
    (perfectMatching_degree p.2.val.2 v).symm

theorem replaceEdges_degree_add {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) (v : Fin n) :
    graphDegree (replaceEdges G (removedMatching p) (addedMatching p)) v +
      graphDegree (removedMatching p) v =
    graphDegree G v + graphDegree (addedMatching p) v := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hg : G.Adj v w <;>
    by_cases hm : (removedMatching p).Adj v w <;>
    by_cases hn : (addedMatching p).Adj v w
  all_goals simp_all [replaceEdges, h.1, h.2]

theorem proposalResult_degree {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) (v : Fin n) :
    graphDegree (proposalResult G p) v = graphDegree G v := by
  classical
  by_cases h : validSwitch G p
  · rw [proposalResult_of_valid h]
    have ha := replaceEdges_degree_add h v
    rw [matchings_degree_eq p v] at ha
    exact Nat.add_right_cancel ha
  · simp [proposalResult, h]

theorem proposalResult_realizes {n : Nat} {d : Fin n → Nat}
    {G : SimpleGraph (Fin n)} (hG : Realizes n d G) (p : SwitchProposal n) :
    Realizes n d (proposalResult G p) := by
  intro v
  rw [proposalResult_degree]
  exact hG v

theorem switchKernel_symm {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    switchKernel n d G H = switchKernel n d H G := by
  classical
  by_cases hGH : G = H
  · subst H
    rfl
  have hvGH : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
  have hc : ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card =
      ((allProposals n).filter (fun p => proposalResult H.val p = G.val)).card := by
    apply Finset.card_bij (fun p _ => reverseProposal p)
    · intro p hp
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne hvGH hp
    · intro p hp q hq heq
      have heq' := congrArg reverseProposal heq
      simpa using heq'
    · intro p hp
      refine ⟨reverseProposal p, ?_, reverseProposal_reverse p⟩
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne (Ne.symm hvGH) hp
  simp only [switchKernel, hGH, Ne.symm hGH, ↓reduceIte, zero_add, hc]

theorem switchKernel_nonneg {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    0 ≤ switchKernel n d G H := by
  classical
  unfold switchKernel
  positivity

theorem switchKernel_self_ge_half {n : Nat} {d : Fin n → Nat} (G : GraphState n d) :
    (1 : ℝ) / 2 ≤ switchKernel n d G G := by
  classical
  simp only [switchKernel, ↓reduceIte]
  exact le_add_of_nonneg_right (by positivity)

end Problem315

end

end OAI
