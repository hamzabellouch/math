import OAI.Combinatorics.Ramsey.CycleClique.Construction.ChainCounts

namespace OAI

/-! Elementary counting properties of nontrivial expanded chains. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem chain_clique_count_two (S : ExpandedPathSystem G Q) {l : List V}
    (hl : l ∈ S.chains) : 2 ≤ chainCliqueCount Q l := by
  have hlen := S.nontrivial l hl
  have hne : l ≠ [] := by intro he; simp [he] at hlen
  let a := l.head hne
  let b := l.getLast hne
  have ha : a ∈ Q := (S.endpoints l hl).1 a (List.head?_eq_some_head hne)
  have hb : b ∈ Q := (S.endpoints l hl).2 b (List.getLast?_eq_some_getLast hne)
  have hab : a ≠ b := by
    intro he
    obtain ⟨v, hv⟩ := ((S.paths l hl).1.head_eq_getLast_iff hne).mp he
    simp [hv] at hlen
  let I := (l.filter (fun v => decide (v ∈ Q))).toFinset
  have haI : a ∈ I := by simp only [I, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]; exact ⟨List.head_mem hne, ha⟩
  have hbI : b ∈ I := by simp only [I, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]; exact ⟨List.getLast_mem hne, hb⟩
  have hc : 2 ≤ I.card := Finset.one_lt_card.mpr ⟨a, haI, b, hbI, hab⟩
  simpa only [I, List.toFinset_card_of_nodup ((S.paths l hl).1.filter _), chainCliqueCount]
    using hc

theorem chains_length_le_assignedCount (S : ExpandedPathSystem G Q) :
    S.chains.length ≤ S.assignedCount := by
  rw [S.assignedCount_eq_raw]
  have hpos : ∀ l ∈ S.chains, 1 ≤ chainCliqueCount Q l - 1 := by
    intro l hl
    have h := S.chain_clique_count_two hl
    omega
  generalize he : S.chains = C at hpos ⊢
  clear he
  induction C with
  | nil => simp [rawAssignedCount]
  | cons l C ih =>
    have hl := hpos l (by simp)
    have hi := ih (fun l hl => hpos l (by simp [hl]))
    simp only [List.length_cons, rawAssignedCount, List.map_cons, List.sum_cons] at hi ⊢
    omega

theorem amount_eq_zero_of_assignedCount_eq_zero (S : ExpandedPathSystem G Q)
    (he : S.assignedCount = 0) : S.amount = 0 := by
  have hl := S.chains_length_le_assignedCount
  have hc : S.chains = [] := List.length_eq_zero_iff.mp (by omega)
  simp [amount, vertices, hc]

theorem assignedCount_pos_of_amount_pos (S : ExpandedPathSystem G Q)
    (hL : 0 < S.amount) : 0 < S.assignedCount := by
  by_contra hn
  have he : S.assignedCount = 0 := by omega
  have h := S.amount_eq_zero_of_assignedCount_eq_zero he
  omega

theorem incident_eq_two_of_assignedCount_one (S : ExpandedPathSystem G Q)
    (he : S.assignedCount = 1) : S.incident = 2 := by
  have hl := S.chains_length_le_assignedCount
  have hl' : S.chains.length ≤ 1 := by omega
  have hne : S.chains ≠ [] := by
    intro hc
    have hh := S.assignedCount_eq_raw
    simp [hc, rawAssignedCount] at hh
    omega
  have hcpos : 1 ≤ S.chains.length := List.length_pos_iff.mpr hne
  unfold assignedCount at he
  omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
