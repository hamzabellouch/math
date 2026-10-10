import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalIncrement

namespace OAI

/-! Numerical classification after a realizable representative replacement.
The graph endpoint restrictions are proved separately from this arithmetic. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped BigOperators Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem IsOptimal.terminal_classification_weights {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 2 ≤ d) (hd' : d ≤ 6)
    {ι : Type*} (old : Finset ι) (new : ι) (wt : ι → ℕ) (hnew : new ∉ old)
    (holdsum : ∑ i ∈ old, wt i ≤ S.amount)
    (holdcard : old.card ≤ S.assignedCount)
    (hfull : old.card = S.assignedCount → (∑ i ∈ old, wt i) = S.amount)
    (htotal : ∑ i ∈ insert new old, wt i = S.amount + d)
    (hrealize : ∀ J ⊆ insert new old, ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card)
    (T : ExpandedPathSystem G Q) (hTa : T.amount = S.amount + d)
    (hTi : T.incident ≤ S.incident + 2) :
    S.amount = k - Q.card ∧ (∀ i ∈ old, d ≤ wt i) ∧
      ((d = 2 ∧ Q.card ≤ S.incident + 2) ∨
       (d = 3 ∧ (Q.card = 9 ∨ Q.card = 11) ∧
         2 * S.assignedCount = Q.card - 3 ∧ S.incident = Q.card - 3) ∨
       (d = 5 ∧ Q.card = 9 ∧ k = 19 ∧ S.assignedCount = 2 ∧ S.incident = 4)) := by
  obtain ⟨hL, he, hs, _, hw⟩ := hopt.terminal_increment_weights ht hQk hkQ hQ hcycle
    (by omega) hd' old new wt hnew holdsum holdcard hfull htotal hrealize
  have hde : d * S.assignedCount ≤ S.amount := by
    calc
      d * S.assignedCount = ∑ _i ∈ old, d := by simp [he, Nat.mul_comm]
      _ ≤ ∑ i ∈ old, wt i :=
        Finset.sum_le_sum (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      _ = S.amount := hs
  have hinc : k + 1 < T.amount + T.incident := by
    by_contra hn
    exact T.forbidden_interval (by omega) hQ hcycle (by omega) (by omega)
  have htv : Q.card ≤ S.incident + d := by omega
  exact ⟨hL, fun i hi => hw i (Finset.mem_insert_of_mem hi),
    terminal_classification_arithmetic ht hQk hkQ hL hd hd' hde htv
      S.incident_le_twice_assignedCount⟩

theorem assignedCount_add_chains_length (S : ExpandedPathSystem G Q) :
    S.assignedCount + S.chains.length = S.incident := by
  have hh := rawAssignedCount_add_length (Q := Q) S.chains (by
    intro l hl
    have hc := S.chain_clique_count_two hl
    omega)
  rwa [← S.assignedCount_eq_raw, ← S.incident_eq_chainCliqueCount] at hh

theorem matching_of_incident_eq_twice (S : ExpandedPathSystem G Q)
    (hv : S.incident = 2 * S.assignedCount) :
    ∀ l ∈ S.chains, chainCliqueCount Q l = 2 := by
  have hc := S.assignedCount_add_chains_length
  have hclen : S.chains.length = S.assignedCount := by omega
  have hraw := S.assignedCount_eq_raw
  have hmin : ∀ l ∈ S.chains, 1 ≤ chainCliqueCount Q l - 1 := by
    intro l hl
    have hh := S.chain_clique_count_two hl
    omega
  have hh : ∀ C : List (List V),
      (∀ l ∈ C, 1 ≤ chainCliqueCount Q l - 1) →
      rawAssignedCount Q C = C.length →
      ∀ l ∈ C, chainCliqueCount Q l = 2 := by
    intro C
    induction C with
    | nil => simp
    | cons a C ih =>
      intro hpos heq l hl
      have ha := hpos a (by simp)
      have ht : C.length ≤ rawAssignedCount Q C := by
        have hbound : ∀ D : List (List V),
            (∀ l ∈ D, 1 ≤ chainCliqueCount Q l - 1) →
            D.length ≤ rawAssignedCount Q D := by
          intro D
          induction D with
          | nil => simp [rawAssignedCount]
          | cons b D ih =>
            intro hb
            have hbb := hb b (by simp)
            have hD := ih (fun l hl => hb l (by simp [hl]))
            simp only [List.length_cons, rawAssignedCount, List.map_cons,
              List.sum_cons] at hD ⊢
            omega
        exact hbound C (fun l hl => hpos l (by simp [hl]))
      have heq' : chainCliqueCount Q a - 1 + rawAssignedCount Q C = C.length + 1 := by
        simpa only [rawAssignedCount, List.map_cons, List.sum_cons, List.length_cons] using heq
      have haeq : chainCliqueCount Q a = 2 := by omega
      have htail : rawAssignedCount Q C = C.length := by omega
      rcases List.mem_cons.mp hl with rfl | hl
      · exact haeq
      · exact ih (fun l hl => hpos l (by simp [hl])) htail l hl
  exact hh S.chains hmin (by omega)

theorem two_chains_of_terminal_two (S : ExpandedPathSystem G Q) {k : ℕ}
    (ht : 9 ≤ Q.card) (hk : k ≤ 2 * Q.card + 1)
    (hL : S.amount = k - Q.card) (hbudget : 2 * S.assignedCount ≤ S.amount)
    (hv : Q.card ≤ S.incident + 2) : 2 ≤ S.chains.length := by
  have hc := S.assignedCount_add_chains_length
  have hzero : S.chains.length ≠ 0 := by
    intro he
    have hnil := List.length_eq_zero_iff.mp he
    have hi : S.incident = 0 := by simp [incident, vertices, hnil]
    omega
  omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
