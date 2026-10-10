import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalArithmetic
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalPathSystem
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathSystemCounts

namespace OAI

/-! The minimal-subcollection argument of terminal:increment. The graph
realizations are explicit; the only arithmetic restriction is the proved
five-case inequality for the amount excess. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped BigOperators Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem incident_le_twice_assignedCount (S : ExpandedPathSystem G Q) :
    S.incident ≤ 2 * S.assignedCount := by
  have hh := rawAssignedCount_add_length (Q := Q) S.chains (by
    intro l hl
    have hc := S.chain_clique_count_two hl
    omega)
  rw [← S.assignedCount_eq_raw, ← S.incident_eq_chainCliqueCount] at hh
  have hc := S.chains_length_le_assignedCount
  omega

theorem IsOptimal.terminal_increment_weights {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {ι : Type*} (old : Finset ι) (new : ι) (wt : ι → ℕ) (hnew : new ∉ old)
    (holdsum : ∑ i ∈ old, wt i ≤ S.amount)
    (holdcard : old.card ≤ S.assignedCount)
    (hfull : old.card = S.assignedCount → (∑ i ∈ old, wt i) = S.amount)
    (htotal : ∑ i ∈ insert new old, wt i = S.amount + d)
    (hrealize : ∀ J ⊆ insert new old, ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card) :
    S.amount = k - Q.card ∧ old.card = S.assignedCount ∧
      (∑ i ∈ old, wt i) = S.amount ∧ wt new = d ∧
      ∀ i ∈ insert new old, d ≤ wt i := by
  classical
  let R := insert new old
  let h := k + 1 - Q.card
  have hbudget := hopt.budget
  have hLh : S.amount < h := by dsimp [h]; omega
  have hRsum : ∑ i ∈ R, wt i = S.amount + d := htotal
  have hRlarge : h ≤ ∑ i ∈ R, wt i := by
    by_contra hn
    obtain ⟨T, hTa, _⟩ := hrealize R (Finset.Subset.refl _)
    have hb : T.amount ≤ k - Q.card := by dsimp [h] at hn; omega
    have hm := hopt.maximal T hb
    omega
  have hex : ∃ r, ∃ J : Finset ι, J ⊆ R ∧ h ≤ ∑ i ∈ J, wt i ∧ J.card = r :=
    ⟨R.card, R, Finset.Subset.refl _, hRlarge, rfl⟩
  obtain ⟨J, hJR, hJh, hJcard⟩ := Nat.find_spec hex
  have hminimal : ∀ K ⊆ R, h ≤ ∑ i ∈ K, wt i → J.card ≤ K.card := by
    intro K hKR hKh
    rw [hJcard]
    exact Nat.find_min' hex ⟨K, hKR, hKh, rfl⟩
  have hdelete : ∀ i ∈ J, (∑ a ∈ J.erase i, wt a) < h := by
    intro i hi
    by_contra hn
    have hm := hminimal (J.erase i) (fun a ha => hJR (Finset.mem_of_mem_erase ha)) (by omega)
    have hc := Finset.card_erase_of_mem hi
    have hp := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hnewJ : new ∈ J := by
    by_contra hn
    have hJo : J ⊆ old := by
      intro i hi
      rcases Finset.mem_insert.mp (hJR hi) with rfl | hiold
      · exact False.elim (hn hi)
      · exact hiold
    have hs : (∑ i ∈ J, wt i) ≤ ∑ i ∈ old, wt i :=
      Finset.sum_le_sum_of_subset_of_nonneg hJo (by intros; omega)
    omega
  let j := (∑ i ∈ J, wt i) - h
  have hsumJ : ∑ i ∈ J, wt i = h + j := by dsimp [j]; omega
  have hjupper : j ≤ 5 := by
    have hs : (∑ i ∈ J, wt i) ≤ ∑ i ∈ R, wt i :=
      Finset.sum_le_sum_of_subset_of_nonneg hJR (by intros; omega)
    omega
  obtain ⟨T, hTa, hTe⟩ := hrealize J hJR
  have hinterval : k + 1 < T.amount + T.incident := by
    by_contra hn
    exact T.forbidden_interval (by omega) hQ hcycle (by dsimp [h] at hJh; omega)
      (by omega)
  have hTi := T.incident_le
  have hTtwice := T.incident_le_twice_assignedCount
  have hjpos : 1 ≤ j := by dsimp [h] at hsumJ; omega
  have hr : Q.card + 1 ≤ 2 * J.card + j := by dsimp [h] at hsumJ; omega
  have hweights : ∀ i ∈ J, j + 1 ≤ wt i := by
    intro i hi
    have hdlt := hdelete i hi
    have hs := Finset.sum_erase_add J wt hi
    omega
  have hexact : ∃ i ∈ J, wt i = j + 1 := by
    by_contra hn
    have hall : ∀ i ∈ J, j + 2 ≤ wt i := by
      intro i hi
      have hb := hweights i hi
      have hne : wt i ≠ j + 1 := by intro he; exact hn ⟨i, hi, he⟩
      omega
    have hJo : J.erase new ⊆ old := by
      intro i hi
      have hne := (Finset.mem_erase.mp hi).1
      rcases Finset.mem_insert.mp (hJR (Finset.mem_of_mem_erase hi)) with he | hiold
      · exact False.elim (hne he)
      · exact hiold
    have hsmall : (J.card - 1) * (j + 2) ≤ k - Q.card := by
      calc
        (J.card - 1) * (j + 2) = ∑ _i ∈ J.erase new, (j + 2) := by
          simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hnewJ]
        _ ≤ ∑ i ∈ J.erase new, wt i :=
          Finset.sum_le_sum (fun i (hi : i ∈ J.erase new) =>
            hall i (Finset.mem_of_mem_erase hi))
        _ ≤ ∑ i ∈ old, wt i :=
          Finset.sum_le_sum_of_subset_of_nonneg hJo (by intros; omega)
        _ ≤ S.amount := holdsum
        _ ≤ k - Q.card := hbudget
    exact terminal_increment_arithmetic ht hkQ hQk hjpos hjupper hr hsmall
  obtain ⟨i, hi, hwi⟩ := hexact
  have hdeleteSum : ∑ a ∈ J.erase i, wt a = h - 1 := by
    have hs := Finset.sum_erase_add J wt hi
    dsimp [h] at hsumJ ⊢
    omega
  obtain ⟨U, hUa, hUe⟩ := hrealize (J.erase i) (fun a ha => hJR (Finset.mem_of_mem_erase ha))
  have hUbudget : U.amount ≤ k - Q.card := by rw [hUa, hdeleteSum]; dsimp [h]; omega
  have hUmax := hopt.maximal U hUbudget
  have hL : S.amount = k - Q.card := by rw [hUa, hdeleteSum] at hUmax; dsimp [h] at hUmax; omega
  have hUeq : U.amount = S.amount := by rw [hUa, hdeleteSum, hL]; dsimp [h]; omega
  have hUmin := hopt.minimal U hUeq
  have hJpos : 0 < J.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hJsmall : J.card ≤ old.card + 1 := by
    have hc := Finset.card_le_card hJR
    have hcR : R.card = old.card + 1 := Finset.card_insert_of_notMem hnew
    omega
  have holdEq : old.card = S.assignedCount := by
    rw [hUe, Finset.card_erase_of_mem hi] at hUmin
    omega
  have hJReq : J = R := by
    apply Finset.eq_of_subset_of_card_le hJR
    rw [hUe, Finset.card_erase_of_mem hi] at hUmin
    have hcR : R.card = old.card + 1 := Finset.card_insert_of_notMem hnew
    omega
  have holdSumEq := hfull holdEq
  have hwnew : wt new = d := by
    rw [Finset.sum_insert hnew, holdSumEq] at htotal
    omega
  have hjd : j + 1 = d := by
    rw [hJReq, hRsum] at hsumJ
    dsimp [h] at hsumJ
    omega
  refine ⟨hL, holdEq, holdSumEq, hwnew, ?_⟩
  intro a ha
  rw [← hjd]
  exact hweights a (by simpa only [hJReq] using ha)

end CycleClique.Construction.ExpandedPathSystem

end OAI
