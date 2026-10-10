import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalIncrement
import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedLabels

namespace OAI

/-! Apply terminal:increment to actual original and replacement profiles.
The subcollection realization premise is discharged by graph deletion. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped BigOperators Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.terminal_increment_profiles {k d a : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U T : RawPathSystem G Q) (hUamount : U.amount = S.amount)
    (hUcount : U.assignedCount = S.assignedCount)
    {original output kept removed : List ℕ}
    (ho : SystemAssignedAmounts Q U.chains original)
    (hout : SystemAssignedAmounts Q T.chains output)
    (hp : original.Perm (kept ++ removed)) (hq : output.Perm (a :: kept))
    (hTa : T.amount = S.amount + d) :
    S.amount = k - Q.card ∧ removed = [] ∧ kept.length = S.assignedCount ∧
      a = d ∧ ∀ b ∈ original, d ≤ b := by
  classical
  let : DecidableEq (Fin (kept.length + 1)) := Classical.decEq _
  have hosum : original.sum = S.amount := by
    rw [ho.sum_eq, ← U.amount_eq_outside_count, hUamount]
  have hocount : original.length = S.assignedCount := ho.length_eq.trans hUcount
  have hsum : kept.sum + removed.sum = S.amount := by
    rw [← List.sum_append, ← hp.sum_eq, hosum]
  have hlen : kept.length + removed.length = S.assignedCount := by
    rw [← List.length_append, ← hp.length_eq, hocount]
  have houtsum : a + kept.sum = S.amount + d := by
    have hs := hq.sum_eq
    rw [hout.sum_eq, ← T.amount_eq_outside_count, hTa, List.sum_cons] at hs
    omega
  let wt : Fin (kept.length + 1) → ℕ := (a :: kept).get
  let fresh : Fin (kept.length + 1) := 0
  let old : Finset (Fin (kept.length + 1)) := Finset.univ.erase fresh
  have hmap : (List.finRange (kept.length + 1)).map wt = a :: kept := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get _
  have hlabels : (List.finRange (kept.length + 1)).toFinset = Finset.univ := by
    ext i
    simp
  have hwfresh : wt fresh = a := rfl
  have hwtotal : (∑ i, wt i) = a + kept.sum := by
    have hs := List.sum_toFinset wt (List.nodup_finRange (kept.length + 1))
    rw [hlabels, hmap, List.sum_cons] at hs
    exact hs
  have hcard : old.card = kept.length := by
    simp only [old, Finset.card_erase_of_mem (Finset.mem_univ fresh),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hnew : fresh ∉ old := by simp [old]
  have hinsert : insert fresh old = Finset.univ := by simp [old]
  have hwold : (∑ i ∈ old, wt i) = kept.sum := by
    have hs := Finset.sum_erase_add Finset.univ wt (Finset.mem_univ fresh)
    rw [hwfresh, hwtotal] at hs
    change (∑ i ∈ old, wt i) + a = a + kept.sum at hs
    omega
  have hfull : old.card = S.assignedCount → (∑ i ∈ old, wt i) = S.amount := by
    intro he
    rw [hcard] at he
    have hrem : removed = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [hrem, List.sum_nil, Nat.add_zero] at hsum
    rw [hwold, hsum]
  have hrealize : ∀ J ⊆ insert fresh old, ∃ Z : ExpandedPathSystem G Q,
      Z.amount = ∑ i ∈ J, wt i ∧ Z.assignedCount = J.card := by
    intro J hJ
    apply hout.realize_labels_of_perm T (List.finRange (kept.length + 1)) wt
      (List.nodup_finRange _) (by rw [hmap]; exact hq) J
    rw [hlabels]
    exact Finset.subset_univ _
  obtain ⟨hL, he, _, hwa, hall⟩ := hopt.terminal_increment_weights ht hQk hkQ hQ hcycle
    hd hd' old fresh wt hnew (by rw [hwold]; omega) (by rw [hcard]; omega) hfull
    (by rw [hinsert, hwtotal]; exact houtsum) hrealize
  have hkept : kept.length = S.assignedCount := by simpa only [hcard] using he
  have hremoved : removed = [] := List.length_eq_zero_iff.mp (by omega)
  refine ⟨hL, hremoved, hkept, hwfresh.symm.trans hwa, ?_⟩
  intro b hb
  have hbkept : b ∈ kept := by simpa only [hremoved, List.append_nil] using hp.mem_iff.mp hb
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_cons_of_mem a hbkept)
  have hi' : wt i = b := hi
  have hh := hall i (by rw [hinsert]; exact Finset.mem_univ _)
  omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
