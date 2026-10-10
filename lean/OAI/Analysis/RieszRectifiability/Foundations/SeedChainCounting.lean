import Mathlib

namespace OAI

namespace RieszRectifiability

theorem nat_finset_card_le_of_bounded_interval (P : Finset ℕ) (p I : ℕ)
    (hP : ∀ r ∈ P, p ≤ r ∧ r ≤ p + I) : P.card ≤ I + 1 := by
  have hsub : P ⊆ Finset.Icc p (p + I) := fun r hr => Finset.mem_Icc.mpr (hP r hr)
  have hb := Finset.card_le_card hsub
  simpa only [Nat.card_Icc, Nat.add_assoc, Nat.add_sub_cancel_left] using! hb

theorem captured_seed_chain_count (P O : Finset ℕ) (seed : ℕ → ℕ) (I : ℕ)
    (hseed : ∀ p ∈ P, p ≤ seed p ∧ seed p ≤ p + I)
    (hgap : ∀ p ∈ P, ∀ q ∈ P, seed p < q →
      ∃ t ∈ O, seed p ≤ t ∧ t < q) :
    P.card ≤ (I + 1) * (1 + O.card) := by
  classical
  induction O using Finset.strongInductionOn generalizing P with | _ O ih
  by_cases hP : P.Nonempty
  · let p := P.min' hP
    have hp : p ∈ P := P.min'_mem hP
    have hpmin : ∀ r ∈ P, p ≤ r := fun r hr => P.min'_le r hr
    let Tail := P.filter (fun r => seed p < r)
    by_cases hTail : Tail.Nonempty
    · let q := Tail.min' hTail
      have hqmem : q ∈ Tail := Tail.min'_mem hTail
      have hqP : q ∈ P := (Finset.mem_filter.mp hqmem).1
      have hsq : seed p < q := (Finset.mem_filter.mp hqmem).2
      obtain ⟨t, htO, hst, htq⟩ := hgap p hp q hqP hsq
      let O' := O.filter (fun t => q ≤ t)
      have hstrict : O' ⊂ O := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro heq
        have ht : t ∈ O' := heq.symm ▸ htO
        have hqt := (Finset.mem_filter.mp ht).2
        omega
      let P' := P.filter (fun r => q ≤ r)
      have hbound : (P.filter (fun r => r < q)).card ≤ I + 1 := by
        apply nat_finset_card_le_of_bounded_interval _ p I
        intro r hr
        obtain ⟨hrP, hrq⟩ := Finset.mem_filter.mp hr
        have hrs : r ≤ seed p := by
          by_contra hbad
          have hrTail : r ∈ Tail := Finset.mem_filter.mpr ⟨hrP, by omega⟩
          have hqr : q ≤ r := Tail.min'_le r hrTail
          omega
        exact ⟨hpmin r hrP, hrs.trans (hseed p hp).2⟩
      have hrec : P'.card ≤ (I + 1) * (1 + O'.card) := by
        apply ih O' hstrict P'
        · intro r hr
          exact hseed r (Finset.mem_filter.mp hr).1
        · intro r hr s hs hrs
          obtain ⟨u, huO, hru, hus⟩ := hgap r (Finset.mem_filter.mp hr).1
            s (Finset.mem_filter.mp hs).1 hrs
          refine ⟨u, Finset.mem_filter.mpr ⟨huO, ?_⟩, hru, hus⟩
          exact (Finset.mem_filter.mp hr).2.trans ((hseed r (Finset.mem_filter.mp hr).1).1.trans hru)
      have hsplit : (P.filter (fun r => r < q)).card + P'.card = P.card := by
        simpa only [Nat.not_lt] using!
          Finset.card_filter_add_card_filter_not (s := P) (fun r => r < q)
      have hOcard : O'.card + 1 ≤ O.card := Finset.card_lt_card hstrict
      calc
        P.card = (P.filter (fun r => r < q)).card + P'.card := hsplit.symm
        _ ≤ (I + 1) + (I + 1) * (1 + O'.card) := Nat.add_le_add hbound hrec
        _ = (I + 1) * (1 + (O'.card + 1)) := by ring
        _ ≤ (I + 1) * (1 + O.card) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hOcard 1)
    · have hbound : P.card ≤ I + 1 := by
        apply nat_finset_card_le_of_bounded_interval P p I
        intro r hr
        have hrs : r ≤ seed p := by
          by_contra hbad
          exact hTail ⟨r, Finset.mem_filter.mpr ⟨hr, by omega⟩⟩
        exact ⟨hpmin r hr, hrs.trans (hseed p hp).2⟩
      calc
        P.card ≤ I + 1 := hbound
        _ ≤ (I + 1) * (1 + O.card) := by nlinarith
  · have heq : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    simp only [heq, Finset.card_empty, Nat.zero_le]

end RieszRectifiability

end OAI
