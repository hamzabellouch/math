import OAI.Combinatorics.BalancedRyser.Local.ReuseWitness

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

def reuseSaving (j : ℕ) : ℕ :=
  if j ≤ 2 then j else if j = 3 then 2 else 1

def reuseExposureScore {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) : List ι → ℕ
  | [] => 0
  | i :: l => reuseExposureScore A l +
      reuseSaving ((A i ∩ l.toFinset.biUnion A).card)

theorem reuseSaving_eq_of_le_two {j : ℕ} (hj : j ≤ 2) : reuseSaving j = j := by
  simp [reuseSaving, hj]

theorem reuseSaving_pos {j : ℕ} (hj : 0 < j) : 1 ≤ reuseSaving j := by
  unfold reuseSaving
  split_ifs <;> omega

theorem family_reuse_insert {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (∑ j ∈ insert i s, (A j).card) - ((insert i s).biUnion A).card =
      ((∑ j ∈ s, (A j).card) - (s.biUnion A).card) +
        (A i ∩ s.biUnion A).card := by
  rw [Finset.sum_insert hi, Finset.biUnion_insert]
  have hsum : (s.biUnion A).card ≤ ∑ j ∈ s, (A j).card := Finset.card_biUnion_le
  have hcard := Finset.card_union_add_card_inter (A i) (s.biUnion A)
  have hinter := Finset.card_le_card (Finset.inter_subset_left : A i ∩ s.biUnion A ⊆ A i)
  omega

theorem reuseExposureScore_eq_reuse_of_small {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (l : List ι)
    (hnd : l.Nodup)
    (hsmall : ∀ i ∈ l, (A i ∩ (l.toFinset.erase i).biUnion A).card ≤ 2) :
    reuseExposureScore A l =
      (∑ i ∈ l.toFinset, (A i).card) - (l.toFinset.biUnion A).card := by
  induction l with
  | nil => simp [reuseExposureScore]
  | cons i l ih =>
    have hni : i ∉ l := (List.nodup_cons.mp hnd).1
    have hnl : l.Nodup := (List.nodup_cons.mp hnd).2
    have hint : (A i ∩ l.toFinset.biUnion A).card ≤ 2 := by
      simpa [List.toFinset_cons, hni] using hsmall i (by simp)
    have hsmalltail : ∀ j ∈ l,
        (A j ∩ (l.toFinset.erase j).biUnion A).card ≤ 2 := by
      intro j hj
      apply le_trans (Finset.card_le_card ?_) (hsmall j (by simp [hj]))
      apply Finset.inter_subset_inter_left
      apply Finset.biUnion_subset_biUnion_of_subset_left
      exact Finset.erase_subset_erase _ (by simp : l.toFinset ⊆ (i :: l).toFinset)
    rw [reuseExposureScore, reuseSaving_eq_of_le_two hint, ih hnl hsmalltail,
      List.toFinset_cons, family_reuse_insert A l.toFinset i (by simpa using hni)]

theorem reuseExposureScore_cons_ge_one {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (i : ι) (l : List ι)
    (j : ι) (hj : j ∈ l) (hoverlap : (A i ∩ A j).Nonempty) :
    reuseExposureScore A l + 1 ≤ reuseExposureScore A (i :: l) := by
  have hpos : 0 < (A i ∩ l.toFinset.biUnion A).card := by
    apply Finset.card_pos.mpr
    obtain ⟨a, ha⟩ := hoverlap
    obtain ⟨hai, haj⟩ := Finset.mem_inter.mp ha
    exact ⟨a, Finset.mem_inter.mpr
      ⟨hai, Finset.mem_biUnion.mpr ⟨j, by simpa using hj, haj⟩⟩⟩
  exact Nat.add_le_add_left (reuseSaving_pos hpos) _

theorem exists_three_reuse_neighbors {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (s : Finset ι)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (i : ι) (hi : i ∈ s)
    (hlarge : 3 ≤ (A i ∩ (s.erase i).biUnion A).card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ i ∧ b ≠ i ∧ c ≠ i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (A a ∩ A i).Nonempty ∧ (A b ∩ A i).Nonempty ∧ (A c ∩ A i).Nonempty := by
  let n := (s.erase i).filter fun j => (A i ∩ A j).Nonempty
  have hni : ∀ j ∈ n, j ∈ s ∧ j ≠ i ∧ (A j ∩ A i).Nonempty := by
    intro j hj
    obtain ⟨hj, hov⟩ := Finset.mem_filter.mp hj
    obtain ⟨hne, hjs⟩ := Finset.mem_erase.mp hj
    exact ⟨hjs, hne, by simpa [Finset.inter_comm] using hov⟩
  have heq : A i ∩ (s.erase i).biUnion A =
      n.biUnion (fun j => A i ∩ A j) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hai, j, hj, haj⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, ⟨a, Finset.mem_inter.mpr ⟨hai, haj⟩⟩⟩, hai, haj⟩
    · rintro ⟨j, hj, hai, haj⟩
      exact ⟨hai, j, (Finset.mem_filter.mp hj).1, haj⟩
  have hncard : 3 ≤ n.card := by
    calc
      3 ≤ (A i ∩ (s.erase i).biUnion A).card := hlarge
      _ = (n.biUnion (fun j => A i ∩ A j)).card := congrArg Finset.card heq
      _ ≤ ∑ j ∈ n, (A i ∩ A j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ n, 1 := Finset.sum_le_sum (fun j hj =>
        hcompat i hi j (hni j hj).1 (Ne.symm (hni j hj).2.1))
      _ = n.card := by simp
  obtain ⟨w, hwn, hwcard⟩ := Finset.exists_subset_card_eq hncard
  obtain ⟨a, b, c, hab, hac, hbc, hw⟩ := Finset.card_eq_three.mp hwcard
  have ha := hni a (hwn (by simp [hw]))
  have hb := hni b (hwn (by simp [hw]))
  have hc := hni c (hwn (by simp [hw]))
  exact ⟨a, ha.1, b, hb.1, c, hc.1, ha.2.1, hb.2.1, hc.2.1,
    hab, hac, hbc, ha.2.2, hb.2.2, hc.2.2⟩

theorem exists_star_reuse_order {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (s : Finset ι)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (i : ι) (hi : i ∈ s)
    (hlarge : 3 ≤ (A i ∩ (s.erase i).biUnion A).card) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset ⊆ s ∧ l.length = 4 ∧
      3 ≤ reuseExposureScore A l := by
  obtain ⟨a, ha, b, hb, c, hc, hai, hbi, hci, hab, hac, hbc, hai', hbi', hci'⟩ :=
    exists_three_reuse_neighbors A s hcompat i hi hlarge
  refine ⟨[c, b, a, i], ?_, ?_, rfl, ?_⟩
  · simp [hai, hbi, hci, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  · intro j hj
    simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
      Finset.notMem_empty, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact hc
    · exact hb
    · exact ha
    · exact hi
  · have h₁ := reuseExposureScore_cons_ge_one A a [i] i (by simp) hai'
    have h₂ := reuseExposureScore_cons_ge_one A b [a, i] i (by simp) hbi'
    have h₃ := reuseExposureScore_cons_ge_one A c [b, a, i] i (by simp) hci'
    omega

theorem exists_six_tuple_reuse_order {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (A : ι → Finset α) (s : Finset ι)
    (hfour : ∀ i ∈ s, (A i).card = 4)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hreuse : 3 ≤ 4 * s.card - (s.biUnion A).card) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset ⊆ s ∧ l.length ≤ 6 ∧
      3 ≤ reuseExposureScore A l := by
  obtain ⟨t, hts, htcard, htr⟩ := exists_six_tuple_reuse_witness s A hfour hreuse
  by_cases hlarge : ∃ i ∈ t, 3 ≤ (A i ∩ (t.erase i).biUnion A).card
  · obtain ⟨i, hi, hlarge⟩ := hlarge
    obtain ⟨l, hnd, hlt, hlen, hscore⟩ := exists_star_reuse_order A t
      (fun a ha b hb hne => hcompat a (hts ha) b (hts hb) hne) i hi hlarge
    exact ⟨l, hnd, hlt.trans hts, by omega, hscore⟩
  · have hsmall : ∀ i ∈ t, (A i ∩ (t.erase i).biUnion A).card ≤ 2 := by
      intro i hi
      have hn : ¬ 3 ≤ (A i ∩ (t.erase i).biUnion A).card :=
        fun h => hlarge ⟨i, hi, h⟩
      omega
    refine ⟨t.toList, t.nodup_toList, by simpa using hts, by simpa using htcard, ?_⟩
    rw [reuseExposureScore_eq_reuse_of_small A t.toList t.nodup_toList
      (by simpa using hsmall)]
    have hsum : (∑ i ∈ t, (A i).card) = 4 * t.card := by
      calc
        (∑ i ∈ t, (A i).card) = ∑ _i ∈ t, 4 :=
          Finset.sum_congr rfl (fun i hi => hfour i (hts hi))
        _ = 4 * t.card := by simp [Nat.mul_comm]
    simpa only [Finset.toList_toFinset, hsum] using htr

end Balanced

end OAI
