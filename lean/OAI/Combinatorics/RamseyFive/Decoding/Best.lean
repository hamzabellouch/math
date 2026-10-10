import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

omit [LinearOrder I] in
lemma maximizers_nonempty (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) :
    (F.filter fun a => ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape a).card).Nonempty := by
  obtain ⟨a,ha,hm⟩ := Finset.exists_max_image F (fun a => (X ∩ shape a).card) hF
  exact ⟨a,Finset.mem_filter.mpr ⟨ha,hm⟩⟩

noncomputable def best (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) : I :=
  (F.filter fun a => ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape a).card).min'
    (maximizers_nonempty F hF shape X)

lemma best_spec (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V) :
    best F hF shape X ∈ F ∧
      ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape (best F hF shape X)).card :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

noncomputable def remaining (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) : ℕ → Finset V
  | 0 => X
  | k+1 => remaining F hF shape X k \ shape (best F hF shape (remaining F hF shape X k))

noncomputable def chosen (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) (k : ℕ) : I := best F hF shape (remaining F hF shape X k)

noncomputable def cell (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) (k : ℕ) : Finset V :=
  remaining F hF shape X k ∩ shape (chosen F hF shape X k)

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma chosen_mem (k : ℕ) : chosen F hF shape X k ∈ F :=
  (best_spec F hF shape _).1

lemma maximal_cell (k : ℕ) (a : I) (ha : a ∈ F) :
    (remaining F hF shape X k ∩ shape a).card ≤ (cell F hF shape X k).card :=
  (best_spec F hF shape _).2 a ha

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma cell_subset (k : ℕ) : cell F hF shape X k ⊆ remaining F hF shape X k :=
  Finset.inter_subset_left

lemma cell_card_antitone : Antitone (fun k => (cell F hF shape X k).card) := by
  apply antitone_nat_of_succ_le
  intro k
  have hle : remaining F hF shape X (k+1) ∩ shape (chosen F hF shape X (k+1)) ⊆
      remaining F hF shape X k ∩ shape (chosen F hF shape X (k+1)) :=
    Finset.inter_subset_inter_right (remaining_succ_subset F hF shape X k)
  exact (Finset.card_le_card hle).trans (maximal_cell F hF shape X k _ (chosen_mem F hF shape X _))

lemma cell_card_add_remaining (k : ℕ) :
    (cell F hF shape X k).card + (remaining F hF shape X (k+1)).card =
      (remaining F hF shape X k).card := by
  exact Finset.card_inter_add_card_sdiff _ _

lemma sum_card_add_remaining (k : ℕ) :
    (∑ j ∈ Finset.range k, (cell F hF shape X j).card) + (remaining F hF shape X k).card = X.card := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hh := cell_card_add_remaining F hF shape X k
    omega

lemma cell_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (cell F hF shape X i) (cell F hF shape X j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hx : x ∈ remaining F hF shape X (i+1) :=
    remaining_antitone F hF shape X hij (cell_subset F hF shape X j hxj)
  have hxnot := (Finset.mem_sdiff.mp hx).2
  exact hxnot (Finset.mem_inter.mp hxi).2

def Stop (threshold k : ℕ) : Prop :=
  X.card ≤ 2*(X.card-(remaining F hF shape X k).card) ∨
    (cell F hF shape X k).card < threshold

lemma exists_stop (threshold : ℕ) (hthreshold : 0 < threshold) :
    ∃ k ≤ X.card, Stop F hF shape X threshold k := by
  by_contra hn
  push Not at hn
  have hpos (j : ℕ) (hj : j ∈ Finset.range X.card) : 1 ≤ (cell F hF shape X j).card := by
    have hns := hn j (Nat.le_of_lt (Finset.mem_range.mp hj))
    simp only [Stop,not_or,not_lt] at hns
    omega
  have hs := Finset.sum_le_sum hpos
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hs
  have hc := sum_card_add_remaining F hF shape X X.card
  have hnlast := hn X.card le_rfl
  apply hnlast
  left
  omega

noncomputable def stopIndex (threshold : ℕ) (hthreshold : 0 < threshold) : ℕ :=
  Nat.find (Exists.imp (fun _ hk => hk.2) (exists_stop F hF shape X threshold hthreshold))

lemma stopIndex_stops (threshold : ℕ) (hthreshold : 0 < threshold) :
    Stop F hF shape X threshold (stopIndex F hF shape X threshold hthreshold) := Nat.find_spec _

lemma before_stop (threshold : ℕ) (hthreshold : 0 < threshold) {j : ℕ}
    (hj : j < stopIndex F hF shape X threshold hthreshold) :
    (cell F hF shape X j).card ≥ threshold ∧
      2*(X.card-(remaining F hF shape X j).card) < X.card := by
  have h := Nat.find_min (Exists.imp (fun _ hk => hk.2)
    (exists_stop F hF shape X threshold hthreshold)) hj
  simpa only [Stop, not_or, not_le, not_lt, and_comm] using h

lemma stopIndex_le_card (threshold : ℕ) (hthreshold : 0 < threshold) :
    stopIndex F hF shape X threshold hthreshold ≤ X.card := by
  obtain ⟨k,hk,hs⟩ := exists_stop F hF shape X threshold hthreshold
  exact (Nat.find_min' _ hs).trans hk

lemma list_length_bound (threshold : ℕ) (hthreshold : 0 < threshold) :
    stopIndex F hF shape X threshold hthreshold * threshold ≤ X.card := by
  let J := stopIndex F hF shape X threshold hthreshold
  change J*threshold ≤ X.card
  have hs := Finset.sum_le_sum (s := Finset.range J) (fun j hj =>
    (before_stop F hF shape X threshold hthreshold (Finset.mem_range.mp hj)).1)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hc := sum_card_add_remaining F hF shape X J
  omega

noncomputable def retained (threshold : ℕ) (hthreshold : 0 < threshold) : Finset V :=
  if X.card ≤ 2*(X.card-(remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)).card)
  then X \ remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)
  else remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)

lemma retained_subset (threshold : ℕ) (hthreshold : 0 < threshold) :
    retained F hF shape X threshold hthreshold ⊆ X := by
  unfold retained
  split
  · exact Finset.sdiff_subset
  · exact remaining_subset F hF shape X _

lemma retained_half (threshold : ℕ) (hthreshold : 0 < threshold) :
    X.card ≤ 2*(retained F hF shape X threshold hthreshold).card := by
  have hsub := Finset.card_le_card (remaining_subset F hF shape X
    (stopIndex F hF shape X threshold hthreshold))
  unfold retained
  split
  · rename_i h
    rw [Finset.card_sdiff_of_subset (remaining_subset F hF shape X _)]
    exact h
  · rename_i h
    omega

lemma residual_cap (threshold : ℕ) (hthreshold : 0 < threshold)
    (hn : ¬X.card ≤ 2*(X.card-(remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)).card))
    (a : I) (ha : a ∈ F) :
    (retained F hF shape X threshold hthreshold ∩ shape a).card < threshold := by
  rw [retained,ite_eq_right hn]
  have hc := (stopIndex_stops F hF shape X threshold hthreshold).resolve_left hn
  exact (maximal_cell F hF shape X _ a ha).trans_lt hc

lemma remaining_eq_sdiff_union (k : ℕ) :
    remaining F hF shape X k = X \ (Finset.range k).biUnion (fun j => shape (chosen F hF shape X j)) := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    change remaining F hF shape X k \ shape (chosen F hF shape X k) = _
    rw [ih]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
    change (x ∈ X ∧ ¬∃ j < k, x ∈ shape (chosen F hF shape X j)) ∧
        x ∉ shape (chosen F hF shape X k) ↔
      x ∈ X ∧ ¬∃ j < k+1, x ∈ shape (chosen F hF shape X j)
    constructor
    · rintro ⟨⟨hx,hn⟩,hk⟩
      refine ⟨hx,?_⟩
      rintro ⟨j,hj,hxj⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hj | rfl
      · exact hn ⟨j,hj,hxj⟩
      · exact hk hxj
    · rintro ⟨hx,hn⟩
      refine ⟨⟨hx,?_⟩,?_⟩
      · rintro ⟨j,hj,hxj⟩
        exact hn ⟨j,Nat.lt_succ_of_lt hj,hxj⟩
      · intro hxk
        exact hn ⟨k,Nat.lt_succ_self k,hxk⟩

lemma prefix_length_bound (k threshold : ℕ)
    (hlarge : ∀ j < k, threshold ≤ (cell F hF shape X j).card) :
    k*threshold ≤ X.card := by
  have hs := Finset.sum_le_sum (s := Finset.range k) (fun j hj => hlarge j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hh := sum_card_add_remaining F hF shape X k
  omega

lemma tail_cap (k cap : ℕ) (hcap : (cell F hF shape X k).card ≤ cap)
    (Y : Finset V) (hY : Y ⊆ remaining F hF shape X k) (a : I) (ha : a ∈ F) :
    (Y ∩ shape a).card ≤ cap := by
  exact (Finset.card_le_card (Finset.inter_subset_inter_right hY)).trans
    ((maximal_cell F hF shape X k a ha).trans hcap)

noncomputable def headIndex (J cap : ℕ) : ℕ :=
  Nat.find (show ∃ k, J ≤ k ∨ (cell F hF shape X k).card ≤ cap from ⟨J,Or.inl le_rfl⟩)

lemma headIndex_le (J cap : ℕ) : headIndex F hF shape X J cap ≤ J :=
  Nat.find_min' _ (Or.inl le_rfl)

lemma before_head (J cap : ℕ) {j : ℕ} (hj : j < headIndex F hF shape X J cap) :
    cap < (cell F hF shape X j).card := by
  have hn := Nat.find_min (show ∃ k, J ≤ k ∨ (cell F hF shape X k).card ≤ cap from ⟨J,Or.inl le_rfl⟩) hj
  exact lt_of_not_ge (fun hh => hn (Or.inr hh))

lemma head_length_bound (J cap : ℕ) : headIndex F hF shape X J cap * cap ≤ X.card :=
  prefix_length_bound F hF shape X _ _ (fun _ hj => (before_head F hF shape X J cap hj).le)

lemma head_tail_cap (J cap : ℕ) (a : I) (ha : a ∈ F) :
    ((remaining F hF shape X (headIndex F hF shape X J cap) \ remaining F hF shape X J) ∩ shape a).card ≤ cap := by
  have hs := Nat.find_spec (show ∃ k, J ≤ k ∨ (cell F hF shape X k).card ≤ cap from ⟨J,Or.inl le_rfl⟩)
  rcases hs with h | h
  · have he : headIndex F hF shape X J cap = J := le_antisymm (headIndex_le F hF shape X J cap) h
    simp [he]
  · exact tail_cap F hF shape X _ cap h _ Finset.sdiff_subset a ha

lemma captured_eq_biUnion_cells (J : ℕ) :
    X \ remaining F hF shape X J = (Finset.range J).biUnion (cell F hF shape X) := by
  induction J with
  | zero => simp [remaining]
  | succ J ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ← ih]
    change X \ (remaining F hF shape X J \ shape (chosen F hF shape X J)) =
      (remaining F hF shape X J ∩ shape (chosen F hF shape X J)) ∪ (X \ remaining F hF shape X J)
    ext x
    have hx := @remaining_subset V I _ _ F hF shape X J x
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto

lemma cell_earliest (j : ℕ) (x : V) :
    x ∈ cell F hF shape X j ↔
      x ∈ X ∧ x ∈ shape (chosen F hF shape X j) ∧ ∀ i < j, x ∉ shape (chosen F hF shape X i) := by
  unfold cell
  rw [Finset.mem_inter, remaining_eq_sdiff_union]
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, not_exists, not_and]
  tauto

noncomputable def firstAt (J : ℕ) (x : V) : ℕ :=
  Nat.find (show ∃ j, J ≤ j ∨ x ∈ shape (chosen F hF shape X j) from ⟨J,Or.inl le_rfl⟩)

lemma firstAt_le (J : ℕ) (x : V) : firstAt F hF shape X J x ≤ J :=
  Nat.find_min' _ (Or.inl le_rfl)

lemma firstAt_mem (J : ℕ) (x : V) (h : firstAt F hF shape X J x < J) :
    x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) := by
  have hs := Nat.find_spec (show ∃ j, J ≤ j ∨ x ∈ shape (chosen F hF shape X j) from ⟨J,Or.inl le_rfl⟩)
  change J ≤ firstAt F hF shape X J x ∨ x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) at hs
  exact hs.resolve_left (not_le_of_gt h)

lemma firstAt_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    firstAt F hF shape X J x = j := by
  apply le_antisymm
  · exact Nat.find_min' _ (Or.inr hxj)
  · by_contra hn
    have hlt : firstAt F hF shape X J x < j := by omega
    exact hearlier _ hlt (firstAt_mem F hF shape X J x (hlt.trans hj))

noncomputable def ownCell (J : ℕ) (x : V) : Finset V :=
  if firstAt F hF shape X J x < J then cell F hF shape X (firstAt F hF shape X J x) else ∅

lemma ownCell_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    ownCell F hF shape X J x = cell F hF shape X j := by
  rw [ownCell, firstAt_eq F hF shape X J j x hj hxj hearlier, ite_eq_left hj]

end SharpRamseyFive.GreedyTraining

end OAI
