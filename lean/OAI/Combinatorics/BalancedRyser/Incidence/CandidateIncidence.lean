import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateBasics
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRetention
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {M : MergedPairs F}

def points (M : MergedPairs F) (v : CandidateVertex F) : Finset (Point F) :=
  designated M (candidateChoice M v)

theorem valid {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    ValidChoice M v.1.1 (candidateChoice M v) :=
  retainedChoice_valid (mem_candidateVertices.mp hv)

theorem points_card {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (points M v).card = 4 := by
  have hinj := (valid hv).2.2.2.2.1
  simpa [points, designated] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin 4)) hinj

theorem points_nonempty {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (points M v).Nonempty := by
  apply Finset.card_pos.mp
  rw [points_card hv]
  decide

theorem points_on_line {v : CandidateVertex F} (hv : v ∈ candidateVertices M)
    {p : Point F} (hp : p ∈ points M v) : OnLine p (candidateLine v) := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact (valid hv).2.2.2.2.2.1 i

omit [Field F] [Fintype F] [DecidableEq F] in

theorem eq_of_same_line_same_bit {v w : CandidateVertex F}
    (hl : candidateLine v = candidateLine w) (hb : v.1.2 = w.1.2) : v = w := by
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun l : Line F => l.1) hl
    · exact hb
  · exact congrArg (fun l : Line F => l.2) hl

theorem card_same_line_le_two (M : MergedPairs F) (l : Line F) :
    ((candidateVertices M).filter (fun v => candidateLine v = l)).card ≤ 2 := by
  let A := (candidateVertices M).filter (fun v => candidateLine v = l)
  have hinj : Set.InjOn (fun v : CandidateVertex F => v.1.2) (A : Set _) := by
    intro v hv w hw hb
    exact eq_of_same_line_same_bit
      ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) hb
  calc
    A.card = (A.image (fun v => v.1.2)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card Bool := Finset.card_le_univ _
    _ = 2 := by decide

def exceptionalSet (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w =>
    candidateLine w = candidateLine v ∨ (points M w ∩ points M v).Nonempty)

theorem exceptional_subset (M : MergedPairs F) (v : CandidateVertex F) :
    exceptionalSet M v ⊆ candidateVertices M := Finset.filter_subset _ _

theorem exceptional_adjacent_or_same_slot {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ exceptionalSet M v) :
    CandidateAdjacent M v w ∨ w.1 = v.1 := by
  have hwv := exceptional_subset M v hw
  by_cases hs : v.1 = w.1
  · exact Or.inr hs.symm
  apply Or.inl
  refine ⟨hv, hwv, hs, ?_⟩
  intro hc
  rcases (Finset.mem_filter.mp hw).2 with hl | hpoints
  · obtain ⟨p, hp⟩ := points_nonempty hv
    apply hc.1 p hp
    change OnLine p (candidateLine w)
    rw [hl]
    exact points_on_line hv hp
  · obtain ⟨p, hp⟩ := hpoints
    exact hc.1 p (Finset.mem_inter.mp hp).2
      (points_on_line hwv (Finset.mem_inter.mp hp).1)

theorem not_exceptional_distinct_disjoint {v w : CandidateVertex F}
    (hwv : w ∈ candidateVertices M) (hw : w ∉ exceptionalSet M v) :
    candidateLine w ≠ candidateLine v ∧ Disjoint (points M w) (points M v) := by
  have hn : ¬ (candidateLine w = candidateLine v ∨
      (points M w ∩ points M v).Nonempty) := by
    intro h
    exact hw (Finset.mem_filter.mpr ⟨hwv, h⟩)
  refine ⟨fun h => hn (Or.inl h), ?_⟩
  apply Finset.disjoint_left.mpr
  intro p hpw hpv
  exact hn (Or.inr ⟨p, Finset.mem_inter.mpr ⟨hpw, hpv⟩⟩)

theorem exceptional_card_le {v : CandidateVertex F} (hv : v ∈ candidateVertices M)
    {P : ℕ} (hP : ∀ p : Point F,
      ((candidateVertices M).filter (fun w => p ∈ points M w)).card ≤ P) :
    (exceptionalSet M v).card ≤ 2 + 4 * P := by
  let A := (candidateVertices M).filter (fun w => candidateLine w = candidateLine v)
  let B := (points M v).biUnion (fun p =>
    (candidateVertices M).filter (fun w => p ∈ points M w))
  have hsub : exceptionalSet M v ⊆ A ∪ B := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, hl | hpoints⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwv, hl⟩)
    · obtain ⟨p, hp⟩ := hpoints
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, (Finset.mem_inter.mp hp).2,
          Finset.mem_filter.mpr ⟨hwv, (Finset.mem_inter.mp hp).1⟩⟩)
  have hB : B.card ≤ 4 * P := by
    calc
      B.card ≤ ∑ p ∈ points M v,
          ((candidateVertices M).filter (fun w => p ∈ points M w)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ points M v, P := Finset.sum_le_sum (fun p _ => hP p)
      _ = 4 * P := by simp [points_card hv]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le A B).trans (Nat.add_le_add (card_same_line_le_two M _) hB))

def B (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => ∃ p ∈ points M v, OnLine p (candidateLine w))

def E (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => ∃ p ∈ points M w, OnLine p (candidateLine v))

theorem card_through_point_in_slot_le_one (M : MergedPairs F) (s : Slot F) (p : Point F) :
    ((candidateSlot M s).filter (fun w => OnLine p (candidateLine w))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  rcases Finset.mem_filter.mp hv with ⟨hv, hpv⟩
  rcases Finset.mem_filter.mp hw with ⟨hw, hpw⟩
  apply candidateSlot_line_injective M s hv hw
  apply eq_of_onLine_same_direction p _ _ _ hpv hpw
  change v.1.1 = w.1.1
  rw [(mem_candidateSlot.mp hv).2, (mem_candidateSlot.mp hw).2]

theorem card_through_point_le (M : MergedPairs F) (p : Point F) :
    ((candidateVertices M).filter (fun w => OnLine p (candidateLine w))).card ≤
      2 * (Fintype.card F + 1) := by
  let A := (candidateVertices M).filter (fun w => OnLine p (candidateLine w))
  have hinj : Set.InjOn (fun v : CandidateVertex F => v.1) (A : Set _) := by
    intro v hv w hw hs
    rcases Finset.mem_filter.mp hv with ⟨hv, hpv⟩
    rcases Finset.mem_filter.mp hw with ⟨hw, hpw⟩
    apply Prod.ext hs
    have hl := eq_of_onLine_same_direction p (candidateLine v) (candidateLine w)
      (congrArg (fun s : Slot F => s.1) hs) hpv hpw
    exact congrArg (fun l : Line F => l.2) hl
  calc
    A.card = (A.image (fun v => v.1)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Slot F) := Finset.card_le_univ _
    _ = 2 * (Fintype.card F + 1) := by simp [Slot, Direction, mul_comm]

theorem B_slot_card_le_four {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (s : Slot F) :
    ((B M v) ∩ candidateSlot M s).card ≤ 4 := by
  have hsub : B M v ∩ candidateSlot M s ⊆
      (points M v).biUnion (fun p =>
        (candidateSlot M s).filter (fun w => OnLine p (candidateLine w))) := by
    intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hwB, hws⟩
    obtain ⟨p, hp, hline⟩ := (Finset.mem_filter.mp hwB).2
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hws, hline⟩⟩
  calc
    ((B M v) ∩ candidateSlot M s).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v,
        ((candidateSlot M s).filter (fun w => OnLine p (candidateLine w))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, 1 :=
      Finset.sum_le_sum (fun p _ => card_through_point_in_slot_le_one M s p)
    _ = 4 := by simp [points_card hv]

theorem B_card_le {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (B M v).card ≤ 8 * (Fintype.card F + 1) := by
  have hsub : B M v ⊆ (points M v).biUnion (fun p =>
      (candidateVertices M).filter (fun w => OnLine p (candidateLine w))) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, p, hp, hline⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hwv, hline⟩⟩
  calc
    (B M v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v,
        ((candidateVertices M).filter (fun w => OnLine p (candidateLine w))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, 2 * (Fintype.card F + 1) :=
      Finset.sum_le_sum (fun p _ => card_through_point_le M p)
    _ = 8 * (Fintype.card F + 1) := by simp [points_card hv]; omega

theorem B_inter_B_card_le {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ candidateVertices M)
    (hd : Disjoint (points M v) (points M w)) :
    ((B M v) ∩ (B M w)).card ≤ 32 := by
  let T := (points M v).biUnion (fun p => (points M w).biUnion (fun r =>
    (candidateVertices M).filter (fun z => candidateLine z = joiningLine p r)))
  have hsub : B M v ∩ B M w ⊆ T := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzv, hzw⟩
    rcases Finset.mem_filter.mp hzv with ⟨hz, p, hp, hpz⟩
    obtain ⟨r, hr, hrz⟩ := (Finset.mem_filter.mp hzw).2
    have hpr : p ≠ r := by
      intro heq
      exact Finset.disjoint_left.mp hd hp (heq.symm ▸ hr)
    have hl := eq_of_two_common_points p r hpr (candidateLine z) (joiningLine p r)
      hpz hrz (onLine_joiningLine_left p r) (onLine_joiningLine_right p r)
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_biUnion.mpr
      ⟨r, hr, Finset.mem_filter.mpr ⟨hz, hl⟩⟩⟩
  have hinner : ∀ p : Point F,
      ((points M w).biUnion (fun r =>
        (candidateVertices M).filter (fun z => candidateLine z = joiningLine p r))).card ≤ 8 := by
    intro p
    calc
      _ ≤ ∑ r ∈ points M w,
          ((candidateVertices M).filter (fun z => candidateLine z = joiningLine p r)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ points M w, 2 :=
        Finset.sum_le_sum (fun r _ => card_same_line_le_two M _)
      _ = 8 := by simp [points_card hw]
  calc
    (B M v ∩ B M w).card ≤ T.card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v, ((points M w).biUnion (fun r =>
        (candidateVertices M).filter (fun z => candidateLine z = joiningLine p r))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, 8 := Finset.sum_le_sum (fun p _ => hinner p)
    _ = 32 := by simp [points_card hv]

def pointCandidates (M : MergedPairs F) (p : Point F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun z => p ∈ points M z)

def pointLineCandidates (M : MergedPairs F) (p : Point F) (l : Line F) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun z => OnLine p (candidateLine z) ∧
    ∃ r ∈ points M z, OnLine r l)

def twoLineCandidates (M : MergedPairs F) (l k : Line F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun z => ∃ p ∈ points M z, ∃ r ∈ points M z,
    p ≠ r ∧ OnLine p l ∧ OnLine r k)

theorem common_line_points_card_le_one (l k : Line F) (hne : l ≠ k) :
    (linePoints l ∩ linePoints k).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  rcases Finset.mem_inter.mp hp with ⟨hpl, hpk⟩
  rcases Finset.mem_inter.mp hr with ⟨hrl, hrk⟩
  exact common_point_eq_of_lines_ne l k hne p r
    (Finset.mem_filter.mp hpl).2 (Finset.mem_filter.mp hpk).2
    (Finset.mem_filter.mp hrl).2 (Finset.mem_filter.mp hrk).2

theorem pointLine_subset_of_onLine (M : MergedPairs F) (p : Point F) (l : Line F)
    (hp : OnLine p l) :
    pointLineCandidates M p l ⊆
      ((candidateVertices M).filter (fun z => candidateLine z = l)) ∪ pointCandidates M p := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzv, hpz, r, hr, hrl⟩
  by_cases hl : candidateLine z = l
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzv, hl⟩)
  · have hpr := common_point_eq_of_lines_ne (candidateLine z) l hl p r hpz hp
      (points_on_line hzv hr) hrl
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzv, hpr.symm ▸ hr⟩)

theorem pointLine_card_le_of_onLine (M : MergedPairs F) (p : Point F) (l : Line F)
    (hp : OnLine p l) {P : ℕ} (hP : (pointCandidates M p).card ≤ P) :
    (pointLineCandidates M p l).card ≤ 2 + P := by
  apply (Finset.card_le_card (pointLine_subset_of_onLine M p l hp)).trans
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (card_same_line_le_two M l) hP)

theorem B_inter_E_card_le {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {P : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixed : ∀ p, ¬ OnLine p (candidateLine w) →
      (pointLineCandidates M p (candidateLine w)).card ≤ P) :
    (B M v ∩ E M w).card ≤ 4 * (2 + P) := by
  have hsub : B M v ∩ E M w ⊆
      (points M v).biUnion (fun p => pointLineCandidates M p (candidateLine w)) := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzB, hzE⟩
    rcases Finset.mem_filter.mp hzB with ⟨hzv, p, hp, hpz⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp,
      Finset.mem_filter.mpr ⟨hzv, hpz, (Finset.mem_filter.mp hzE).2⟩⟩
  have hsingle : ∀ p, (pointLineCandidates M p (candidateLine w)).card ≤ 2 + P := by
    intro p
    by_cases hp : OnLine p (candidateLine w)
    · exact pointLine_card_le_of_onLine M p (candidateLine w) hp (hpoint p)
    · exact (hmixed p hp).trans (Nat.le_add_left _ _)
  calc
    (B M v ∩ E M w).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v, (pointLineCandidates M p (candidateLine w)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, (2 + P) := Finset.sum_le_sum (fun p _ => hsingle p)
    _ = 4 * (2 + P) := by simp [points_card hv]

theorem E_inter_E_card_le {v w : CandidateVertex F}
    (hne : candidateLine v ≠ candidateLine w) {P : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (htwo : (twoLineCandidates M (candidateLine v) (candidateLine w)).card ≤ P) :
    (E M v ∩ E M w).card ≤ 2 * P := by
  let I := linePoints (candidateLine v) ∩ linePoints (candidateLine w)
  let A := I.biUnion (fun p => pointCandidates M p)
  have hsub : E M v ∩ E M w ⊆
      twoLineCandidates M (candidateLine v) (candidateLine w) ∪ A := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzv, hzw⟩
    rcases Finset.mem_filter.mp hzv with ⟨hz, p, hp, hpl⟩
    obtain ⟨r, hr, hrk⟩ := (Finset.mem_filter.mp hzw).2
    by_cases hpr : p = r
    · subst r
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨p, ?_, Finset.mem_filter.mpr ⟨hz, hp⟩⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrk⟩⟩
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hz, p, hp, r, hr, hpr, hpl, hrk⟩)
  have hA : A.card ≤ P := by
    calc
      A.card ≤ ∑ p ∈ I, (pointCandidates M p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ I, P := Finset.sum_le_sum (fun p _ => hpoint p)
      _ = I.card * P := by simp
      _ ≤ 1 * P := Nat.mul_le_mul_right P (common_line_points_card_le_one _ _ hne)
      _ = P := one_mul P
  calc
    (E M v ∩ E M w).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (twoLineCandidates M (candidateLine v) (candidateLine w)).card + A.card :=
      Finset.card_union_le _ _
    _ ≤ P + P := Nat.add_le_add htwo hA
    _ = 2 * P := by omega

theorem primary_common_card_le {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ candidateVertices M)
    (hne : candidateLine v ≠ candidateLine w)
    (hd : Disjoint (points M v) (points M w)) {P : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixedv : ∀ p, ¬ OnLine p (candidateLine v) →
      (pointLineCandidates M p (candidateLine v)).card ≤ P)
    (hmixedw : ∀ p, ¬ OnLine p (candidateLine w) →
      (pointLineCandidates M p (candidateLine w)).card ≤ P)
    (htwo : (twoLineCandidates M (candidateLine v) (candidateLine w)).card ≤ P) :
    ((B M v ∪ E M v) ∩ (B M w ∪ E M w)).card ≤ 48 + 10 * P := by
  have hBB := B_inter_B_card_le hv hw hd
  have hBE := B_inter_E_card_le hv hpoint hmixedw
  have hEB : (E M v ∩ B M w).card ≤ 4 * (2 + P) := by
    simpa only [Finset.inter_comm] using B_inter_E_card_le hw hpoint hmixedv
  have hEE := E_inter_E_card_le hne hpoint htwo
  rw [Finset.union_inter_distrib_right, Finset.inter_union_distrib_left,
    Finset.inter_union_distrib_left]
  have houter := Finset.card_union_le
    ((B M v ∩ B M w) ∪ (B M v ∩ E M w))
    ((E M v ∩ B M w) ∪ (E M v ∩ E M w))
  have hleft := Finset.card_union_le (B M v ∩ B M w) (B M v ∩ E M w)
  have hright := Finset.card_union_le (E M v ∩ B M w) (E M v ∩ E M w)
  omega

def secondary (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  candidateNeighbors M v \ (B M v ∪ E M v)

theorem neighbors_subset_primary_secondary (M : MergedPairs F) (v : CandidateVertex F) :
    candidateNeighbors M v ⊆ (B M v ∪ E M v) ∪ secondary M v := by
  intro z hz
  by_cases hp : z ∈ B M v ∪ E M v
  · exact Finset.mem_union_left _ hp
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hp⟩)

theorem common_neighbors_subset (M : MergedPairs F) (v w : CandidateVertex F) :
    candidateNeighbors M v ∩ candidateNeighbors M w ⊆
      (((B M v ∪ E M v) ∩ (B M w ∪ E M w)) ∪ secondary M v) ∪ secondary M w := by
  intro z hz
  rcases Finset.mem_inter.mp hz with ⟨hzv, hzw⟩
  by_cases hvp : z ∈ B M v ∪ E M v
  · by_cases hwp : z ∈ B M w ∪ E M w
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvp, hwp⟩))
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzw, hwp⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzv, hvp⟩))

theorem codegree_le_of_incidence_bounds {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ candidateVertices M)
    (hex : w ∉ exceptionalSet M v) {P R : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixedv : ∀ p, ¬ OnLine p (candidateLine v) →
      (pointLineCandidates M p (candidateLine v)).card ≤ P)
    (hmixedw : ∀ p, ¬ OnLine p (candidateLine w) →
      (pointLineCandidates M p (candidateLine w)).card ≤ P)
    (htwo : (twoLineCandidates M (candidateLine v) (candidateLine w)).card ≤ P)
    (hRv : (secondary M v).card ≤ R) (hRw : (secondary M w).card ≤ R) :
    (candidateNeighbors M v ∩ candidateNeighbors M w).card ≤ 48 + 10 * P + 2 * R := by
  have hgeom := not_exceptional_distinct_disjoint hw hex
  have hprimary := primary_common_card_le hv hw (Ne.symm hgeom.1) hgeom.2.symm
    hpoint hmixedv hmixedw htwo
  have hsub := Finset.card_le_card (common_neighbors_subset M v w)
  have houter := Finset.card_union_le
    (((B M v ∪ E M v) ∩ (B M w ∪ E M w)) ∪ secondary M v) (secondary M w)
  have hinner := Finset.card_union_le
    ((B M v ∪ E M v) ∩ (B M w ∪ E M w)) (secondary M v)
  omega

theorem degree_le_of_incidence_bounds {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {Ebound R : ℕ}
    (hE : (E M v).card ≤ Ebound) (hR : (secondary M v).card ≤ R) :
    (candidateNeighbors M v).card ≤ 8 * (Fintype.card F + 1) + Ebound + R := by
  have hB := B_card_le hv
  have hsub := Finset.card_le_card (neighbors_subset_primary_secondary M v)
  have houter := Finset.card_union_le (B M v ∪ E M v) (secondary M v)
  have hinner := Finset.card_union_le (B M v) (E M v)
  omega

theorem slot_degree_le_of_incidence_bounds {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (s : Slot F) {Ebound R : ℕ}
    (hE : (E M v ∩ candidateSlot M s).card ≤ Ebound)
    (hR : (secondary M v).card ≤ R) :
    (candidateNeighbors M v ∩ candidateSlot M s).card ≤ 4 + Ebound + R := by
  have hB := B_slot_card_le_four hv s
  have hsub : candidateNeighbors M v ∩ candidateSlot M s ⊆
      ((B M v ∩ candidateSlot M s) ∪ (E M v ∩ candidateSlot M s)) ∪ secondary M v := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzn, hzs⟩
    rcases Finset.mem_union.mp (neighbors_subset_primary_secondary M v hzn) with hp | hr
    · apply Finset.mem_union_left
      rcases Finset.mem_union.mp hp with hb | he
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hb, hzs⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, hzs⟩)
    · exact Finset.mem_union_right _ hr
  have hcard := Finset.card_le_card hsub
  have houter := Finset.card_union_le
    ((B M v ∩ candidateSlot M s) ∪ (E M v ∩ candidateSlot M s)) (secondary M v)
  have hinner := Finset.card_union_le (B M v ∩ candidateSlot M s) (E M v ∩ candidateSlot M s)
  omega

end
end Balanced.CandidateIncidence

end OAI
