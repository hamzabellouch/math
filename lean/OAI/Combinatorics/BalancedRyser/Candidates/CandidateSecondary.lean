import Mathlib.Data.Finset.Powerset
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidence

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {M : MergedPairs F}

def generators (M : MergedPairs F) (v : CandidateVertex F) : Finset (Direction F) :=
  generatorSet (candidateChoice M v).tuple

theorem generators_card {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (generators M v).card = 4 := by
  have hinj := (valid hv).2.2.1
  simpa [generators, generatorSet] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin 4)) hinj

def generatorPairCandidates (M : MergedPairs F) (e : Finset (Direction F)) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => e ⊆ generators M w)

def generatorConflicts (M : MergedPairs F) (v : CandidateVertex F) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => 2 ≤ (generators M v ∩ generators M w).card)

theorem generator_conflicts_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {P : ℕ}
    (hpair : ∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P) :
    (generatorConflicts M v).card ≤ 6 * P := by
  have hsub : generatorConflicts M v ⊆
      ((generators M v).powersetCard 2).biUnion (generatorPairCandidates M) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, htwo⟩
    obtain ⟨e, he, hcard⟩ := Finset.exists_subset_card_eq htwo
    have hev : e ⊆ generators M v := fun x hx => (Finset.mem_inter.mp (he hx)).1
    have hew : e ⊆ generators M w := fun x hx => (Finset.mem_inter.mp (he hx)).2
    exact Finset.mem_biUnion.mpr
      ⟨e, Finset.mem_powersetCard.mpr ⟨hev, hcard⟩, Finset.mem_filter.mpr ⟨hwv, hew⟩⟩
  calc
    (generatorConflicts M v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ (generators M v).powersetCard 2, (generatorPairCandidates M e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ (generators M v).powersetCard 2, P :=
      Finset.sum_le_sum (fun e he => hpair e (Finset.mem_powersetCard.mp he).2)
    _ = 6 * P := by norm_num [Finset.card_powersetCard, generators_card hv, Nat.choose]

def directionsAt (M : MergedPairs F) (p : Point F) : Finset (Direction F) :=
  (Finset.univ.filter (fun ds : Direction F × Bool =>
    OnLine p (constituent M ds.1 ds.2))).image Prod.fst

theorem directionsAt_card_le_multiplicity (M : MergedPairs F) (p : Point F) :
    (directionsAt M p).card ≤ sampledMultiplicity M p := Finset.card_image_le

theorem mem_directionsAt_iff (M : MergedPairs F) (p : Point F) (d : Direction F) :
    d ∈ directionsAt M p ↔ p ∈ mergedPoints M d := by
  simp only [directionsAt, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    mergedPoints, Finset.mem_union, linePoints]
  constructor
  · rintro ⟨⟨d', b⟩, hp, rfl⟩
    cases b with
    | false => exact Or.inl hp
    | true => exact Or.inr hp
  · rintro (hp | hp)
    · exact ⟨(d, false), hp, rfl⟩
    · exact ⟨(d, true), hp, rfl⟩

def touchedDirections (M : MergedPairs F) (v : CandidateVertex F) : Finset (Direction F) :=
  (points M v).biUnion (directionsAt M)

theorem mem_touchedDirections_iff (M : MergedPairs F) (v : CandidateVertex F)
    (d : Direction F) :
    d ∈ touchedDirections M v ↔ (points M v ∩ mergedPoints M d).Nonempty := by
  simp only [touchedDirections, Finset.mem_biUnion, mem_directionsAt_iff]
  constructor
  · rintro ⟨p, hp, hpd⟩
    exact ⟨p, Finset.mem_inter.mpr ⟨hp, hpd⟩⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩

theorem touchedDirections_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {cap : ℕ}
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap) :
    (touchedDirections M v).card ≤ 4 * cap := by
  calc
    (touchedDirections M v).card ≤ ∑ p ∈ points M v, (directionsAt M p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, cap := Finset.sum_le_sum
      (fun p _ => (directionsAt_card_le_multiplicity M p).trans (hcap p))
    _ = 4 * cap := by simp [points_card hv]

def mergedConflicts (M : MergedPairs F) (v : CandidateVertex F) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => v.1.1 = w.1.1 ∧
    ∃ d, (points M v ∩ mergedPoints M d).Nonempty ∧
      (points M w ∩ mergedPoints M d).Nonempty)

theorem secondary_subset_generator_merged (M : MergedPairs F) (v : CandidateVertex F) :
    secondary M v ⊆ generatorConflicts M v ∪ mergedConflicts M v := by
  intro w hw
  rcases Finset.mem_sdiff.mp hw with ⟨hwn, hnot⟩
  have hadj := (Finset.mem_filter.mp hwn).2
  have hwv := hadj.2.1
  have hnotB : w ∉ B M v := fun h => hnot (Finset.mem_union_left _ h)
  have hnotE : w ∉ E M v := fun h => hnot (Finset.mem_union_right _ h)
  have hpv : ∀ p ∈ points M v, ¬ OnLine p (candidateLine w) := by
    intro p hp hline
    exact hnotB (Finset.mem_filter.mpr ⟨hwv, p, hp, hline⟩)
  have hpw : ∀ p ∈ points M w, ¬ OnLine p (candidateLine v) := by
    intro p hp hline
    exact hnotE (Finset.mem_filter.mpr ⟨hwv, p, hp, hline⟩)
  by_cases hgen : (generators M v ∩ generators M w).card ≤ 1
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hwv, ?_⟩
    by_contra hn
    apply hadj.2.2.2
    refine ⟨hpv, hpw, hgen, ?_⟩
    intro heq d
    constructor
    · intro hbad
      apply hn
      have hvpos : 0 < (points M v ∩ mergedPoints M d).card :=
        lt_of_lt_of_le (by decide : 0 < 2) hbad.1
      have hwpos : 0 < (points M w ∩ mergedPoints M d).card := hbad.2
      exact ⟨heq, d, Finset.card_pos.mp hvpos, Finset.card_pos.mp hwpos⟩
    · intro hbad
      apply hn
      have hvpos : 0 < (points M v ∩ mergedPoints M d).card := hbad.2
      have hwpos : 0 < (points M w ∩ mergedPoints M d).card :=
        lt_of_lt_of_le (by decide : 0 < 2) hbad.1
      exact ⟨heq, d, Finset.card_pos.mp hvpos, Finset.card_pos.mp hwpos⟩
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hwv, by omega⟩

def lineHitSlot (M : MergedPairs F) (s : Slot F) (l : Line F) : Finset (CandidateVertex F) :=
  (candidateSlot M s).filter (fun w => ∃ p ∈ points M w, OnLine p l)

def mergedHitCandidates (M : MergedPairs F) (g d : Direction F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => w.1.1 = g ∧
    (points M w ∩ mergedPoints M d).Nonempty)

theorem mergedHit_candidates_card_le (M : MergedPairs F) (g d : Direction F) {A : ℕ}
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A) :
    (mergedHitCandidates M g d).card ≤ 4 * A := by
  let U := Finset.univ.biUnion (fun sb : Bool × Bool =>
    lineHitSlot M (g, sb.1) (constituent M d sb.2))
  have hsub : mergedHitCandidates M g d ⊆ U := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, hdir, p, hp⟩
    rcases Finset.mem_inter.mp hp with ⟨hpw, hpm⟩
    have hpm' : OnLine p (constituent M d false) ∨ OnLine p (constituent M d true) := by
      simpa [mergedPoints, linePoints] using hpm
    have hws : w ∈ candidateSlot M (g, w.1.2) :=
      mem_candidateSlot.mpr ⟨mem_candidateVertices.mp hwv, Prod.ext hdir rfl⟩
    rcases hpm' with hl | hl
    · exact Finset.mem_biUnion.mpr ⟨(w.1.2, false), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hws, p, hpw, hl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(w.1.2, true), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hws, p, hpw, hl⟩⟩
  calc
    (mergedHitCandidates M g d).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ sb : Bool × Bool, (lineHitSlot M (g, sb.1) (constituent M d sb.2)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _sb : Bool × Bool, A := Finset.sum_le_sum (fun sb _ => hline _ _)
    _ = 4 * A := by simp

theorem merged_conflicts_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {cap A : ℕ}
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap)
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A) :
    (mergedConflicts M v).card ≤ 16 * cap * A := by
  have hsub : mergedConflicts M v ⊆
      (touchedDirections M v).biUnion (mergedHitCandidates M v.1.1) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, hdir, d, hdv, hdw⟩
    exact Finset.mem_biUnion.mpr ⟨d, (mem_touchedDirections_iff M v d).mpr hdv,
      Finset.mem_filter.mpr ⟨hwv, hdir.symm, hdw⟩⟩
  calc
    (mergedConflicts M v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ touchedDirections M v, (mergedHitCandidates M v.1.1 d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ touchedDirections M v, 4 * A :=
      Finset.sum_le_sum (fun d _ => mergedHit_candidates_card_le M _ d hline)
    _ = (touchedDirections M v).card * (4 * A) := by simp
    _ ≤ (4 * cap) * (4 * A) :=
      Nat.mul_le_mul_right (4 * A) (touchedDirections_card_le hv hcap)
    _ = 16 * cap * A := by ring

theorem secondary_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {P cap A : ℕ}
    (hpair : ∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P)
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap)
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A) :
    (secondary M v).card ≤ 6 * P + 16 * cap * A := by
  apply (Finset.card_le_card (secondary_subset_generator_merged M v)).trans
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (generator_conflicts_card_le hv hpair) (merged_conflicts_card_le hv hcap hline))

theorem E_inter_slot_eq_lineHitSlot (M : MergedPairs F) (v : CandidateVertex F) (s : Slot F) :
    E M v ∩ candidateSlot M s = lineHitSlot M s (candidateLine v) := by
  ext w
  simp only [E, lineHitSlot, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨_, hp⟩, hws⟩
    exact ⟨hws, hp⟩
  · rintro ⟨hws, hp⟩
    exact ⟨⟨Finset.mem_of_mem_filter w hws, hp⟩, hws⟩

end
end Balanced.CandidateIncidence

end OAI
