import OAI.Combinatorics.BalancedRyser.Candidates.CandidateSecondary

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem candidateGraphGood_of_counts (M : MergedPairs F) (c C : ℝ)
    (P A cap D : ℕ)
    (hsize : ∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ))
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixed : ∀ p l, ¬ OnLine p l → (pointLineCandidates M p l).card ≤ P)
    (htwo : ∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
      (twoLineCandidates M l k).card ≤ P)
    (hpair : ∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P)
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap)
    (hcaplog : cap ≤ Nat.ceil (Real.log (Fintype.card F)))
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A)
    (hglobal : ∀ l : Line F, l ∉ constituentLines M →
      ((candidateVertices M).filter (fun w => ∃ p ∈ points M w, OnLine p l)).card ≤ D)
    (hdegree : ((8 * (Fintype.card F + 1) + D + (6 * P + 16 * cap * A) : ℕ) : ℝ) ≤
      C * Fintype.card F)
    (hslot : ((4 + A + (6 * P + 16 * cap * A) : ℕ) : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 / 8 : ℝ))
    (hexception : ((2 + 4 * P : ℕ) : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 / 8 : ℝ))
    (hcodegree : ((48 + 10 * P + 2 * (6 * P + 16 * cap * A) : ℕ) : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 / 8 : ℝ))
    (hoccupancy : ∀ l : Line F, l ∉ initialDeletedLines M →
      (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) :
    CandidateGraphGood M c C := by
  have hsecondary : ∀ v ∈ candidateVertices M,
      (secondary M v).card ≤ 6 * P + 16 * cap * A := by
    intro v hv
    exact secondary_card_le hv hpair hcap hline
  have hnonconst : ∀ v ∈ candidateVertices M, candidateLine v ∉ constituentLines M := by
    intro v hv
    exact (valid hv).2.1
  refine ⟨?_, ?_, ?_, ?_, hoccupancy⟩
  · intro s
    exact ⟨hsize s, candidateSlot_card_le M s⟩
  · intro v hv
    constructor
    · have hn := degree_le_of_incidence_bounds hv
        (hglobal (candidateLine v) (hnonconst v hv)) (hsecondary v hv)
      exact (show ((candidateNeighbors M v).card : ℝ) ≤
          ((8 * (Fintype.card F + 1) + D + (6 * P + 16 * cap * A) : ℕ) : ℝ) by
        exact_mod_cast hn).trans hdegree
    · intro s
      have hE : (E M v ∩ candidateSlot M s).card ≤ A := by
        rw [E_inter_slot_eq_lineHitSlot]
        exact hline s (candidateLine v)
      have hn := slot_degree_le_of_incidence_bounds hv s hE (hsecondary v hv)
      exact (show ((candidateNeighbors M v ∩ candidateSlot M s).card : ℝ) ≤
          ((4 + A + (6 * P + 16 * cap * A) : ℕ) : ℝ) by exact_mod_cast hn).trans hslot
  · intro v hv
    refine ⟨exceptionalSet M v, exceptional_subset M v, ?_, ?_, ?_⟩
    · have hn := exceptional_card_le hv hpoint
      exact (show ((exceptionalSet M v).card : ℝ) ≤ ((2 + 4 * P : ℕ) : ℝ) by
        exact_mod_cast hn).trans hexception
    · intro w hw
      exact exceptional_adjacent_or_same_slot hv hw
    · intro w hw hex
      have hgeom := not_exceptional_distinct_disjoint hw hex
      have hn := codegree_le_of_incidence_bounds hv hw hex hpoint
        (fun p hp => hmixed p (candidateLine v) hp)
        (fun p hp => hmixed p (candidateLine w) hp)
        (htwo (candidateLine v) (candidateLine w) (Ne.symm hgeom.1)
          (hnonconst v hv) (hnonconst w hw))
        (hsecondary v hv) (hsecondary w hw)
      exact (show ((candidateNeighbors M v ∩ candidateNeighbors M w).card : ℝ) ≤
          ((48 + 10 * P + 2 * (6 * P + 16 * cap * A) : ℕ) : ℝ) by
        exact_mod_cast hn).trans hcodegree
  · intro p
    exact (hcap p).trans hcaplog

end
end Balanced.CandidateIncidence

end OAI
