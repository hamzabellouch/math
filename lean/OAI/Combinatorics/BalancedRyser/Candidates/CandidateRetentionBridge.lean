import OAI.Combinatorics.BalancedRyser.Candidates.CandidateBasics
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRetention

namespace OAI

namespace Balanced.CandidateRetention

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem valid_line_image_card_le_slot (M : MergedPairs F) (s : Slot F)
    (valid : Finset (SplitChoice F))
    (hvalid : ∀ C ∈ valid, ValidChoice M s.1 C) :
    (valid.image SplitChoice.line).card ≤ (candidateSlot M s).card := by
  let f : Line F → CandidateVertex F := fun l => (s, l.2)
  apply Finset.card_le_card_of_injOn f
  · intro l hl
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hl
    have hc := hvalid C hC
    apply mem_candidateSlot.mpr
    refine ⟨?_, rfl⟩
    change SupportsValidTuple M (s.1, C.line.2)
    have hline : (s.1, C.line.2) = C.line := Prod.ext hc.1.symm rfl
    rw [hline]
    exact ⟨C.tuple, by simpa only [hc.1] using hc⟩
  · intro l hl k hk heq
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hk
    apply Prod.ext
    · exact (hvalid C hC).1.trans (hvalid D hD).1.symm
    · exact congrArg (fun v : CandidateVertex F => v.2) heq

theorem candidateSlot_lower_bound (M : MergedPairs F) (s : Slot F)
    {valid all : Finset (SplitChoice F)} (hsub : valid ⊆ all)
    (hvalid : ∀ C ∈ valid, ValidChoice M s.1 C)
    {a C q : ℝ} (ha : 0 ≤ a) (hC : 0 < C) (hq : 0 < q)
    (hmass : a * q ≤ valid.card)
    (hsquare : (∑ l : Line F,
      ((all.filter (fun T => T.line = l)).card : ℝ) ^ 2) ≤ C * q) :
    (a ^ 2 / C) * q ≤ ((candidateSlot M s).card : ℝ) := by
  have hret := retained_card_lower_bound hsub SplitChoice.line ha hC hq hmass hsquare
  have hslot : ((valid.image SplitChoice.line).card : ℝ) ≤ (candidateSlot M s).card := by
    exact_mod_cast valid_line_image_card_le_slot M s valid hvalid
  exact hret.trans hslot

end
end Balanced.CandidateRetention

end OAI
