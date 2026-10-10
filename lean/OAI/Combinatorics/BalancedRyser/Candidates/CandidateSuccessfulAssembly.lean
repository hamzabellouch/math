import OAI.Combinatorics.BalancedRyser.Candidates.CandidateCountAssembly
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRetentionTransport

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical
universe u

theorem exists_threshold_candidateGraphGood_of_successful_counts
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → ∀ (M : MergedPairs F) (c : ℝ),
      let P := Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
      (∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ)) →
      (∀ p, (successfulTest M (fun A => p ∈ designated M A)).card ≤ P) →
      (∀ p l, ¬ OnLine p l →
        (successfulTest M (fun A => OnLine p A.line ∧
          ∃ r ∈ designated M A, OnLine r l)).card ≤ P) →
      (∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
        (successfulTest M (fun A => ∃ p ∈ designated M A, ∃ r ∈ designated M A,
          p ≠ r ∧ OnLine p l ∧ OnLine r k)).card ≤ P) →
      (∀ e : Finset (Direction F), e.card = 2 →
        (successfulTest M (fun A => e ⊆ generatorSet A.tuple)).card ≤ P) →
      (∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card F : ℝ))) →
      (∀ g : Direction F, ∀ l : Line F,
        (successfulTest M (fun A => A.line.1 = g ∧
          ∃ p ∈ designated M A, OnLine p l)).card ≤ P) →
      (∀ l : Line F, l ∉ constituentLines M →
        ((successfulTest M (fun A => ∃ p ∈ designated M A, OnLine p l)).card : ℝ) ≤
          C * Fintype.card F) →
      (∀ l : Line F, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) →
      CandidateGraphGood M c (2 * C + 11) := by
  obtain ⟨N, hN⟩ := CandidateIncidence.exists_threshold_candidateGraphGood_of_scaled_counts.{u}
    2 (by omega) (2 * C) (by positivity)
  refine ⟨N, ?_⟩
  intro F _ _ _ hq M c P hsize hpoint hmixed htwo hpair hcap hline hglobal hoccupancy
  apply hN F hq M c hsize
  · intro p
    exact (pointCandidates_card_le M p).trans (Nat.mul_le_mul_left 2 (hpoint p))
  · intro p l hpl
    exact (pointLineCandidates_card_le M p l).trans
      (Nat.mul_le_mul_left 2 (hmixed p l hpl))
  · intro l k hlk hl hk
    exact (twoLineCandidates_card_le M l k).trans
      (Nat.mul_le_mul_left 2 (htwo l k hlk hl hk))
  · intro e he
    exact (generatorPairCandidates_card_le M e).trans
      (Nat.mul_le_mul_left 2 (hpair e he))
  · exact hcap
  · intro s l
    have h := (lineHitSlot_card_le M s l).trans (hline s.1 l)
    omega
  · intro l hl
    have hcount :
        (((candidateVertices M).filter (fun v =>
          ∃ p ∈ CandidateIncidence.points M v, OnLine p l)).card : ℝ) ≤
        2 * (successfulTest M (fun A => ∃ p ∈ designated M A, OnLine p l)).card := by
      exact_mod_cast lineHitAll_card_le M l
    have hg := hglobal l hl
    nlinarith
  · exact hoccupancy

end
end Balanced.CandidateRetentionTransport

end OAI
