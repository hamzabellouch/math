import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantRootFrequencyCount
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGoodMainBudgetRootBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedGoodMainBudget
open Construction Conclusion Filter ResidueHaar HistoryCRTIntegration HistoryGiantFrequencyCount
open HistoryBulkSpectatorProduct HistoryBulkSpectatorDiagramAverage HistorySignedSpectatorDiagramAverage

theorem exists_actual_root_good_main_budget (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0 ≤ Bs) (hk : 0 < k) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ l : ℕ, l ≤ k → ∀ (outside : List ℕ), outside.length = bulkSize k L →
      ∀ (h g : History l)
        (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
        (gs : g.Supported (frequencyBound Bs BD Bz k L) outside)
        (hp : ∀ q ∈ outside, q.Prime)
        (hV : ∀ q ∈ outside, ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q)
        (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))),
      letI := outsideNeZero hp
      letI := primeAtNeZero hp
      (∀ q ∈ outside, 3 ≤ q) → ¬TransferBadArrangement σ →
      (∀ i : Fin outside.length, Real.exp (L/2000) ≤ Real.log (outside.get i:ℝ)) →
      (∀ i : Fin outside.length,
        (FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ) ≤ ε) →
      rootGoodMainPrefactor Bs BD Bz L k l *
        ‖average (fun roots : UnitPair outside.prod =>
          average (unitTest h g hs gs hp hV σ (residueTransform d) roots))‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  have htarget : 0 ≤ H+2*actualFrequencyCost Bs BD Bz k := by
    linarith [actualFrequencyCost_pos Bs BD Bz hk]
  obtain ⟨ε, hε, he⟩ := exists_actual_good_main_budget d Bs BD Bz
    (H+2*actualFrequencyCost Bs BD Bz k) hBs hk htarget
  refine ⟨ε, hε, ?_⟩
  filter_upwards [he, eventually_extraRootFrequency_le Bs BD Bz hk] with L hL hF
  intro l hl outside hlen h g hs gs hp hV σ hthree hgood hlog hcorr
  have := outsideNeZero hp
  have := primeAtNeZero hp
  exact extraRootFrequency_absorb Bs BD Bz H L hk hF
    (hL l hl outside hlen h g hs gs hp hV σ hthree hgood hlog hcorr)

def rootFrequencyPrefactor (Bs BD Bz L : ℝ) (k l : ℕ) : ℝ :=
  64 * correctedAmplitude Bs L k l *
    (2:ℝ)^(2^l*(2*(bulkSize k L/2))) *
    Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) *
    (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)

theorem rootFrequencyPrefactor_le (Bs BD Bz L : ℝ) (k : ℕ) (hL : 0 ≤ L)
    (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    rootFrequencyPrefactor Bs BD Bz L k l ≤ rootGoodMainPrefactor Bs BD Bz L k l := by
  unfold rootFrequencyPrefactor rootGoodMainPrefactor
  apply mul_le_mul_of_nonneg_left
    (HistoryGiantFrequencyCount.actual_root_pair_card_le Bs BD Bz k L hL hm hl)
  unfold correctedAmplitude
  positivity

theorem exists_actual_rootFrequency_good_main_budget (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0 ≤ Bs) (hk : 0 < k) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ l : ℕ, l ≤ k → ∀ (outside : List ℕ), outside.length = bulkSize k L →
      ∀ (h g : History l)
        (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
        (gs : g.Supported (frequencyBound Bs BD Bz k L) outside)
        (hp : ∀ q ∈ outside, q.Prime)
        (hV : ∀ q ∈ outside, ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q)
        (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))),
      letI := outsideNeZero hp
      letI := primeAtNeZero hp
      (∀ q ∈ outside, 3 ≤ q) → ¬TransferBadArrangement σ →
      (∀ i : Fin outside.length, Real.exp (L/2000) ≤ Real.log (outside.get i:ℝ)) →
      (∀ i : Fin outside.length,
        (FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ) ≤ ε) →
      rootFrequencyPrefactor Bs BD Bz L k l *
        ‖average (fun roots : UnitPair outside.prod =>
          average (unitTest h g hs gs hp hV σ (residueTransform d) roots))‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  obtain ⟨ε, hε, he⟩ := exists_actual_root_good_main_budget d Bs BD Bz H hBs hk hH
  refine ⟨ε, hε, ?_⟩
  filter_upwards [he, eventually_ge_atTop (0:ℝ),
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hL hL0 hm
  intro l hl outside hlen h g hs gs hp hV σ hthree hgood hlog hcorr
  have := outsideNeZero hp
  have := primeAtNeZero hp
  apply (mul_le_mul_of_nonneg_right
    (rootFrequencyPrefactor_le Bs BD Bz L k hL0 (by exact_mod_cast hm) hl)
    (norm_nonneg _)).trans
  exact hL l hl outside hlen h g hs gs hp hV σ hthree hgood hlog hcorr

end Ostmann.Arithmetic.HistorySelectedGoodMainBudget

end

end OAI
