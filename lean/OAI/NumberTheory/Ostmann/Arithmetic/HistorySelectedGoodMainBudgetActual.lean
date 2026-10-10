import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGoodMainBudget

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedGoodMainBudget
open Construction Conclusion Filter ResidueHaar HistoryCRTIntegration
open HistoryBulkSpectatorProduct HistoryBulkSpectatorDiagramAverage HistorySignedSpectatorDiagramAverage

theorem exists_actual_good_main_budget (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
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
      goodMainPrefactor Bs BD Bz L k l *
        ‖average (fun roots : UnitPair outside.prod =>
          average (unitTest h g hs gs hp hV σ (residueTransform d) roots))‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  obtain ⟨ε, hε, he⟩ := exists_good_product_dyadic_budget Bs BD Bz H hBs hk hH
  refine ⟨ε, hε, ?_⟩
  filter_upwards [he, (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hL hm
  intro l hl outside hlen h g hs gs hp hV σ hthree hgood hlog hcorr
  have := outsideNeZero hp
  have := primeAtNeZero hp
  have hm0 : 0 < 2*(bulkSize k L/2) := by
    have heven : 2*(bulkSize k L/2) = bulkSize k L := by unfold bulkSize; omega
    rw [heven]
    have : (0:ℝ) < bulkSize k L := by linarith
    exact_mod_cast this
  have hD := actual_unit_average_good d h g hs gs hp hV σ hm0 hthree hgood
  apply (mul_le_mul_of_nonneg_left hD (goodMainPrefactor_nonneg Bs BD Bz L k l)).trans
  exact hL l hl outside hlen
    (fun i => (FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ))
    (fun i => (hp _ (List.get_mem outside i)).pos) hlog (fun _ => NNReal.coe_nonneg _) hcorr

end Ostmann.Arithmetic.HistorySelectedGoodMainBudget

end

end OAI
