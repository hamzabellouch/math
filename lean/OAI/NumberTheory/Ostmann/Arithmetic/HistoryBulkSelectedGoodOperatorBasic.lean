import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementMeans
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGoodMainBudgetRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSelectedGoodOperator
open Construction Conclusion Filter ResidueHaar HistoryCRTIntegration
open HistorySelectedGoodMainBudget HistoryGiantFrequencyCount HistorySelectedJointIntegralBounds
open HistoryBulkSelectedIntegralReplacement HistoryBulkReplacementGeometry
open HistoryBulkSpectatorProduct HistoryBulkSpectatorDiagramAverage HistorySignedSpectatorDiagramAverage
open HistoryRepresentativeSourceSeparation HistoryBulkResidueNormSum

def principalPayment (Bs BD Bz L : ℝ) (k l : ℕ) : ℝ :=
  (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)*
    Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ))

theorem principalPayment_nonneg (Bs BD Bz L : ℝ) (k l : ℕ) :
    0 ≤ principalPayment Bs BD Bz L k l := by unfold principalPayment; positivity

theorem paid_principal_le (Bs BD Bz L : ℝ) (k l : ℕ) (I z : ℂ)
    (hI : ‖I‖ ≤ 64*(2:ℝ)^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l) :
    principalPayment Bs BD Bz L k l*‖I*z‖ ≤ rootFrequencyPrefactor Bs BD Bz L k l*‖z‖ := by
  rw [norm_mul]
  calc
    _ ≤ principalPayment Bs BD Bz L k l*
        ((64*(2:ℝ)^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)*‖z‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hI (norm_nonneg _))
        (principalPayment_nonneg Bs BD Bz L k l)
    _ = _ := by
      unfold principalPayment rootFrequencyPrefactor mainAmplitude correctedAmplitude
      ring

theorem exists_rootTest_good_operator_budget (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0 ≤ Bs) (hk : 0 < k) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ l : ℕ, l ≤ k → ∀ (outside : List ℕ), outside.length = bulkSize k L →
      ∀ (h g : History l)
        (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
        (gs : g.Supported (frequencyBound Bs BD Bz k L) outside)
        (hp : ∀ q ∈ outside, q.Prime)
        (hV : ∀ q ∈ outside, ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q)
        (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
        (K : ℕ) (_had : PairAdmissible h g outside),
      letI : NeZero (bulkModulus h g outside K) :=
        ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
      letI := primeAtNeZero hp
      (∀ q ∈ outside, 3 ≤ q) → ¬TransferBadArrangement σ →
      (∀ i : Fin outside.length, Real.exp (L/2000) ≤ Real.log (outside.get i:ℝ)) →
      (∀ i : Fin outside.length,
        (FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ) ≤ ε) →
      ∀ (mixed : Bool) (I : ℂ),
      ‖I‖ ≤ 64*(2:ℝ)^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l →
      principalPayment Bs BD Bz L k l*
        ‖I*average (rootTest true mixed d h g hs gs hp hV σ K)‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  have ht : 0 ≤ H+2*actualFrequencyCost Bs BD Bz k := by
    linarith [actualFrequencyCost_pos Bs BD Bz hk]
  obtain ⟨ε,hε,he⟩ := exists_good_product_dyadic_budget Bs BD Bz
    (H+2*actualFrequencyCost Bs BD Bz k) hBs hk ht
  refine ⟨ε,hε,?_⟩
  filter_upwards [he, eventually_extraRootFrequency_le Bs BD Bz hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L hL hF hm hL0
  intro l hl outside hlen h g hs gs hp hV σ K had hthree hgood hlog hcorr mixed I hI
  have : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
  have := primeAtNeZero hp
  have hm0 : 0 < 2*(bulkSize k L/2) := by
    have heven : 2*(bulkSize k L/2)=bulkSize k L := by unfold bulkSize; omega
    rw [heven]
    have hh : (0:ℝ) < bulkSize k L := by linarith
    exact_mod_cast hh
  let D := ∏ i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
    ((FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ)+
      (primeAt outside i:ℝ)^(-(1/4:ℝ)))
  have hD : ‖average (rootTest true mixed d h g hs gs hp hV σ K)‖ ≤ D := by
    cases mixed
    · exact rootTest_independent_unit_average_le d h g hs gs hp hV σ K had hm0 hthree hgood
    · exact rootTest_independent_mixed_average_le d h g hs gs hp hV σ K had hm0 hthree hgood
  have hprod : goodMainPrefactor Bs BD Bz L k l*D ≤
      Real.exp (-(H+2*actualFrequencyCost Bs BD Bz k)*(2:ℝ)^l*(bulkSize k L:ℝ)) :=
    hL l hl outside hlen
      (fun i => (FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ))
      (fun i => (hp _ (List.get_mem outside i)).pos) hlog (fun _ => NNReal.coe_nonneg _) hcorr
  calc
    _ ≤ rootFrequencyPrefactor Bs BD Bz L k l*
        ‖average (rootTest true mixed d h g hs gs hp hV σ K)‖ :=
      paid_principal_le Bs BD Bz L k l I _ hI
    _ ≤ rootGoodMainPrefactor Bs BD Bz L k l*
        ‖average (rootTest true mixed d h g hs gs hp hV σ K)‖ :=
      mul_le_mul_of_nonneg_right (rootFrequencyPrefactor_le Bs BD Bz L k hL0
        (by exact_mod_cast hm) hl) (norm_nonneg _)
    _ ≤ rootGoodMainPrefactor Bs BD Bz L k l*D := by
      apply mul_le_mul_of_nonneg_left hD
      unfold rootGoodMainPrefactor correctedAmplitude
      positivity
    _ ≤ _ := extraRootFrequency_absorb Bs BD Bz H L hk hF hprod

theorem spectator_three_le {L : ℝ} (hL : 0 ≤ L) (q : ℕ) (hq : q.Prime)
    (hlog : Real.exp ((1/2000:ℝ)*L) ≤ Real.log (q:ℝ)) : 3 ≤ q := by
  by_contra hh
  have hq2 : q ≤ 2 := by omega
  have hlog2 : Real.log (q:ℝ) ≤ Real.log 2 :=
    Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast hq2)
  have he : (1:ℝ) ≤ Real.exp ((1/2000:ℝ)*L) := Real.one_le_exp (by positivity)
  linarith [Real.log_two_lt_d9]

end Ostmann.Arithmetic.HistoryBulkSelectedGoodOperator

end

end OAI
