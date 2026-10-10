import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns Filter
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkUniversalPatternAggregation
open HistorySelectedBulkErrorBudget
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance bulkPatternSelectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem patternComplexSum_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin τ : ι → ℕ)
    (F G : ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ F-patternComplexSum sources origin τ G=
      patternComplexSum sources origin τ (fun p b=>F p b-G p b) := by
  unfold patternComplexSum
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem selected_pattern_bulk_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop,∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
    ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀l ≤ k,∀(corrected mixed : Bool)
      (hV : ∀q∈spectatorList spectator ds,∀j ≤ l,frequencyBound Bs BD Bz k L j<q),
      (corrected=true → l<k) →
    ∀F : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
      Family C (spectatorList spectator ds) l p,
    let before := patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun p b=>familyValue false (F p b) b corrected mixed hV)
    let after := patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun p b=>familyValue true (F p b) b corrected mixed hV)
    ‖before-after‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖before-after‖ ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_weighted_bulkMean_error_eventually d Bs BD Bz hBs (by omega : 0<k),
    selected_patternComplexSum_eventually d Bs BD Bz hk,
    selected_paid_bulk_error_eventually Bs BD Bz H hH (by omega : 0<k)] with L hbulk hpattern hpay
  intro spectator hspec ds E C hG hGu hcl hcu hb hd l hl corrected mixed hV hstage F
  dsimp only
  rw [patternComplexSum_sub]
  have hA : 0 ≤ (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)*
      (192*Real.exp (-Real.exp (ScaleBudget.bulk.target*L))) := by positivity
  have hsum := hpattern E C hG hGu hcl hcu hb hd l hl
    (fun p b=>familyValue false (F p b) b corrected mixed hV-
      familyValue true (F p b) b corrected mixed hV) _ hA (by
        intro p b _ _
        apply familyValue_sub_norm_le _ _ _ _ _ _ (by positivity)
        intro i r _
        exact hbulk spectator hspec ds E C hG hcl l hl r.frame corrected mixed
          r.nonbulk r.permutation hV hstage)
  have hs : ‖patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun p b=>familyValue false (F p b) b corrected mixed hV-
        familyValue true (F p b) b corrected mixed hV)‖ ≤
      ((Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)*
        Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)))*
        (192*Real.exp (-Real.exp (ScaleBudget.bulk.target*L))) := by
    convert hsum using 1
    ring
  exact ⟨hs.trans (hpay l hl).1,hs.trans (hpay l hl).2⟩

end Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacement

end

end OAI
