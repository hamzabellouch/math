import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSelectedInputs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetCounts

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryPairReferenceSourceTransport
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRows HistoryPairKernelReplacement
open HistoryPairSourceCoordinates HistoryPairRepresentativeVariables Filter
attribute [local instance] Classical.propDecidable
local instance kernelSelectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_principal_kernel_error_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀l (corrected mixed : Bool),(if corrected then l<k else l≤k) →
      ∀outside : List ℕ,(∀p∈outside,0<p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀F : (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        MatchedPrincipalBlockFamily C outside l f g p,
      (∀f g p i hi,RootGiantsAgree ((F f g p).reference i hi).left.history
        ((F f g p).reference i hi).right.history) →
      ∀mask : (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        OriginalDraw (fun _ : Bool=>C.giant) C.sources
          (Template.initial (2*(bulkSize k L/2)) k) l p→Prop,
      (∑f,∑g,∑p,‖principalDifferenceMean (F f g p) corrected mixed (mask f g p)‖) ≤
        (2:ℝ)^(4*k*2^k)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [selected_matched_principal_pattern_frequency_error_eventually d Bs BD Bz hBs hk,
    HistoryBulkSupportConverse.selected_source_inputs_eventually d Bs BD Bz hk] with L hflags hinputs
  intro E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl outside hpos hlen hlog F hroot mask
  have hl' : l≤k := by
    cases corrected with
    | false => exact hl
    | true => exact Nat.le_of_lt hl
  have hsource := hinputs E C hG hcl hcu hb hd spectator hspec
  have hV : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j) :=
    fun j hj=>hsource.2.1 j (hj.trans hl')
  have hcount (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) :
      Fintype.card (Block p)≤4*k*2^k := by
    calc
      _ ≤ Fintype.card (Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) := card_block_le p
      _ = 4*l*2^l := HistoryCompensationNormalizationBudget.paired_internal_card _ k l hl'
      _ ≤ 4*k*2^k := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hl')
        (Nat.pow_le_pow_right (by norm_num : 1≤(2:ℕ)) hl')
  calc
    _ ≤ ∑f,∑g,∑p,(2:ℝ)^(4*k*2^k)*(4*(F f g p).mean corrected mixed) := by
      apply Finset.sum_le_sum
      intro f _
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro p _
      exact (principalDifferenceMean_le (F f g p) corrected mixed hsource.1
        (hroot f g p) hV (mask f g p)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hcount p))
          (mul_nonneg (by norm_num) (principalFlagMean_nonneg (F f g p) corrected mixed)))
    _ = (2:ℝ)^(4*k*2^k)*(∑f,∑g,∑p,4*(F f g p).mean corrected mixed) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hflags E C hG hGu hcl hcu hb hd l corrected mixed hl outside hpos hlen hlog F)
      (pow_nonneg (by norm_num) _)

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
