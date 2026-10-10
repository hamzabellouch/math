import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedDensitySelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootFlagErrorNumerics

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
open HistorySelectedRootFlagError
attribute [local instance] Classical.propDecidable
local instance matchedDensityRootFlagInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_root_density_principal_kernel_error_eventually (d : Decomposition)
    (Bs BD Bz D H : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0≤H) (hk : 0 < k) :
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
      ∀F : (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) →
        (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        MatchedPrincipalBlockFamily C outside l f g p,
      (∀v f g p i hi,RootGiantsAgree ((F v f g p).reference i hi).left.history
        ((F v f g p).reference i hi).right.history) →
      ∀X : ∀v f g p,DensitySources (F v f g p),
      ∀mask : (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) →
        (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        OriginalDraw (fun _ : Bool=>C.giant) C.sources
          (Template.initial (2*(bulkSize k L/2)) k) l p→Prop,
      Real.exp (D*(L+1)^2)*(∑v,∑f,∑g,∑p,
        ‖densityPrincipalDifferenceMean (F v f g p) (X v f g p) corrected mixed (mask v f g p)‖) ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      Real.exp (D*(L+1)^2)*(∑v,∑f,∑g,∑p,
        ‖densityPrincipalDifferenceMean (F v f g p) (X v f g p) corrected mixed (mask v f g p)‖) ≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_density_principal_kernel_error_eventually d Bs BD Bz hBs hk,
    selected_root_kernel_flag_error_eventually Bs BD Bz D H hH hk] with L hbase hbudget
  intro E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl outside hpos hlen hlog F hroot X mask
  have hl' : l≤k := by
    cases corrected with
    | false => exact hl
    | true => exact Nat.le_of_lt hl
  have hsum : (∑v,∑f,∑g,∑p,
      ‖densityPrincipalDifferenceMean (F v f g p) (X v f g p) corrected mixed (mask v f g p)‖) ≤
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
        ((2:ℝ)^(4*k*2^k)*Real.exp (-Real.exp ((3/2000:ℝ)*L))) := by
    calc
      _ ≤ ∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          (2:ℝ)^(4*k*2^k)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hbase E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl
          outside hpos hlen hlog (F v) (hroot v) (X v) (mask v)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hpaid : Real.exp (D*(L+1)^2)*(∑v,∑f,∑g,∑p,
      ‖densityPrincipalDifferenceMean (F v f g p) (X v f g p) corrected mixed (mask v f g p)‖) ≤
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
        (2:ℝ)^(4*k*2^k)*Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
    convert mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg (D*(L+1)^2)) using 1
    ring
  exact ⟨hpaid.trans (hbudget l hl').1,hpaid.trans (hbudget l hl').2⟩

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
