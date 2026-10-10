import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootFlagErrorNumerics

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum Filter HistorySelectedRootFlagError
attribute [local instance] Classical.propDecidable
local instance squareDensityRootInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_root_density_B_replacement_eventually (d : Decomposition)
    (Bs BD Bz D H : ℝ) {k : ℕ} (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop, ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
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
      ∀(α : Type) [Fintype α](μ : FinitePrior α),
      ∀R : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α → ReferenceFamily C outside l,
      ∀X : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α → DensitySources C l,
      ∀mask : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        (Block p → CommonSample C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop,
      Real.exp (D*(L+1)^2)*(∑v,∑f,∑g,‖μ.cmean (fun a=>densityBExpressionSum (R v f g a) (X v f g a) false corrected mixed (mask v f g a))-
        μ.cmean (fun a=>densityBExpressionSum (R v f g a) (X v f g a) true corrected mixed (mask v f g a))‖) ≤
        Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      Real.exp (D*(L+1)^2)*(∑v,∑f,∑g,‖μ.cmean (fun a=>densityBExpressionSum (R v f g a) (X v f g a) false corrected mixed (mask v f g a))-
        μ.cmean (fun a=>densityBExpressionSum (R v f g a) (X v f g a) true corrected mixed (mask v f g a))‖) ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_density_B_replacement_eventually d Bs BD Bz hBs hk,
    selected_root_flag_error_eventually Bs BD Bz 1 D H (by norm_num) hH
      (by omega : 0<k)] with L hbase hbudget
  intro E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl outside hpos hlen hlog
    α _ μ R X mask
  have hl' : l≤k := by
    cases corrected with
    | false => exact hl
    | true => exact Nat.le_of_lt hl
  let err (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) : ℝ :=
    ∑f,∑g,‖μ.cmean (fun a=>densityBExpressionSum (R v f g a) (X v f g a) false corrected mixed (mask v f g a))-
      μ.cmean (fun a=>densityBExpressionSum (R v f g a) (X v f g a) true corrected mixed (mask v f g a))‖
  have hsum : (∑v,err v)≤
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
        Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
    calc
      _ ≤ ∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
        apply Finset.sum_le_sum
        intro v _
        exact hbase E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl
          outside hpos hlen hlog α μ (R v) (X v) (mask v)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hpaid : Real.exp (D*(L+1)^2)*(∑v,err v)≤
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*1*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
    convert mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg (D*(L+1)^2)) using 1
    ring
  exact ⟨hpaid.trans (hbudget l hl').1,hpaid.trans (hbudget l hl').2⟩

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
