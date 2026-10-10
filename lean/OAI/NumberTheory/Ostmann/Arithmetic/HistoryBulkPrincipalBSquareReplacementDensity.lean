import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensitySelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementFrequency

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum Filter
attribute [local instance] Classical.propDecidable
local instance squareDensityFinalInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_density_B_replacement_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hBs : 0≤Bs) (hk : 2≤k) :
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
      ∀R : FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α → ReferenceFamily C outside l,
      ∀X : FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α → DensitySources C l,
      ∀mask : FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l → α →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        (Block p → CommonSample C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop,
      (∑f,∑g,‖μ.cmean (fun a=>densityBExpressionSum (R f g a) (X f g a) false corrected mixed (mask f g a))-
        μ.cmean (fun a=>densityBExpressionSum (R f g a) (X f g a) true corrected mixed (mask f g a))‖) ≤
        Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [selected_density_B_error_eventually d Bs BD Bz hBs hk,
    frequency_error_eventually Bs BD Bz (by omega : 0<k)] with L he hf
  intro E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl outside hpos hlen hlog
    α _ μ R X mask
  have hl' : l≤k := by
    cases corrected with
    | false => exact hl
    | true => exact Nat.le_of_lt hl
  apply hf l hl'
  intro f g
  rw [GiantCollisionError.cmean_sub_eq]
  simp_rw [densityBExpressionSum_sub]
  apply GiantCollisionError.norm_cmean_le_of_mass_ne_zero
  intro a _
  exact he E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl
    outside hpos hlen hlog (R f g a) (X f g a) (mask f g a)

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
