import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensityBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensityRoot

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns Filter
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum HistoryBulkPrincipalBSquareReplacement
attribute [local instance] Classical.propDecidable
local instance actualSquareBoundInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_root_density_B_replacement_interface (d : Decomposition)
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
        μ.cmean (fun a=>densityBExpressionSum (R v f g a) (X v f g a) true corrected mixed (mask v f g a))‖) ≤ Real.exp (-H*(bulkSize k L:ℝ)) :=
  selected_root_density_B_replacement_eventually d Bs BD Bz D H hBs hH hk

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
