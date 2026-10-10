import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensityBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSelectedInputs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum
open HistoryPairVariableBSquareErrorSelected HistoryBulkPrincipalCollisionError
open HistorySelectedPairDerivativeBounds Filter
attribute [local instance] Classical.propDecidable
local instance squareDensitySelectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_density_B_error_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hk : 2 ≤ k) :
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
      ∀(R : ReferenceFamily C outside l) (X : DensitySources C l)
        (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
          (Block p → CommonSample C.sources
            (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop),
      ‖densityBErrorSum R X corrected mixed mask‖ ≤
        Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  have hkpos : 0<k := by omega
  filter_upwards [selected_weightedOriginalDecodedBErrorSum_scaled_eventually d Bs BD Bz
      (selectedExponent Bs BD Bz k+64) 0 hk,
    selected_principalAmplitudeData_norm_eventually d Bs BD Bz hBs hkpos,
    HistoryBulkSupportConverse.selected_source_inputs_eventually d Bs BD Bz hkpos]
    with L herror hnorm hinputs
  intro E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl outside hpos hlen hlog R X mask
  have hl' : l≤k := by
    cases corrected with
    | false => exact hl
    | true => exact Nat.le_of_lt hl
  have hsource := hinputs E C hG hcl hcu hb hd spectator hspec
  have hV : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j) :=
    fun j hj=>hsource.2.1 j (hj.trans hl')
  apply herror E C hG hGu hcl hcu hb hd l hl' mixed
    (frequencyBound Bs BD Bz k L) outside hpos hlen hlog hsource.1 hV
    (squareReferences R) (fun p b=>if mask p b then 1 else 0)
    (by intro p b; split_ifs <;> norm_num) (densityAmplitude R X corrected mixed)
  intro p b
  simp only [zero_mul, Real.exp_zero,mul_one]
  calc
    ‖densityAmplitude R X corrected mixed p b‖ ≤ ‖principalAmplitude R corrected mixed p b‖ := by
      rw [densityAmplitude,norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_densityFactor_le X mixed p b.val) (norm_nonneg (principalAmplitude R corrected mixed p b))
    _ ≤ _ := by
      unfold principalAmplitude
      cases hr : R p b.val with
      | none => simp only [norm_zero]; positivity
      | some r => exact hnorm E C hG hcl outside l r.principal corrected mixed hl r.newBulk

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
