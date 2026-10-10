import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedIdentities
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedScalarDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter ScaleBudget
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily (Draws Index leftChoices rightChoices)
open HistoryBulkIndependentFibreReference

theorem selectedDiagonalCovariance_corrected_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    (hBs : 0≤Bs) (hH : 0≤H) {depth : ℕ} (hdepth : 0<depth) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ (l : ℕ) (_hl : l<depth)
      (e : RemainingPermutation (k:=depth) (L:=L) (l:=l))
      (he : PreservesRemainingBands _ e),
      ‖C.selectedDiagonalCovariance spectator (bulkSize depth L/2) C.scale l e -
        originalSourceAverage C spectator (correctedSelectedPrincipal C spectator e he)‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz depth L l-H*(bulkSize depth L:ℝ)) ∧
      ‖C.selectedDiagonalCovariance spectator (bulkSize depth L/2) C.scale l e -
        originalSourceAverage C spectator (correctedSelectedPrincipal C spectator e he)‖ ≤
        Real.exp (-H*(bulkSize depth L:ℝ)) := by
  filter_upwards [actual_corrected_error_eventually d Bs BD Bz H hBs hH hdepth] with L hL
  intro E C hG hGu hcl hcu hb hd spectator hspec l hl e he
  rw [selectedDiagonalCovariance_eq_originalSourceAverage C spectator e he]
  exact hL E C hG hGu hcl hcu hb hd spectator hspec l hl e he

theorem selectedDiagonalCovariance_guarded_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    (hBs : 0≤Bs) (hH : 0≤H) {depth : ℕ} (hdepth : 0<depth) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ (l : ℕ) (_hl : l<depth)
      (e : RemainingPermutation (k:=depth) (L:=L) (l:=l)),
      ‖C.selectedDiagonalCovariance spectator (bulkSize depth L/2) C.scale l e -
        correctedGuardedPrincipalAverage C spectator e‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz depth L l-H*(bulkSize depth L:ℝ)) ∧
      ‖C.selectedDiagonalCovariance spectator (bulkSize depth L/2) C.scale l e -
        correctedGuardedPrincipalAverage C spectator e‖ ≤
        Real.exp (-H*(bulkSize depth L:ℝ)) := by
  filter_upwards [selectedDiagonalCovariance_corrected_error_eventually
    d Bs BD Bz H hBs hH hdepth] with L hL
  intro E C hG hGu hcl hcu hb hd spectator hspec l hl e
  by_cases he : PreservesRemainingBands _ e
  · rw [correctedGuardedPrincipalAverage,dite_eq_left he]
    exact hL E C hG hGu hcl hcu hb hd spectator hspec l hl e he
  · rw [correctedGuardedPrincipalAverage,dite_eq_right he,
      selectedDiagonalCovariance_eq_guardedOriginalSourceAverage C spectator e,ite_eq_right he]
    simp only [sub_self,norm_zero]
    exact ⟨Real.exp_nonneg _,Real.exp_nonneg _⟩

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
