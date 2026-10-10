import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageBudgetSymbolic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter ScaleBudget
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily (Draws Index leftChoices rightChoices)
open HistoryBulkIndependentFibreReference

theorem actual_corrected_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
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
      ‖originalSourceAverage C spectator (correctedOriginalValue C spectator e) -
        originalSourceAverage C spectator (correctedSelectedPrincipal C spectator e he)‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz depth L l-H*(bulkSize depth L:ℝ)) ∧
      ‖originalSourceAverage C spectator (correctedOriginalValue C spectator e) -
        originalSourceAverage C spectator (correctedSelectedPrincipal C spectator e he)‖ ≤
        Real.exp (-H*(bulkSize depth L:ℝ)) := by
  filter_upwards [corrected_selected_error_eventually d Bs BD Bz hBs hdepth,
    selected_nested_symbolic_error_eventually d Bs BD Bz H hH hdepth]
      with L hpoint hbudget
  intro E C hG hGu hcl hcu hb hd spectator hspec l hl e he
  have h := hbudget E C hG hcl hcu hb hd l (Nat.le_of_lt hl)
    (Fin (2*(bulkSize depth L/2))→spectator.Sample) (SelectedNonbulkSample C l)
    (spectatorPrior spectator (2*(bulkSize depth L/2))) (fun _=>selectedNonbulkPrior C l)
    (correctedOriginalValue C spectator e) (correctedSelectedPrincipal C spectator e he) (by
      intro ds hds a ha x y hx hy i
      exact hpoint E C hG hGu hcl hcu hb hd spectator hspec ds
        (spectator_mass_ne_zero spectator ds hds) l hl e he a x y i
        (lt_of_le_of_ne ((selectedNonbulkPrior C l).mass_nonneg a) (Ne.symm ha)) hx hy)
  simpa only [originalSourceAverage] using h

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
