import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageBudgetSymbolic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter ScaleBudget
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximation HistoryBulkActualRootReferenceFamily

theorem actual_prime_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
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
    ∃ hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
    ∀ (l : ℕ) (hl : l≤depth)
      (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l))),
      ‖originalSourceAverage C spectator (primeOriginalValue C spectator σ) -
        originalSourceAverage C spectator (primeSelectedPrincipal C spectator hactual hl σ)‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz depth L l-H*(bulkSize depth L:ℝ)) ∧
      ‖originalSourceAverage C spectator (primeOriginalValue C spectator σ) -
        originalSourceAverage C spectator (primeSelectedPrincipal C spectator hactual hl σ)‖ ≤
        Real.exp (-H*(bulkSize depth L:ℝ)) := by
  filter_upwards [prime_selected_error_eventually d Bs BD Bz hBs hdepth,
    selected_nested_symbolic_error_eventually d Bs BD Bz H hH hdepth,
    HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually d Bs BD Bz hdepth]
      with L hpoint hbudget href
  intro E C hG hGu hcl hcu hb hd spectator hspec
  let hactual := href E C hG hcl hcu hb hd spectator hspec
  refine ⟨hactual,?_⟩
  intro l hl σ
  have h := hbudget E C hG hcl hcu hb hd l hl
    (Fin (2*(bulkSize depth L/2))→spectator.Sample) (SelectedNonbulkSample C l)
    (spectatorPrior spectator (2*(bulkSize depth L/2))) (fun _=>selectedNonbulkPrior C l)
    (primeOriginalValue C spectator σ) (primeSelectedPrincipal C spectator hactual hl σ) (by
      intro ds hds a ha x y hx hy i
      exact hpoint E C hG hGu hcl hcu hb hd spectator hspec ds
        (spectator_mass_ne_zero spectator ds hds) l hl σ hactual a x y i
        (lt_of_le_of_ne ((selectedNonbulkPrior C l).mass_nonneg a) (Ne.symm ha)) hx hy)
  simpa only [originalSourceAverage] using h

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
