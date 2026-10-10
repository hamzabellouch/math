import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMeanBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAveragePrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter ScaleBudget
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryGiantReferenceMean
open HistoryBulkReferencePeriodicMeanSource HistoryGiantOriginalMeanFactorization
open HistoryBulkFibreGiantApproximation HistoryBulkActualRootReferenceFamily

theorem prime_selected_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0≤Bs) {depth : ℕ} (hdepth : 0<depth) :
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
    ∀ ds : Fin (2*(bulkSize depth L/2))→spectator.Sample,
      (∀i,spectator.law.mass (ds i)≠0) →
    ∀ (l : ℕ) (hl : l≤depth),∀(σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
      (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
      (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
      (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=depth) (L:=L) (l:=l)),
      0 < (selectedNonbulkPrior C l).mass a →
      (internalSourcePrior C.sources (Template.initial (2*(bulkSize depth L/2)) depth) l).mass x≠0 →
      (internalSourcePrior C.sources (Template.initial (2*(bulkSize depth L/2)) depth) l).mass y≠0 →
      ‖primeOriginalValue C spectator σ ds a x y i -
        primeSelectedPrincipal C spectator hactual hl σ ds a x y i‖ ≤
        pairedChoiceCompensation C (leftChoices C x i) (rightChoices C y i) *
          (30*Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [prime_witness_error_eventually d Bs BD Bz hBs hdepth] with L hAP
  intro E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl σ hactual a x y i ha hx hy
  rw [primeSelectedPrincipal,dite_eq_left ha,dite_eq_left hx,dite_eq_left hy]
  generalize hR : selectWitness C (spectatorList spectator ds) σ a x y (fun _ _ _ _ => 1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl ha (leftChoices_mass_of_draws C x hx) (rightChoices_mass_of_draws C y hy)
      (spectatorList_source spectator ds) (primeWeight_nonneg C.giant) (fun r _=>primeDraw_positive C.giant r) i = R
  cases R with
  | none =>
    have hz := (selectWitness_none_iff C (spectatorList spectator ds) σ a x y
      (fun _ _ _ _ => 1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) hactual hl ha
      (leftChoices_mass_of_draws C x hx) (rightChoices_mass_of_draws C y hy)
      (spectatorList_source spectator ds) (primeWeight_nonneg C.giant) (fun r _=>primeDraw_positive C.giant r) i).mp hR
    simp only [primeOriginalValue,hz,Option.elim_none,sub_self,norm_zero]
    exact mul_nonneg (pairedChoiceCompensation_nonneg C _ _) (by positivity)
  | some r =>
    have h := hAP E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl σ a x y i r ha
      (leftChoices_mass_of_draws C x hx i) (rightChoices_mass_of_draws C y hy i)
    simpa only [primeOriginalValue,Option.elim_some] using h

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
