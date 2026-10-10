import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMeanBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedWitness

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter ScaleBudget
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryGiantReferenceMean
open HistoryBulkReferencePeriodicMeanSource HistoryGiantOriginalMeanFactorization
open HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily (Draws Index leftChoices rightChoices)
open HistoryBulkIndependentFibreReference

theorem corrected_selected_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
    ∀ (l : ℕ) (_hl : l<depth),∀(e : RemainingPermutation (k:=depth) (L:=L) (l:=l))
      (he : PreservesRemainingBands _ e)
      (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
      (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=depth) (L:=L) (l:=l)),
      0 < (selectedNonbulkPrior C l).mass a →
      (internalSourcePrior C.sources (Template.initial (2*(bulkSize depth L/2)) depth) l).mass x≠0 →
      (internalSourcePrior C.sources (Template.initial (2*(bulkSize depth L/2)) depth) l).mass y≠0 →
      ‖correctedOriginalValue C spectator e ds a x y i -
        correctedSelectedPrincipal C spectator e he ds a x y i‖ ≤
        pairedChoiceCompensation C (leftChoices C x i) (rightChoices C y i) *
          (30*Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [corrected_witness_error_eventually d Bs BD Bz hBs hdepth] with L hAP
  intro E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl e he a x y i ha hx hy
  rw [correctedSelectedPrincipal,dite_eq_left ha,dite_eq_left hx,dite_eq_left hy]
  generalize hR : HistoryBulkActualCorrectedReferenceFamily.selectWitness C
    (spectatorList spectator ds) a e i.1.val i.1.val (leftChoices C x i) (rightChoices C y i) ha = R
  cases R with
  | none =>
    have hz := (HistoryBulkActualCorrectedReferenceFamily.selectWitness_none_iff C
      (spectatorList spectator ds) a e i.1.val i.1.val (leftChoices C x i) (rightChoices C y i) ha).mp hR
    simp only [correctedOriginalValue,hz,Option.elim_none,sub_self,norm_zero]
    exact mul_nonneg (pairedChoiceCompensation_nonneg C _ _) (by positivity)
  | some r =>
    have h := hAP E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl a e he
      i.1.val i.1.val (leftChoices C x i) (rightChoices C y i) ha
      (leftChoices_mass_of_draws C x hx i) (rightChoices_mass_of_draws C y hy i) r
    have h' := h.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by norm_num : (9:ℝ)≤30) (Real.exp_nonneg _))
        (pairedChoiceCompensation_nonneg C _ _))
    simpa only [correctedOriginalValue,Option.elim_some] using h'

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
