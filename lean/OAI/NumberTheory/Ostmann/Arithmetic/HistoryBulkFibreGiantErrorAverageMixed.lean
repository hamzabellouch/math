import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMeanBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAveragePrincipal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter ScaleBudget
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryGiantReferenceMean
open HistoryBulkReferencePeriodicMeanSource HistoryGiantOriginalMeanFactorization
open HistoryBulkFibreGiantApproximation HistoryBulkActualRootReferenceFamily

theorem mixed_witness_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
    ∀ l≤depth,∀(σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
      (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
      (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=depth) (L:=L) (l:=l))
      (r : Witness C (spectatorList spectator ds) σ a x y
        (fun i => plainMixedWeight C (spectatorList spectator ds) a i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
      (ha : 0 < (selectedNonbulkPrior C l).mass a)
      (hc : choicesMass C.sources _ _ l (leftChoices C x i)≠0)
      (he : choicesMass C.sources _ _ l (rightChoices C y i)≠0),
      ‖wholeMean C (spectatorList spectator ds) σ a x y
          (fun i => plainMixedWeight C (spectatorList spectator ds) a i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i -
        mixedWitnessPrincipal C (spectatorList spectator ds) σ a x y r ha hc he
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)‖ ≤
        pairedChoiceCompensation C (leftChoices C x i) (rightChoices C y i) *
          (9*Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [frame_mixed_source_error_eventually
    d Bs BD Bz hBs hdepth] with L hAP
  intro E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl σ a x y i r ha hc he
  let hp := HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds
  let f := mixedWitnessFrame C (spectatorList spectator ds) σ a x y
    (fun i => plainMixedWeight C (spectatorList spectator ds) a i.1.val) r ha hc he hp
  have heq := mixedWitnessMean_eq_source C (spectatorList spectator ds) σ a x y r ha hc he hp
  have hbnd : ‖(selectedBulkPrior C l).cmean (fun u=>f.sourceMeanMixed σ
      (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u))) -
      oldCompensation f.left f.right * (selectedBulkPrior C l).cmean (fun u=>
        staticPairMask (f.newLeft (fibreAssignment C a u))
          (f.newRight (permuteAssignment C σ (fibreAssignment C a u))) (spectatorList spectator ds)*
          f.principalMixed σ (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u)))‖ ≤
      ((f.left.compensationProduct:ℝ)*(f.right.compensationProduct:ℝ))*
        (9*Real.exp (-Real.exp (giant.target*L))) := by
    apply cmean_error_of_fixed_factor
    intro u hu
    exact hAP E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl f σ
      (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u))
      (selectedLeafPermutation C l σ)
      (sourceAssignmentPermutation_val C.sources _ _ _ _)
      (ne_of_gt (fibreAssignment_mass_pos C a u ha
        (lt_of_le_of_ne ((selectedBulkPrior C l).mass_nonneg u) (Ne.symm hu))))
      (fibreAssignment_nonbulk_fixed C a u r.bulk)
  rw [←heq] at hbnd
  simpa only [mixedWitnessPrincipal,frame_left_compensation,frame_right_compensation,
    pairedChoiceCompensation, f, hp, mixedWitnessFrame, plainMixedFrame] using hbnd

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
