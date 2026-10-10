import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationFibreIdentities
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMeanBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter ScaleBudget
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryGiantReferenceMean
open HistoryBulkReferencePeriodicMeanSource HistoryGiantOriginalMeanFactorization
open HistoryBulkIndependentFibreReference HistoryDiagonalRemainingRootMatching

open HistoryBulkFibreGiantApproximation

theorem corrected_witness_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
    ∀ l<depth,∀(a : SelectedNonbulkSample C l)
      (e : RemainingPermutation (k:=depth) (L:=L) (l:=l))
      (he : PreservesRemainingBands _ e) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)
      (ha : 0<(selectedNonbulkPrior C l).mass a)
      (hc₁ : choicesMass C.sources _ (frequencyBound Bs BD Bz depth L) l c₁≠0)
      (hc₂ : choicesMass C.sources _ (frequencyBound Bs BD Bz depth L) l c₂≠0),
    ∀ r : HistoryBulkActualCorrectedReferenceFamily.Witness C
      (spectatorList spectator ds) a e s t c₁ c₂,
      ‖mixedFibreMean C (spectatorList spectator ds) a e s t c₁ c₂ -
        correctedWitnessPrincipal C (spectatorList spectator ds) a e he s t c₁ c₂ r
          ha hc₁ hc₂ (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)‖ ≤
        pairedChoiceCompensation C c₁ c₂ *
          (9*Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [frame_corrected_mixed_source_error_eventually d Bs BD Bz hBs hdepth,
    HistoryBulkActualCorrectedReferenceFamily.selected_witness_equality_eventually
      d Bs BD Bz hdepth] with L hAP hselect
  intro E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl a e he s t c₁ c₂ ha hc₁ hc₂ old
  have hout : ∀q∈spectatorList spectator ds,∃p:spectator.Sample,(p:ℕ)=q := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨ds i,rfl⟩
  have hmean := (hselect E C hG hcl hcu hb hd spectator hspec (spectatorList spectator ds)
    hout l (Nat.le_of_lt hl) a e he s t c₁ c₂ ha hc₁ hc₂ old).2
  let hp := HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds
  let r := correctedFrame C (spectatorList spectator ds) a e s t c₁ c₂ old ha he hc₁ hc₂ hp
  have heq : mixedFibreMean C (spectatorList spectator ds) a e s t c₁ c₂ =
      (selectedBulkPrior C l).cmean (fun u=>r.sourceMeanCorrectedMixed
        (bulkPermutation e he) (fibreAssignment C a u)
        (rightAssignment C a e u (reference_compatible_all C (spectatorList spectator ds)
          a e he s t c₁ c₂ old u))) :=
    hmean.trans (corrected_mixed_reference_mean C (spectatorList spectator ds) a e he s t c₁ c₂
      old ha hc₁ hc₂ r.outside_primes)
  have hbnd : ‖(selectedBulkPrior C l).cmean (fun u=>r.sourceMeanCorrectedMixed
        (bulkPermutation e he) (fibreAssignment C a u)
        (rightAssignment C a e u (reference_compatible_all C (spectatorList spectator ds)
          a e he s t c₁ c₂ old u))) -
      oldCompensation r.left r.right*(selectedBulkPrior C l).cmean (fun u=>
        let y := rightAssignment C a e u (reference_compatible_all C (spectatorList spectator ds)
          a e he s t c₁ c₂ old u)
        staticPairMask (r.newLeft (fibreAssignment C a u)) (r.newRight y) (spectatorList spectator ds) *
          r.principalCorrectedMixed (bulkPermutation e he) (fibreAssignment C a u) y)‖ ≤
      ((r.left.compensationProduct:ℝ)*(r.right.compensationProduct:ℝ))*
        (9*Real.exp (-Real.exp (giant.target*L))) := by
    apply cmean_error_of_fixed_factor
    intro u hu
    exact hAP E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl r (bulkPermutation e he)
      (fibreAssignment C a u)
      (rightAssignment C a e u (reference_compatible_all C (spectatorList spectator ds)
        a e he s t c₁ c₂ old u))
      (fullPermutation (l+1) _ e he)
      (counterpartCurrentAssignment_value C _ e he old.compatible)
      (counterpartCurrentAssignment_value C _ e he _)
      (ne_of_gt (fibreAssignment_mass_pos C a u ha
        (lt_of_le_of_ne ((selectedBulkPrior C l).mass_nonneg u) (Ne.symm hu))))
      (fibreAssignment_nonbulk_fixed C a u old.bulk)
  rw [←heq] at hbnd
  simpa only [correctedWitnessPrincipal, HistoryBulkActualCorrectedReferenceFamily.witnessFrame,
    frame_left_compensation, frame_right_compensation, pairedChoiceCompensation,
    r, hp, correctedFrame] using hbnd

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
