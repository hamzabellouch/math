import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximation
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) (a : SelectedNonbulkSample C l)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀j,(expand p b j).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)
  (ha : 0<(selectedNonbulkPrior C l).mass a)
  (hx : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass (leftDraws C p b hb)≠0)
  (hy : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass (rightDraws C p b hb)≠0)
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)

theorem primeSelectedPrincipal_patternValue_eq_option :
    drawPatternValue C spectator (primeSelectedPrincipal C spectator hactual hl σ) ds a i p b.val =
      (selectWitness C (spectatorList spectator ds) σ a
        (leftDraws C p b hb) (rightDraws C p b hb) (fun _ _ _ _=>1)
        (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
        hactual hl ha (leftChoices_mass_of_draws C _ hx) (rightChoices_mass_of_draws C _ hy)
        (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
        (fun r _=>primeDraw_positive C.giant r) i).elim 0
        (fun r=>primeWitnessPrincipal C (spectatorList spectator ds) σ a
          (leftDraws C p b hb) (rightDraws C p b hb) r ha
          (leftChoices_mass_of_draws C _ hx i) (rightChoices_mass_of_draws C _ hy i)
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) / blockJacobian C p b := by
  rw [drawPatternValue_of_valid C spectator _ ds a i p b hb]
  simp only [primeSelectedPrincipal,dite_eq_left ha,dite_eq_left hx,dite_eq_left hy]

theorem mixedSelectedPrincipal_patternValue_eq_option :
    drawPatternValue C spectator (mixedSelectedPrincipal C spectator hactual hl σ) ds a i p b.val =
      (selectWitness C (spectatorList spectator ds) σ a
        (leftDraws C p b hb) (rightDraws C p b hb)
        (fun i=>plainMixedWeight C (spectatorList spectator ds) a i.1.val)
        (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
        hactual hl ha (leftChoices_mass_of_draws C _ hx) (rightChoices_mass_of_draws C _ hy)
        (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
        (fun r _=>mixedDraw_positive C.giantCenter C.giant r) i).elim 0
        (fun r=>mixedWitnessPrincipal C (spectatorList spectator ds) σ a
          (leftDraws C p b hb) (rightDraws C p b hb) r ha
          (leftChoices_mass_of_draws C _ hx i) (rightChoices_mass_of_draws C _ hy i)
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) / blockJacobian C p b := by
  rw [drawPatternValue_of_valid C spectator _ ds a i p b hb]
  simp only [mixedSelectedPrincipal,dite_eq_left ha,dite_eq_left hx,dite_eq_left hy]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern

end

end OAI
