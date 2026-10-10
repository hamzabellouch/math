import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily (Draws Index leftChoices rightChoices)
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def correctedOriginalValue (spectator : PrimeSource)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : ℂ :=
  mixedFibreMean C (spectatorList spectator ds) a e i.1.val i.1.val
    (leftChoices C x i) (rightChoices C y i)

def correctedSelectedPrincipal (spectator : PrimeSource)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : ℂ :=
  if ha : 0<(selectedNonbulkPrior C l).mass a then
    if hx : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass x≠0 then
      if hy : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass y≠0 then
        (HistoryBulkActualCorrectedReferenceFamily.selectWitness C (spectatorList spectator ds)
          a e i.1.val i.1.val (leftChoices C x i) (rightChoices C y i) ha).elim 0
          (fun r=>correctedWitnessPrincipal C (spectatorList spectator ds) a e he
            i.1.val i.1.val (leftChoices C x i) (rightChoices C y i) r ha
            (leftChoices_mass_of_draws C x hx i) (rightChoices_mass_of_draws C y hy i)
            (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds))
      else 0
    else 0
  else 0

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
