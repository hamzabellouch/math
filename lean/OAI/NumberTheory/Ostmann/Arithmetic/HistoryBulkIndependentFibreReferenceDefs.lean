import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanEnergyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanZeroMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreReference
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization (Current Seed Choices history counterpart)
open HistoryDiagonalSmallOriginalMean (smallAssignment smallMultiplier)
open HistoryDiagonalCorrectedOriginalMean hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

abbrev RemainingPermutation := Equiv.Perm (RemainingIndex
  (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))))

def Compatible (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (u : SelectedBulkSample C l) : Prop :=
  SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u)) e

def rightAssignment (a : SelectedNonbulkSample C l)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (u : SelectedBulkSample C l)
    (hc : Compatible C a e u) := counterpartCurrentAssignment C (fibreAssignment C a u) e hc

variable (outside : List ℕ) (a : SelectedNonbulkSample C l)
variable (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

def multiplier (u : SelectedBulkSample C l) (hc : Compatible C a e u) (P Q : ℤ) : ℂ :=
  (smallMultiplier C outside (fibreAssignment C a u) s P Q:ℂ)*
    counterpart C (rightAssignment C a e u hc) Q

def compatibleTerm (u : SelectedBulkSample C l) (hc : Compatible C a e u) (P Q : ℤ) : ℂ :=
  sourceIntegrand d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) outside l
    (sourceState C.sources _ (fibreAssignment C a u) s)
    (sourceState C.sources _ (rightAssignment C a e u hc) t) c₁ c₂
    (multiplier C outside a e s u hc) (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter P Q

def term (u : SelectedBulkSample C l) (P Q : ℤ) : ℂ :=
  if hc : Compatible C a e u then compatibleTerm C outside a e s t c₁ c₂ u hc P Q else 0

def mixedFibreMean : ℂ :=
  (selectedBulkPrior C l).cmean (fun u=>mixedMean C.giantCenter C.giant
    (term C outside a e s t c₁ c₂ u))

def Supported (u : SelectedBulkSample C l) (hc : Compatible C a e u) (P Q : ℤ) : Prop :=
  (history C (fibreAssignment C a u) s P Q c₁).Supported (frequencyBound Bs BD Bz k L) outside ∧
  (history C (rightAssignment C a e u hc) t P Q c₂).Supported (frequencyBound Bs BD Bz k L) outside

end Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

end

end OAI
