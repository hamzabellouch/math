import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegration
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMeanCovariance

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean HistorySignedXiTransport
open HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Seed Current Choices history)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def fibreAssignment (a : SelectedNonbulkSample C l) (y : SelectedBulkSample C l) :
    SourceAssignment C.sources (SelectedTemplate k L l) :=
  (selectedSourceEquiv C l).symm (a,y)

def permuteAssignment
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (x : SourceAssignment C.sources (SelectedTemplate k L l)) :=
  sourceAssignmentPermutation C.sources (SelectedTemplate k L l)
    (selectedLeafPermutation C l σ) (selectedLeafPermutation_source C l σ) x

variable (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)

def fibreTerm (y : SelectedBulkSample C l) (P Q : ℤ) : ℂ :=
  sourceIntegrand d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) outside l
    (sourceState C.sources _ (fibreAssignment C a y) s)
    (sourceState C.sources _ (permuteAssignment C σ (fibreAssignment C a y)) t)
    c e (fun _ _ => 1) (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter
    P Q

def FibreSupported (y : SelectedBulkSample C l) (P Q : ℤ) : Prop :=
  (history C (fibreAssignment C a y) s P Q c).Supported (frequencyBound Bs BD Bz k L) outside ∧
  (history C (permuteAssignment C σ (fibreAssignment C a y)) t P Q e).Supported
    (frequencyBound Bs BD Bz k L) outside

theorem fibreTerm_ne_zero_supported (y : SelectedBulkSample C l) (P Q : ℤ)
    (h : fibreTerm C outside σ a s t c e y P Q ≠ 0) :
    FibreSupported C outside σ a s t c e y P Q := by
  have hh : supportedHistoryPairXi d (frequencyBound Bs BD Bz k L) outside
      (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
      (history C (fibreAssignment C a y) s P Q c)
      (history C (permuteAssignment C σ (fibreAssignment C a y)) t P Q e) ≠ 0 := by
    simpa only [fibreTerm,sourceIntegrand,one_mul,history] using h
  constructor
  · by_contra hn
    apply hh
    simp only [supportedHistoryPairXi,hn,dite_false]
  · by_contra hn
    apply hh
    simp only [supportedHistoryPairXi,hn,dite_false]
    split <;> rfl

def primeFibreMean : ℂ :=
  (selectedBulkPrior C l).cmean (fun y =>
    primeMean C.giant (fibreTerm C outside σ a s t c e y))

def mixedFibreMean : ℂ :=
  (selectedBulkPrior C l).cmean (fun y =>
    mixedMean C.giantCenter C.giant (fibreTerm C outside σ a s t c e y))

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
