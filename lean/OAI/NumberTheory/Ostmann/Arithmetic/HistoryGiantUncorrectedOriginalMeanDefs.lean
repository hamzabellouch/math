import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorizationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean
open Construction Conclusion HistorySignedResidues HistorySignedXiTransport HistorySymbolicEncoding
open HistoryGiantReferenceMean HistoryGiantPriorGrid HistoryGiantXiReplacementUncorrected
open HistoryGiantOriginalMeanFactorization (Seed Current Choices history compensationFactor compensationFactor_eq)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def originalPrimeMean (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  primeMean C.giant (sourceIntegrand d C.sources _ (frequencyBound Bs BD Bz k L) outside l
    (sourceState C.sources _ x s) (sourceState C.sources _ y t) c e
    (fun _ _ => 1) (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter)

def originalMixedMean (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  mixedMean C.giantCenter C.giant
    (sourceIntegrand d C.sources _ (frequencyBound Bs BD Bz k L) outside l
      (sourceState C.sources _ x s) (sourceState C.sources _ y t) c e
      (fun _ _ => 1) (bulkSize k L/2) (bulkSize k L/2)
      C.scale C.bulkBin C.spectatorBin C.giantCenter)

variable (outside : List ℕ)
variable (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
variable (s t P Q : ℤ) (c e : Choices (l:=l) C)
variable (hs : (history C x s P Q c).Supported (frequencyBound Bs BD Bz k L) outside)
variable (gs : (history C y t P Q e).Supported (frequencyBound Bs BD Bz k L) outside)

theorem prime_reference_factor (n : ℕ) :
    primeMean C.giant (referenceTerm d (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) hs gs n
        (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter) =
    (((history C x s P Q c).compensationProduct:ℂ)*
      ((history C y t P Q e).compensationProduct:ℂ))*
      guardedSourcePrimeMean (residueTransform d) (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) C.giantCenter ∅ C.giantPositive
        (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n)
        (pairModulus_dvd_comparisonModulus _ _ _ n)
        (primeScalar C (bulkSize k L/2) _ _ hs gs) := by
  exact prime_referenceMean_eq_guarded d _ outside _ _ hs gs n
    (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
    ∅ C.giantPositive

theorem mixed_reference_factor (n : ℕ) :
    mixedMean C.giantCenter C.giant (referenceTerm d (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) hs gs n
        (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter) =
    (((history C x s P Q c).compensationProduct:ℂ)*
      ((history C y t P Q e).compensationProduct:ℂ))*
      guardedSourceMixedMean (residueTransform d) (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) C.giantCenter ∅ C.giantPositive
        (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n)
        (pairModulus_dvd_comparisonModulus _ _ _ n)
        (mixedScalar C (bulkSize k L/2) _ _ hs gs) := by
  exact mixed_referenceMean_eq_guarded d _ outside _ _ hs gs n
    (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
    ∅ C.giantPositive

end Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean

end

end OAI
