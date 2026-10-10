import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsAmplitude

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairGiantCoordinates HistoryPairSmoothXi HistoryProductWindows
open HistoryGiantPriorGrid HistoryGiantXiPriorReplacement HistorySignedResidues
open HistoryPrincipalIntegralAverage HistoryCRTIntegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k₀ L E)

def referenceAmplitude (l : ℕ) : ℝ :=
  Real.exp ((nominalInheritedWidth k₀ l+2)+nominalRemovedWidth k₀ l)*
    Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k₀ L+sourceXiConstant l k₀ (2+2*(k₀:ℝ)))

def referenceDerivative (h k : History l) (priorCells : List Bool) : ℝ :=
  correctedPairDerivativeBound (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
    (pairedDiagonalHKeys h k (l+1)).length (pairedDiagonalUKeys h k (l+1)).length
    (Fintype.card (Fin (diagonalCellKeys k (l+1)).length ⊕ Fin priorCells.length)) h k
    (frequencyBound Bs BD Bz k₀ L) (bulkSize k₀ L/2) k₀ C.bulkBin (initialGap Bs k₀ L)
    (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2))

def primeScalar (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) : (Bool → ℝ) → ℂ :=
  reindexedCorrectedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l) (C.compensationLogScale l)
    (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
    (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) (giantCoordinates h k) (pairBackground h k) (boolEquiv h k)

def mixedScalar (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) : (Option Unit → ℝ) → ℂ :=
  reindexedCorrectedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l) (C.compensationLogScale l)
    (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
    (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) (giantCoordinates h k) (pairBackground h k) (optionEquiv h k)

def primeDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M) : ℂ :=
  sourcePrimeMean (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k
    C.giantCenter deleted hZ M hd (primeScalar C s h k hs ks) -
  primeIntegral (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter deleted) (primeCutoff C.giantCenter (primeScalar C s h k hs ks))*
    ResidueHaar.average (fun z : UnitPair M => liftedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k₀ L) outside h k M hd ((z.1:ZMod M),(z.2:ZMod M)))

def mixedDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M) : ℂ :=
  sourceMixedMean (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k
    C.giantCenter deleted hZ M hd (mixedScalar C s h k hs ks) -
  mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
    (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter deleted)
    (mixedGiantPrimeTest C.giantCenter (mixedScalar C s h k hs ks))*
    ResidueHaar.average (fun z : MixedPair M => liftedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k₀ L) outside h k M hd (z.1,(z.2:ZMod M)))

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
