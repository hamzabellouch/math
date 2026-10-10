import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsAmplitude

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected
open Construction Conclusion HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairGiantCoordinates HistoryPairSmoothXi HistoryProductWindows
open HistoryGiantPriorGrid HistoryGiantXiPriorReplacement HistorySignedResidues
open HistoryPrincipalIntegralAverage HistoryCRTIntegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k₀ L E)

def primeScalar (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) : (Bool → ℝ) → ℂ :=
  reindexedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    (giantCoordinates h k) (pairBackground h k) (boolEquiv h k)

def mixedScalar (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) : (Option Unit → ℝ) → ℂ :=
  reindexedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    (giantCoordinates h k) (pairBackground h k) (optionEquiv h k)

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

end Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected

end

end OAI
