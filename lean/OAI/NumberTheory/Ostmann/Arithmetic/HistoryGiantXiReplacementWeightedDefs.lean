import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsAmplitude

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted
open HistoryGiantXiReplacementUncorrected HistoryGiantWeightedPriorReplacement
open Construction Conclusion HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairGiantCoordinates HistoryPairSmoothXi HistoryProductWindows
open HistoryGiantPriorGrid HistoryGiantXiPriorReplacement HistorySignedResidues
open HistoryPrincipalIntegralAverage HistoryCRTIntegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k₀ L E)

def primeDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) : ℂ :=
  periodicSourcePrimeMean C.giantCenter deleted hZ M
    (weightedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd W) (primeScalar C s h k hs ks) -
  primeIntegral (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter deleted) (primeCutoff C.giantCenter (primeScalar C s h k hs ks))*
    ResidueHaar.average (fun z : UnitPair M => weightedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k₀ L) outside h k M hd W ((z.1:ZMod M),(z.2:ZMod M)))

def mixedDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) : ℂ :=
  periodicSourceMixedMean C.giantCenter deleted hZ M
    (weightedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd W) (mixedScalar C s h k hs ks) -
  mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
    (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter deleted)
    (mixedGiantPrimeTest C.giantCenter (mixedScalar C s h k hs ks))*
    ResidueHaar.average (fun z : MixedPair M => weightedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k₀ L) outside h k M hd W (z.1,(z.2:ZMod M)))

def guardedPrimeDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) : ℂ :=
  guardedPeriodicSourcePrimeMean C.giantCenter deleted hZ M
    (weightedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd W) (primeScalar C s h k hs ks) -
  primeIntegral (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter deleted) (primeCutoff C.giantCenter (primeScalar C s h k hs ks))*
    ResidueHaar.average (fun z : UnitPair M => weightedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k₀ L) outside h k M hd W ((z.1:ZMod M),(z.2:ZMod M)))

def guardedMixedDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) : ℂ :=
  guardedPeriodicSourceMixedMean C.giantCenter deleted hZ M
    (weightedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd W) (mixedScalar C s h k hs ks) -
  mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
    (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter deleted)
    (mixedGiantPrimeTest C.giantCenter (mixedScalar C s h k hs ks))*
    ResidueHaar.average (fun z : MixedPair M => weightedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k₀ L) outside h k M hd W (z.1,(z.2:ZMod M)))

end Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

end

end OAI
