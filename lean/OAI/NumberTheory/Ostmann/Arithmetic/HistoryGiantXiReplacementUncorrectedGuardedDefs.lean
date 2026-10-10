import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorCollision
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected
open Construction Conclusion HistoryGiantPriorGrid HistorySignedResidues
open HistoryPrincipalIntegralAverage HistoryCRTIntegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k₀ L E)

def guardedPrimeDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M) : ℂ :=
  guardedSourcePrimeMean (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k
    C.giantCenter deleted hZ M hd (primeScalar C s h k hs ks) -
  primeIntegral (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter deleted) (primeCutoff C.giantCenter (primeScalar C s h k hs ks))*
    ResidueHaar.average (fun z : UnitPair M => liftedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k₀ L) outside h k M hd ((z.1:ZMod M),(z.2:ZMod M)))

def guardedMixedDifference (s : ℕ) {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M) : ℂ :=
  guardedSourceMixedMean (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k
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
