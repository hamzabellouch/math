import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMeanFactorization
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedGuarded

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean
open Construction Conclusion HistorySignedResidues HistoryGiantXiReplacementUncorrected
open HistoryPrincipalIntegralAverage HistoryCRTIntegration HistoryGiantPriorGrid
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (h g : History l)
variable (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
variable (gs : g.Supported (frequencyBound Bs BD Bz k L) outside)
variable (hout : ∀q∈outside,q.Prime) (n : ℕ)

def primeMainTerm : ℂ :=
  let M := comparisonModulus h g outside n
  letI : NeZero M := ⟨(comparisonModulus_pos h g hs gs hout n).ne'⟩
  primeIntegral (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter ∅)
    (primeCutoff C.giantCenter (primeScalar C (bulkSize k L/2) h g hs gs)) *
    ResidueHaar.average (fun z : UnitPair M => liftedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k L) outside h g M
      (pairModulus_dvd_comparisonModulus h g outside n) ((z.1:ZMod M),(z.2:ZMod M)))

theorem prime_factor_difference (a J : ℂ)
    (ha : a=J*guardedSourcePrimeMean (residueTransform d) (frequencyBound Bs BD Bz k L)
      outside h g C.giantCenter ∅ C.giantPositive
      (comparisonModulus h g outside n) (pairModulus_dvd_comparisonModulus h g outside n)
      (primeScalar C (bulkSize k L/2) h g hs gs)) :
    a-J*primeMainTerm C outside h g hs gs hout n =
      J*comparisonGuardedPrimeDifference C (bulkSize k L/2) h g hs gs hout ∅ C.giantPositive n := by
  rw [ha]
  unfold primeMainTerm comparisonGuardedPrimeDifference guardedPrimeDifference
  ring

def mixedMainTerm : ℂ :=
  let M := comparisonModulus h g outside n
  letI : NeZero M := ⟨(comparisonModulus_pos h g hs gs hout n).ne'⟩
  mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
    (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1)
    (fun _ => logCellMass C.giantCenter ∅)
    (mixedGiantPrimeTest C.giantCenter (mixedScalar C (bulkSize k L/2) h g hs gs)) *
    ResidueHaar.average (fun z : MixedPair M => liftedResidueTest (residueTransform d)
      (frequencyBound Bs BD Bz k L) outside h g M
      (pairModulus_dvd_comparisonModulus h g outside n) (z.1,(z.2:ZMod M)))

theorem mixed_factor_difference (a J : ℂ)
    (ha : a=J*guardedSourceMixedMean (residueTransform d) (frequencyBound Bs BD Bz k L)
      outside h g C.giantCenter ∅ C.giantPositive
      (comparisonModulus h g outside n) (pairModulus_dvd_comparisonModulus h g outside n)
      (mixedScalar C (bulkSize k L/2) h g hs gs)) :
    a-J*mixedMainTerm C outside h g hs gs hout n =
      J*comparisonGuardedMixedDifference C (bulkSize k L/2) h g hs gs hout ∅ C.giantPositive n := by
  rw [ha]
  unfold mixedMainTerm comparisonGuardedMixedDifference guardedMixedDifference
  ring

end Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean

end

end OAI
