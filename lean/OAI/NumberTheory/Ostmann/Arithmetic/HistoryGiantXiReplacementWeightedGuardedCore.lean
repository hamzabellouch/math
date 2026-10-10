import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedGuardedCore
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementWeightedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted
open HistoryGiantXiReplacementActual HistoryGiantXiReplacementUncorrected HistoryGiantWeightedPriorReplacement
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryGiantXiPriorReplacement HistoryActiveCoordinates HistorySignedResidues
open HistoryGiantPriorGrid PrimeCellFreezing LogCellPartition HistoryGiantReferenceSourceBounds

theorem guarded_difference_bounds
    {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) (outside : List ℕ)
    (hout : ∀ q ∈ outside, q.Prime) (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (hprime : ∀ z ∈ logRectangle (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1),
      ‖HistoryGiantXiReplacementUncorrected.primeScalar C s h k hs ks (fun i => Real.exp (z i))‖ ≤ referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)
    (hmixed : ∀ z ∈ logRectangle (Option.elim' (C.giantCenter-1) (fun _ : Unit => C.giantCenter-1))
      (Option.elim' (C.giantCenter+1) (fun _ : Unit => C.giantCenter+1)),
      ‖HistoryGiantXiReplacementUncorrected.mixedScalar C s h k hs ks (fun i => Real.exp (z i))‖ ≤ referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) (BW : ℝ) (hBW : 0 ≤ BW) (hW : ∀ z, ‖W z‖ ≤ BW) :
    ‖guardedPrimeDifference C s h k hs ks deleted hZ M hd W‖ ≤
      (BW*((outside.prod:ℝ)^(2^(l+1))*referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l))*
        (Real.exp (1-C.giantCenter)/logCellMass C.giantCenter deleted)+
      ‖primeDifference C s h k hs ks deleted hZ M hd W‖ ∧
    ‖guardedMixedDifference C s h k hs ks deleted hZ M hd W‖ ≤
      (BW*((outside.prod:ℝ)^(2^(l+1))*referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l))*
        (8*Real.exp (-C.giantCenter))+
      ‖mixedDifference C s h k hs ks deleted hZ M hd W‖ := by
  have hp := guardedWeightedSourcePrimeMean_error d (frequencyBound Bs BD Bz k₀ L) outside h k
    C.giantCenter deleted hZ M hd hout W BW hBW hW (HistoryGiantXiReplacementUncorrected.primeScalar C s h k hs ks)
    (referenceAmplitude_nonneg Bs L k₀ l) hprime
  have hm := guardedWeightedSourceMixedMean_error d (frequencyBound Bs BD Bz k₀ L) outside h k
    C.giantCenter deleted hZ M hd hout W BW hBW hW (HistoryGiantXiReplacementUncorrected.mixedScalar C s h k hs ks)
    (referenceAmplitude_nonneg Bs L k₀ l) hmixed
  constructor
  · exact (norm_sub_le_norm_sub_add_norm_sub _ (periodicSourcePrimeMean C.giantCenter deleted hZ M
      (weightedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd W) (HistoryGiantXiReplacementUncorrected.primeScalar C s h k hs ks)) _).trans
      (add_le_add hp le_rfl)
  · exact (norm_sub_le_norm_sub_add_norm_sub _ (periodicSourceMixedMean C.giantCenter deleted hZ M
      (weightedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd W) (HistoryGiantXiReplacementUncorrected.mixedScalar C s h k hs ks)) _).trans
      (add_le_add hm le_rfl)

end Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

end

end OAI
