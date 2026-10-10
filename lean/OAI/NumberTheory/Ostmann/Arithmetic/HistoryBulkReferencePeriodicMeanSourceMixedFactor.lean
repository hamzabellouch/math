import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportValues
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplierActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource
open Construction Conclusion HistoryPairPattern HistoryCRTIntegration HistoryFrequencyResidues
open HistoryBulkGiantPrincipalTransport HistoryBulkReferenceSmallMultiplier
open HistoryDiagonalSmallOriginalMean HistorySignedResidueFactorization HistorySignedResidueWeightedAverages
open DiagonalSmallResidueNorm HistoryBulkReferenceTests

theorem smallMultiplier_mul_newReferenceResidueTest
    {d : Decomposition} {Bs BD Bz L : ℝ} {depth l m : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz depth L E) (outside : List ℕ) (K : ℕ)
    (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz depth L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz depth L) outside)
    (x : SourceAssignment C.sources (HistoryGiantOriginalMeanFactorization.Current
      (k:=depth) (L:=L) (l:=l))) (s : ℤ)
    (c : HistoryGiantOriginalMeanFactorization.Choices (l:=l) C)
    (newk : History l) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (xUnits : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ)
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) s)
    (P Q : ℤ) (hp : 0≤P) (hq : 0≤Q) :
    (smallMultiplier C outside x s P Q:ℂ)*
      newReferenceResidueTest d K h k hs ks (currentSmallHistory C x s c) newk σ xUnits v
        (rootResidueIndicator (currentSmallHistory C x s c)) (P,Q) =
    newReferenceResidueTest d K h k hs ks (currentSmallHistory C x s c) newk σ xUnits v
      (fun z=>rootResidueIndicator (currentSmallHistory C x s c) z *
        mixedExtension (currentRootSmallTest C outside x s c hu) z) (P,Q) := by
  simp only [newReferenceResidueTest_intCast]
  rw [←mul_assoc,←mul_assoc,←mul_assoc,
    smallMultiplier_mul_currentRootIndicator C outside x s c hu P Q hp hq]

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI
