import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualCounterpart
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedXiCenter

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryActiveCoordinates
open HistoryPairGiantCoordinates HistoryProductWindows

theorem reference_counterpartBounds
    {d : Decomposition} {Bs BD Bz : ℝ} {k₀ l : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ)
    {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (hl : l < k₀)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (hgiants : RootGiantsAgree h k)
    (hsrc : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter
      (C.cells.center (bulkSize k₀ L/2)) k (rightMap h k)
      (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hne : pairedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter
      h k hs ks (pairBackground h k) ≠ 0) :
    CounterpartBounds ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l)
      (C.compensationLogScale l) (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
      (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
      (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) :=
  counterpartBounds_of_reference_Xi C s C.scale h k hs ks hl hk hgiants
    hsrc.background_source hne

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
