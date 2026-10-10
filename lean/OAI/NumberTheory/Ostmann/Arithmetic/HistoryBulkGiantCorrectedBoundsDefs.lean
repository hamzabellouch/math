import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIntegralReplacementBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k₀ L E)
variable {outside : List ℕ}

def jointCorrectedScalar (s : ℕ) (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    {κ ι : Type*} (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : κ → ℝ) (x : ι → ℝ) : ℂ :=
  reindexedCorrectedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l) (C.compensationLogScale l)
    (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
    (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) (bulkCoordinates h k)
    (insert (giantCoordinates h k) (pairBackground h k) (fun j => u (eG.symm j))) eB x

def jointScalar (s : ℕ) (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    {κ ι : Type*} (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : κ → ℝ) (x : ι → ℝ) : ℂ :=
  reindexedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    (bulkCoordinates h k)
    (insert (giantCoordinates h k) (pairBackground h k) (fun j => u (eG.symm j))) eB x

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
