import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportCoefficients
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRows

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding Characters.RationalHistory

def normalizedRows (seed : List SourceSlot) {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hh : TreeSourceLabels seed h) :
    Internal seed l→Expr (Coordinate seed l)×Expr (Coordinate seed l) := fun i =>
  let r := Arithmetic.HistoryOccurrenceRows.canonical h hs (internalEquiv seed h hh i)
  (r.1.rename (coordinateEquiv seed h hh).symm,r.2.rename (coordinateEquiv seed h hh).symm)

theorem normalizedRows_eq_fixedRows (seed : List SourceSlot) {l : ℕ}
    {V : ℕ→ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hh : TreeSourceLabels seed h) :
    normalizedRows seed h hs hh=
      fixedRows seed (plan h hs) (normalizedCoefficientCode seed h hs hh false)
        (normalizedCoefficientCode seed h hs hh true) := by
  funext i
  exact renamed_rows_eq_fixedRows seed h hh hs
    (Arithmetic.HistorySymbolicLinearity.coefficientHistory h hs false)
    (Arithmetic.HistorySymbolicLinearity.coefficientHistory h hs true)
    (coordinateEquiv seed h hh).symm i

def fixedCanonicalRows (seed : List SourceSlot) {l : ℕ} (p : Plan l) :
    Internal seed l→Expr (Coordinate seed l)×Expr (Coordinate seed l) :=
  fixedRows seed p
    (execute p (fixedCoefficientRootCode seed l false)
      (fixedCompensationCode seed l (fun i => .atom (.inr (.inr i)))))
    (execute p (fixedCoefficientRootCode seed l true)
      (fixedCompensationCode seed l (fun i => .atom (.inr (.inr i)))))

theorem normalizedRows_eq_fixedCanonicalRows (seed : List SourceSlot) {l : ℕ}
    {V : ℕ→ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hh : TreeSourceLabels seed h) :
    normalizedRows seed h hs hh=fixedCanonicalRows seed (plan h hs) := by
  rw [normalizedRows_eq_fixedRows,normalizedCoefficientCode_eq_execute,
    normalizedCoefficientCode_eq_execute]
  rfl

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
