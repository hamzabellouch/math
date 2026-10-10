import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicLinearity
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportNormalized

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding
open Arithmetic.HistorySymbolicState Arithmetic.HistorySymbolicLinearity Characters.RationalHistory

def fixedCoefficientRootCode (seed : List SourceSlot) (l : ℕ) (second : Bool) :
    StateCode (Coordinate seed l) :=
  ⟨.fixed (if second then 0 else 1),.fixed (if second then 1 else 0),(fixedRootCode seed l).small⟩

lemma coefficient_root_code_normalized (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (second : Bool) :
    (stateCode (coefficientRoot h second)).rename (coordinateEquiv seed h hh).symm=
      fixedCoefficientRootCode seed l second := by
  apply StateCode.ext
  · rfl
  · rfl
  · have he := congrArg (fun e : StateCode (Coordinate seed l) => e.small) (root_code_normalized seed h hh)
    exact he

def normalizedCoefficientCode (seed : List SourceSlot) {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hh : TreeSourceLabels seed h) (second : Bool) :
    TreeCode (Coordinate seed l) l :=
  renameTree (coordinateEquiv seed h hh).symm (treeCode h (coefficientHistory h hs second))

theorem normalizedCoefficientCode_eq_execute (seed : List SourceSlot) {l : ℕ} {V : ℕ→ℕ}
    {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hh : TreeSourceLabels seed h) (second : Bool) :
    normalizedCoefficientCode seed h hs hh second=
      execute (plan h hs) (fixedCoefficientRootCode seed l second)
        (fixedCompensationCode seed l (fun i => .atom (.inr (.inr i)))) := by
  rw [normalizedCoefficientCode,coefficientHistory,encode_code,execute_rename,
    coefficient_root_code_normalized,compensation_code_normalized]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
