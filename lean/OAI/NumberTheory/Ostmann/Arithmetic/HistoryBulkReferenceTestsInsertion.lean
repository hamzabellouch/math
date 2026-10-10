import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTests

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTests
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryPairBulkCoordinates HistoryBulkReferenceScalarCoordinates
attribute [local instance] Classical.propDecidable
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def integerInsertOrderedGiants (m k₀ : ℕ) (h k : History l)
    (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℤ) (u : Bool → ℤ) : PairKey h k → ℤ :=
  fun i => if hi : i ∈ giantCoordinates h k then u ((boolEquiv h k).symm ⟨i,hi⟩)
    else if hi : i ∈ bulkCoordinates h k then z ((orderedEquiv m k₀ h k hs hh).symm ⟨i,hi⟩)
    else pairSample h k i

theorem integerInsertOrderedGiants_cast (m k₀ : ℕ) (h k : History l)
    (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℤ) (u : Bool → ℤ) :
    (fun i => (integerInsertOrderedGiants m k₀ h k hs hh z u i : ℝ)) =
      insertOrderedGiants m k₀ h k hs hh (fun i => (z i : ℝ)) (fun i => (u i : ℝ)) := by
  funext i
  unfold integerInsertOrderedGiants insertOrderedGiants insertOrdered HistoryActiveCoordinates.insert
  split_ifs <;> rfl

def orderedIntegerSourceValues (sources : SourceFamily) (m k₀ l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k₀) l)) :
    Fin (2^l) × Fin m → ℤ :=
  fun j => ((x ((Conclusion.currentBulkPositionEquiv m k₀ l).symm j).val).val : ℤ)

theorem orderedIntegerSourceValues_cast (sources : SourceFamily) (m k₀ l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k₀) l)) :
    (fun i => (orderedIntegerSourceValues sources m k₀ l x i : ℝ)) =
      orderedSourceValues sources m k₀ l x := by
  funext i
  simp only [orderedIntegerSourceValues, orderedSourceValues, Int.cast_natCast]

def orderedSourceIndicatorB (sources : SourceFamily) (m k₀ : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
    (Xp Xm : ℤ) : ℂ :=
  primeResidueIndicatorAt h k hs ks
    (integerInsertOrderedGiants m k₀ h k hs hh
      (orderedIntegerSourceValues sources m k₀ l x) (fun t => if t then Xm else Xp)) (Xp,Xm)

end Ostmann.Arithmetic.HistoryBulkReferenceTests

end

end OAI
