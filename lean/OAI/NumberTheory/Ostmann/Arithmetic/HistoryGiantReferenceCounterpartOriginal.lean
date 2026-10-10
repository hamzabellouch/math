import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCounterpartXi

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantReferenceCounterpart
open Construction HistoryOccurrenceVariables HistoryPairGiantCoordinates HistoryPairSmoothXi
open HistoryPairPattern HistoryActiveCoordinates HistorySymbolicEncoding HistorySignedDecode
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem reindexedCorrectedRealXi_bool_remainingSample
    (b s : ℕ) (X tb td G : ℝ) (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : g.root = remainingState sources T j giant p u x v)
    (A B : ℝ) (center : ℕ → ℝ) (P : ℤ) (q : giant.Sample) :
    reindexedCorrectedRealXi b s X tb td G h g hs gs A B
      (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
      (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
      (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
      (giantCoordinates h g) (pairBackground h g) (boolEquiv h g) (fun a => if a then (q.val : ℝ) else (P : ℝ)) =
    (remainingCounterpart sources T j giant A B G center u (q,x.2) : ℂ) *
      actualRealXi b s X tb td G outside h g hs gs
        (signedGiantSample h P (q.val : ℤ)) (signedGiantSample g P (q.val : ℤ)) := by
  have hsmall : g.root.small = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) x.2) := congrArg State.small hroot
  have hh := reindexedCorrectedRealXi_bool_signed b s X tb td G h g hs gs
    sources T j u x.2 hsmall A B center P (q.val : ℤ)
  simp only [Int.cast_natCast] at hh
  have hK := remainingCounterpartAt_sample sources T j giant A B G center u (q,x.2)
  rw [hK] at hh
  exact hh

theorem reindexedCorrectedRealXi_option_remainingSample
    (b s : ℕ) (X tb td G : ℝ) (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : g.root = remainingState sources T j giant p u x v)
    (A B : ℝ) (center : ℕ → ℝ) (P : ℤ) (q : giant.Sample) :
    reindexedCorrectedRealXi b s X tb td G h g hs gs A B
      (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
      (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
      (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
      (giantCoordinates h g) (pairBackground h g) (optionEquiv h g) (fun a => match a with | none => (P : ℝ) | some _ => (q.val : ℝ)) =
    (remainingCounterpart sources T j giant A B G center u (q,x.2) : ℂ) *
      actualRealXi b s X tb td G outside h g hs gs
        (signedGiantSample h P (q.val : ℤ)) (signedGiantSample g P (q.val : ℤ)) := by
  have hsmall : g.root.small = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) x.2) := congrArg State.small hroot
  have hh := reindexedCorrectedRealXi_option_signed b s X tb td G h g hs gs
    sources T j u x.2 hsmall A B center P (q.val : ℤ)
  simp only [Int.cast_natCast] at hh
  have hK := remainingCounterpartAt_sample sources T j giant A B G center u (q,x.2)
  rw [hK] at hh
  exact hh

end Ostmann.Arithmetic.HistoryGiantReferenceCounterpart

end

end OAI
