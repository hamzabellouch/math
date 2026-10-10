import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCounterpartValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedReindex

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantReferenceCounterpart
open Construction HistoryOccurrenceVariables HistoryPairGiantCoordinates HistoryPairSmoothXi
open HistoryPairPattern HistoryActiveCoordinates HistorySymbolicEncoding HistorySignedDecode
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem reindexedCorrectedRealXi_bool_real
    (b s : ℕ) (X tb td G : ℝ) (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T))
    (hsmall : g.root.small = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) y))
    (A B : ℝ) (center : ℕ → ℝ) (z : Bool → ℝ) :
    reindexedCorrectedRealXi b s X tb td G h g hs gs A B
      (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
      (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
      (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
      (giantCoordinates h g) (pairBackground h g) (boolEquiv h g) z =
    (remainingCounterpartAt sources T j A B G center u y (z true) : ℂ) *
      actualRealXi b s X tb td G outside h g hs gs
        (realGiantSample h z) (realGiantSample g z) := by
  change (pairedRootCounterpart h g j A B G center (insertGiants h g z) : ℂ) *
    pairedRealXi b s X tb td G h g hs gs (insertGiants h g z) = _
  rw [pairedRootCounterpart_insertGiants h g sources T j u y hsmall,
    pairedRealXi_insertGiants]

theorem reindexedCorrectedRealXi_bool_signed
    (b s : ℕ) (X tb td G : ℝ) (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T))
    (hsmall : g.root.small = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) y))
    (A B : ℝ) (center : ℕ → ℝ) (P Q : ℤ) :
    reindexedCorrectedRealXi b s X tb td G h g hs gs A B
      (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
      (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
      (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
      (giantCoordinates h g) (pairBackground h g) (boolEquiv h g) (fun a => if a then (Q : ℝ) else (P : ℝ)) =
    (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
      actualRealXi b s X tb td G outside h g hs gs
        (signedGiantSample h P Q) (signedGiantSample g P Q) := by
  have hh := reindexedCorrectedRealXi_bool_real b s X tb td G h g hs gs
    sources T j u y hsmall A B center (fun a => if a then (Q : ℝ) else (P : ℝ))
  simpa only [Bool.true_eq,ite_true,realGiantSample_signed] using hh

theorem reindexedCorrectedRealXi_option_signed
    (b s : ℕ) (X tb td G : ℝ) (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T))
    (hsmall : g.root.small = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) y))
    (A B : ℝ) (center : ℕ → ℝ) (P Q : ℤ) :
    reindexedCorrectedRealXi b s X tb td G h g hs gs A B
      (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
      (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
      (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
      (giantCoordinates h g) (pairBackground h g) (optionEquiv h g) (fun a => match a with | none => (P : ℝ) | some _ => (Q : ℝ)) =
    (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
      actualRealXi b s X tb td G outside h g hs gs
        (signedGiantSample h P Q) (signedGiantSample g P Q) := by
  change reindexedCorrectedRealXi b s X tb td G h g hs gs A B
    (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
    (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
    (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
    (giantCoordinates h g) (pairBackground h g) (boolEquiv h g)
      (fun a => match optionBoolEquiv.symm a with | none => (P : ℝ) | some _ => (Q : ℝ)) = _
  have hz : (fun a => match optionBoolEquiv.symm a with | none => (P : ℝ) | some _ => (Q : ℝ)) =
      (fun a => if a then (Q : ℝ) else (P : ℝ)) := by
    funext a
    cases a <;> rfl
  rw [hz]
  exact reindexedCorrectedRealXi_bool_signed b s X tb td G h g hs gs
    sources T j u y hsmall A B center P Q

end Ostmann.Arithmetic.HistoryGiantReferenceCounterpart

end

end OAI
