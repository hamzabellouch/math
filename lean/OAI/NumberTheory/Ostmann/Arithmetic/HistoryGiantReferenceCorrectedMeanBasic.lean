import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorCollision
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCounterpart
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanLaws

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantReferenceCorrectedMean
open Construction HistorySignedResidues HistoryPairSmoothXi HistoryPairGiantCoordinates
open HistoryGiantPriorGrid HistoryGiantReferenceMean HistoryGiantReferenceCounterpart
variable {l : ℕ} (d : Decomposition) (V : ℕ → ℕ) (outside : List ℕ)
variable (h g : History l) (hs : h.Supported V outside) (gs : g.Supported V outside)
variable (n b s : ℕ) (X tb td G : ℝ)
variable (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
variable (u : SourceAssignment sources (Template.extracted j T))
variable (y : SourceAssignment sources (Template.remainder j T))
variable (hsmall : g.root.small = Template.reinsert j T
  (assignedSlots sources (Template.extracted j T) u)
  (assignedSlots sources (Template.remainder j T) y))
variable (A B : ℝ) (center : ℕ → ℝ)
include hsmall

theorem counterpart_referenceTerm_eq_bool (P Q : ℤ) :
    (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
      referenceTerm d V outside h g hs gs n b s X tb td G P Q =
    ((h.compensationProduct : ℂ)*(g.compensationProduct : ℂ)) *
      (if Nat.Coprime P.natAbs Q.natAbs then
        liftedResidueTest (residueTransform d) V outside h g (comparisonModulus h g outside n)
          (pairModulus_dvd_comparisonModulus h g outside n) (P,Q) *
        reindexedCorrectedRealXi b s X tb td G h g hs gs A B
          (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
          (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
          (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
          (giantCoordinates h g) (pairBackground h g) (boolEquiv h g) (fun a => if a then (Q : ℝ) else (P : ℝ))
      else 0) := by
  rw [reindexedCorrectedRealXi_bool_signed b s X tb td G h g hs gs
    sources T j u y hsmall A B center P Q]
  unfold referenceTerm
  split_ifs <;> ring

theorem counterpart_referenceTerm_eq_option (P Q : ℤ) :
    (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
      referenceTerm d V outside h g hs gs n b s X tb td G P Q =
    ((h.compensationProduct : ℂ)*(g.compensationProduct : ℂ)) *
      (if Nat.Coprime P.natAbs Q.natAbs then
        liftedResidueTest (residueTransform d) V outside h g (comparisonModulus h g outside n)
          (pairModulus_dvd_comparisonModulus h g outside n) (P,Q) *
        reindexedCorrectedRealXi b s X tb td G h g hs gs A B
          (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
          (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
          (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
          (giantCoordinates h g) (pairBackground h g) (optionEquiv h g) (fun a => match a with | none => (P : ℝ) | some _ => (Q : ℝ))
      else 0) := by
  have hxi : reindexedCorrectedRealXi b s X tb td G h g hs gs A B
      (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
      (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
      (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
      (giantCoordinates h g) (pairBackground h g) (optionEquiv h g)
      (fun a => match a with | none => (P : ℝ) | some _ => (Q : ℝ)) =
      (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
        HistorySymbolicEncoding.actualRealXi b s X tb td G outside h g hs gs
          (HistorySignedDecode.signedGiantSample h P Q) (HistorySignedDecode.signedGiantSample g P Q) :=
    reindexedCorrectedRealXi_option_signed b s X tb td G h g hs gs
      sources T j u y hsmall A B center P Q
  rw [hxi]
  unfold referenceTerm
  split_ifs <;> ring

end Ostmann.Arithmetic.HistoryGiantReferenceCorrectedMean

end

end OAI
