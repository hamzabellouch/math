import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCorrectedMeanBasic

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

theorem prime_corrected_referenceMean_eq_guarded (E : Finset ℕ) (hZ : 0 < logCellMass G E) :
    primeMean (logCellPrimeSource G E hZ) (fun P Q =>
      (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
        referenceTerm d V outside h g hs gs n b s X tb td G P Q) =
      ((h.compensationProduct : ℂ)*(g.compensationProduct : ℂ)) *
        guardedSourcePrimeMean (residueTransform d) V outside h g G E hZ
          (comparisonModulus h g outside n) (pairModulus_dvd_comparisonModulus h g outside n)
          (reindexedCorrectedRealXi b s X tb td G h g hs gs A B
            (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
            (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
            (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
            (giantCoordinates h g) (pairBackground h g) (boolEquiv h g)) := by
  unfold primeMean
  simp_rw [counterpart_referenceTerm_eq_bool d V outside h g hs gs n b s X tb td G
    sources T j u y hsmall A B center,Int.natAbs_natCast,Int.cast_natCast,
    FinitePrior.cmean_mul_left]
  rfl

theorem mixed_corrected_referenceMean_eq_guarded (E : Finset ℕ) (hZ : 0 < logCellMass G E) :
    mixedMean G (logCellPrimeSource G E hZ) (fun P Q =>
      (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
        referenceTerm d V outside h g hs gs n b s X tb td G P Q) =
      ((h.compensationProduct : ℂ)*(g.compensationProduct : ℂ)) *
        guardedSourceMixedMean (residueTransform d) V outside h g G E hZ
          (comparisonModulus h g outside n) (pairModulus_dvd_comparisonModulus h g outside n)
          (reindexedCorrectedRealXi b s X tb td G h g hs gs A B
            (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
            (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
            (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
            (giantCoordinates h g) (pairBackground h g) (optionEquiv h g)) := by
  unfold mixedMean
  simp_rw [counterpart_referenceTerm_eq_option d V outside h g hs gs n b s X tb td G
    sources T j u y hsmall A B center,Int.natAbs_natCast,Int.cast_natCast,
    FinitePrior.cmean_mul_left]
  unfold guardedSourceMixedMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (fun q : (logCellPrimeSource G E hZ).Sample =>
      if p.Coprime q.val then
        liftedResidueTest (residueTransform d) V outside h g (comparisonModulus h g outside n)
          (pairModulus_dvd_comparisonModulus h g outside n) (p,q.val) *
        reindexedCorrectedRealXi b s X tb td G h g hs gs A B
          (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
          (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
          (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
          (giantCoordinates h g) (pairBackground h g) (optionEquiv h g)
          (fun a => match a with | none => (p : ℝ) | some _ => (q.val : ℝ)) else 0) =
      (fun q => if p.Coprime q.val then
        liftedResidueTest (residueTransform d) V outside h g (comparisonModulus h g outside n)
          (pairModulus_dvd_comparisonModulus h g outside n) (p,q.val) *
        reindexedCorrectedRealXi b s X tb td G h g hs gs A B
          (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
          (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
          (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
          (giantCoordinates h g) (pairBackground h g) (optionEquiv h g)
          (Option.elim' (p : ℝ) (fun _ : Unit => (q.val : ℝ))) else 0) := by
    funext q
    split_ifs
    · congr 2
      funext a
      cases a <;> rfl
    · rfl
  have hh := congrArg (fun f : (logCellPrimeSource G E hZ).Sample → ℂ =>
    ((h.compensationProduct : ℂ)*(g.compensationProduct : ℂ)) *
      ((externalPivotWeight G p : ℂ) * (logCellPrimeSource G E hZ).law.cmean f)) he
  convert hh using 1
  ring_nf
  congr 2

end Ostmann.Arithmetic.HistoryGiantReferenceCorrectedMean

end

end OAI
