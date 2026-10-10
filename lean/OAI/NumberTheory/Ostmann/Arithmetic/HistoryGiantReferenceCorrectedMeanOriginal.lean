import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCorrectedMeanLaws

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

theorem prime_original_counterpart_referenceMean_eq_guarded
    (E : Finset ℕ) (hZ : 0 < logCellMass G E) :
    (logCellPrimeSource G E hZ).law.cmean (fun p =>
      (logCellPrimeSource G E hZ).law.cmean (fun q =>
        (remainingCounterpart sources T j (logCellPrimeSource G E hZ) A B G center u (q,y) : ℂ) *
          referenceTerm d V outside h g hs gs n b s X tb td G p.val q.val)) =
      ((h.compensationProduct : ℂ)*(g.compensationProduct : ℂ)) *
        guardedSourcePrimeMean (residueTransform d) V outside h g G E hZ
          (comparisonModulus h g outside n) (pairModulus_dvd_comparisonModulus h g outside n)
          (reindexedCorrectedRealXi b s X tb td G h g hs gs A B
            (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
            (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
            (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
            (giantCoordinates h g) (pairBackground h g) (boolEquiv h g)) := by
  have hmean : (logCellPrimeSource G E hZ).law.cmean (fun p =>
      (logCellPrimeSource G E hZ).law.cmean (fun q =>
        (remainingCounterpart sources T j (logCellPrimeSource G E hZ) A B G center u (q,y) : ℂ) *
          referenceTerm d V outside h g hs gs n b s X tb td G p.val q.val)) =
      primeMean (logCellPrimeSource G E hZ) (fun P Q =>
        (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
          referenceTerm d V outside h g hs gs n b s X tb td G P Q) := by
    unfold primeMean
    apply congrArg (logCellPrimeSource G E hZ).law.cmean
    funext p
    apply congrArg (logCellPrimeSource G E hZ).law.cmean
    funext q
    simp only [Int.cast_natCast]
    rw [remainingCounterpartAt_sample sources T j (logCellPrimeSource G E hZ) A B G center u (q,y)]
  rw [hmean]
  exact prime_corrected_referenceMean_eq_guarded d V outside h g hs gs n b s X tb td G
    sources T j u y hsmall A B center E hZ

theorem mixed_original_counterpart_referenceMean_eq_guarded
    (E : Finset ℕ) (hZ : 0 < logCellMass G E) :
    (∑ P ∈ integerPivotCell G, (externalPivotWeight G P : ℂ) *
      (logCellPrimeSource G E hZ).law.cmean (fun q =>
        (remainingCounterpart sources T j (logCellPrimeSource G E hZ) A B G center u (q,y) : ℂ) *
          referenceTerm d V outside h g hs gs n b s X tb td G P q.val)) =
      ((h.compensationProduct : ℂ)*(g.compensationProduct : ℂ)) *
        guardedSourceMixedMean (residueTransform d) V outside h g G E hZ
          (comparisonModulus h g outside n) (pairModulus_dvd_comparisonModulus h g outside n)
          (reindexedCorrectedRealXi b s X tb td G h g hs gs A B
            (pairedDiagonalHKeys h g j) (pairedDiagonalUKeys h g j)
            (Finset.univ : Finset (Fin (diagonalCellKeys g j).length))
            (pairedDiagonalCellCenter g j G center) (pairedDiagonalCellKey h g j)
            (giantCoordinates h g) (pairBackground h g) (optionEquiv h g)) := by
  have hmean : (∑ P ∈ integerPivotCell G, (externalPivotWeight G P : ℂ) *
      (logCellPrimeSource G E hZ).law.cmean (fun q =>
        (remainingCounterpart sources T j (logCellPrimeSource G E hZ) A B G center u (q,y) : ℂ) *
          referenceTerm d V outside h g hs gs n b s X tb td G P q.val)) =
      mixedMean G (logCellPrimeSource G E hZ) (fun P Q =>
        (remainingCounterpartAt sources T j A B G center u y (Q : ℝ) : ℂ) *
          referenceTerm d V outside h g hs gs n b s X tb td G P Q) := by
    unfold mixedMean
    apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun z : ℂ => (externalPivotWeight G p : ℂ)*z)
    apply congrArg (logCellPrimeSource G E hZ).law.cmean
    funext q
    simp only [Int.cast_natCast]
    rw [remainingCounterpartAt_sample sources T j (logCellPrimeSource G E hZ) A B G center u (q,y)]
  rw [hmean]
  exact mixed_corrected_referenceMean_eq_guarded d V outside h g hs gs n b s X tb td G
    sources T j u y hsmall A B center E hZ

end Ostmann.Arithmetic.HistoryGiantReferenceCorrectedMean

end

end OAI
