import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryGiantXiReplacementActual HistoryActiveCoordinates
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem corrected_empty_eq (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    {ι : Type} (e : ι ≃ I) :
    reindexedCorrectedRealXi b s X tb td G h k hs ks 0 0 [] []
      (Finset.univ : Finset Empty) Empty.elim Empty.elim I background e =
    reindexedRealXi b s X tb td G h k hs ks I background e := by
  funext x
  simp [reindexedCorrectedRealXi,correctedPairedRealXi,rootCounterpart,counterpartArchimedean,
    reindexedRealXi,activeRealXi]

theorem empty_counterpartBounds (k₀ l : ℕ) (h k : History l)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ) (lo hi : I → ℝ) :
    CounterpartBounds 0 0 (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
      [] [] I background lo hi := by
  constructor
  · simp only [keyLogEndpoint,List.map_nil,List.sum_nil,zero_sub]
    apply neg_nonpos.mpr
    unfold nominalInheritedWidth
    positivity
  · simp only [keyLogEndpoint,List.map_nil,List.sum_nil,zero_add]
    unfold nominalRemovedWidth
    positivity

theorem empty_derivative_le_reference
    {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (h k : History l) (roots : List Bool) :
    correctedPairDerivativeBound (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
      0 0 (Fintype.card (Empty ⊕ Fin roots.length)) h k (frequencyBound Bs BD Bz k₀ L)
      (bulkSize k₀ L/2) k₀ C.bulkBin (initialGap Bs k₀ L) (2+2*(k₀:ℝ))
      (C.cells.center (bulkSize k₀ L/2)) ≤ referenceDerivative C h k roots := by
  unfold referenceDerivative correctedPairDerivativeBound
  simp only [Fintype.card_sum,Fintype.card_empty,Fintype.card_fin,
    Nat.cast_zero,Nat.cast_add,zero_add]
  have hp := rootCounterpartDerivativeConstant_pos.le
  gcongr
  nlinarith [Nat.cast_nonneg (pairedDiagonalHKeys h k (l+1)).length (α:=ℝ),
    Nat.cast_nonneg (pairedDiagonalUKeys h k (l+1)).length (α:=ℝ),
    mul_nonneg hp (Nat.cast_nonneg (diagonalCellKeys k (l+1)).length (α:=ℝ))]

end Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected

end

end OAI
