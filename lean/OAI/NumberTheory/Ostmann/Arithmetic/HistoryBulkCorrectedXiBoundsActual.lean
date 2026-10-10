import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedXiCenter

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryProductWindows HistoryPairSmoothXi HistoryPairPattern
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates

theorem actual_bulk_corrected_bounds {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hX : 0 < C.scale) (s : ℕ) (outside : List ℕ)
    (houtside : ∀q∈outside,0 < q) (hout : outside.length = 2*s)
    (V : ℕ → ℕ) (l : ℕ) (hl : l < k₀)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))))
    (x : OuterSample C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant)
    (p q : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l)
    (hx : (outerPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass x ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l e ≠ 0) :
    let h := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant x p) c
    let k := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant
        (selectedPermutedOuter C l σ x) q) e
    ∀(hs : h.Supported V outside) (ks : k.Supported V outside),
    let T := (C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l
    let U := C.compensationLogScale l
    let WH := nominalInheritedWidth k₀ l+1
    let Wu := nominalRemovedWidth k₀ l
    ∀(τ : Type) (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k),
    let f := reindexedCorrectedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
      T U (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1)) S cellCenter cellKey
      (bulkCoordinates h k) (pairBackground h k) (selectedOrderedEquiv C V l outside σ x p q c e hs)
    ContDiff ℝ ∞ (fun y : Fin (2^l) × Fin (2*(bulkSize k₀ L/2)) → ℝ => f (fun i => Real.exp (y i))) ∧
    (∀y : Fin (2^l) × Fin (2*(bulkSize k₀ L/2)) → ℝ, (∀i,0 < y i) → ∀i,
      ‖deriv (fun t => f (Expr.logCurve y i t)) 0‖ ≤
        correctedPairDerivativeBound WH Wu (pairedDiagonalHKeys h k (l+1)).length
          (pairedDiagonalUKeys h k (l+1)).length S.card h k V (bulkSize k₀ L/2) k₀ C.bulkBin
          (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2))) ∧
    (∀y : Fin (2^l) × Fin (2*(bulkSize k₀ L/2)) → ℝ, (∀i,0 < y i) → ‖f y‖ ≤ Real.exp (WH+Wu)*
      Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k₀ L+sourceXiConstant l k₀ (2+2*(k₀:ℝ)))) := by
  dsimp only
  intro hs ks τ S cellCenter cellKey
  have hd := selected_bulk_sourceBounds C V l outside σ x p q c e hx hc he hs
  apply selected_bulk_corrected_bounds C s C.scale (initialGap Bs k₀ L) (2+2*(k₀:ℝ))
    (by exact_mod_cast hX) houtside hout _ _ hs ks hl _ _
    (selectedMatching C V l σ x p q c e) _ hd.1.background_source hd.2.background_source
    (selected_Xi_source_center C) S cellCenter cellKey
    (selectedOrderedEquiv C V l outside σ x p q c e hs)
  · exact decoded_tree_source_labels _ _ _ _ _ _
      (Template.assignedSlots_matches C.sources _ x.2.2)
  · exact decoded_tree_source_labels _ _ _ _ _ _
      (Template.assignedSlots_matches C.sources _ (selectedPermutedOuter C l σ x).2.2)

end Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds

end

end OAI
