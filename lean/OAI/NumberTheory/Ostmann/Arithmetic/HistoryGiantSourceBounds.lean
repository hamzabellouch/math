import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBoundsPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBoundsSelected

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantSourceBounds
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairGiantCoordinates HistoryActiveCoordinates

theorem selected_decoded_pair_giant_sourceBounds {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (V : ℕ → ℕ) (l : ℕ)
    (x y : OuterSample C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant)
    (s t : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (hx : (outerPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant).mass x ≠ 0)
    (hy : (outerPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant).mass y ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l e ≠ 0) :
    let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
    let h := decodeHistory C.sources seed V l
      (outerState C.sources (Template.current seed l) C.giant x s) c
    let g := decodeHistory C.sources seed V l
      (outerState C.sources (Template.current seed l) C.giant y t) e
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) h (leftMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) ∧
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) g (rightMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) := by
  have hh := selected_decoded_sourceDomain C V l x s c hx hc
  have hg := selected_decoded_sourceDomain C V l y t e hy he
  dsimp only
  exact ⟨left_giant_sourceBounds _ _ hh, right_giant_sourceBounds _ _ hh hg⟩

end Ostmann.Arithmetic.HistoryGiantSourceBounds

end

end OAI
