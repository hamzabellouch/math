import OAI.Combinatorics.ContingencyTables.Dense.DenseBoundedTrial
import OAI.Combinatorics.ContingencyTables.Transport.FiniteScaledDraw
import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts

namespace OAI

/-! # Independent actual Boolean offset draws realize the bounded offset law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {q : ℕ}

abbrev OffsetWords (e : I × J ≃ Fin q) (w : I × J → ℕ) (h d : ℕ) :=
  ∀ j : Fin q, Fin (offsetBitLength (w (e.symm j)) h d) → Bool

def drawOffsetWords (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (h d : ℕ) (bits : OffsetWords e w h d) : Offset w :=
  offsetCoordinateEquiv e w (fun j =>
    scaledBitInteger (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _) (bits j))

/-- Every coordinate uses its declared independent bounded Boolean word;
the resulting offset vector has the bounded quotient-offset law. -/
theorem drawOffsetWordsLaw_eq (e : I × J ≃ Fin q) (w : I × J → ℕ)
    [DecidableEq (Offset w)]
    (hw : ∀ p, 0 < w p) (h d : ℕ) :
    mapLaw (uniformLaw (α := OffsetWords e w h d)) (drawOffsetWords e w hw h d) =
      boundedOffsetLaw e w hw h d := by
  unfold drawOffsetWords boundedOffsetLaw
  refine (mapLaw_equiv_output (offsetCoordinateEquiv e w)
    (uniformLaw (α := OffsetWords e w h d)) (fun bits j =>
      scaledBitInteger (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _)
        (bits j))).trans ?_
  congr 1
  rw [← pi_uniformLaw, pi_mapLaw]
  congr 1
  funext j
  exact scaledBitIntegerLaw_eq (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _)

end

end ContingencyTables.GridBoundary

end OAI
