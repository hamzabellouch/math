import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralRelativeEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorWholeFutureEntropy

namespace OAI

/-! # Bring neutral displacements at a terminal time back to the initial time -/

noncomputable section
open Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem diagonal_negative_iterate_injective {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (N : ℕ) :
    Function.Injective
      ((fun z : X n => rightAction z (diagonalOneParameter ell hell (-1)))^[N]) :=
  (rightActionHomeomorph (diagonalOneParameter ell hell (-1))).injective.iterate N

theorem neutral_displacement_of_terminal {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (N : ℕ)
    (x y : X n) (g : G n)
    (hcomm : ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (hterminal : rightAction
      ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[N] x) g =
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[N] y) :
    rightAction x g=y := by
  apply diagonal_negative_iterate_injective ell hell N
  calc
    _ = rightAction
        ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[N] x) g := by
      rw [diagonal_negative_iterate,diagonal_negative_iterate,
        rightAction_mul,rightAction_mul,(hcomm (-(N:ℝ))).eq]
    _ = _ := hterminal

theorem fullFutureObservation_terminal {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (N : ℕ) (x : X n) :
    fullFutureObservation
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q N x =
    fullFutureObservation
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0
      ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[N] x) := by
  funext k
  dsimp only [fullFutureObservation]
  rw [zero_add,←Function.iterate_add_apply,Nat.add_comm]

end DukePrimeDegree

end

end OAI
