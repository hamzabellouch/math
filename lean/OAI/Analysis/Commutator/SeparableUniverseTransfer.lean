import Mathlib
import OAI.Analysis.Commutator.SeparableBoundTransfer
import OAI.Analysis.Commutator.SeparableSmall
import OAI.Analysis.Commutator.UnitaryMainTransport

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison.SeparableTest

theorem SeparableBound.lift {c : ℝ} (hsmall : SeparableBound.{0} c) :
    SeparableBound.{u} c := by
  intro H _ _ _ _ P Y h hh X hX
  let U := (SeparableSmall.unitary H).symm
  let Q := UnitaryTransport.algebra U P
  have hb := hsmall (SeparableSmall.Model H) Q (U.conjStarAlgEquiv Y) h hh
    (fun i j => U.conjStarAlgEquiv (X i j))
    (fun i j => (UnitaryTransport.mem_algebra U P (X i j)).mpr (hX i j))
  change ‖diagonalAmplification h (U.conjStarAlgEquiv Y)*
    matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))-
    matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))*
    diagonalAmplification h (U.conjStarAlgEquiv Y)‖≤
    c*commutatorSeminorm (UnitaryTransport.algebra U P) (U.conjStarAlgEquiv Y)*
    ‖matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))‖ at hb
  simpa only [UnitaryTransport.matrix_commutator_norm,UnitaryTransport.seminorm,
    UnitaryTransport.matrix_norm] using hb

theorem bound_of_small_separable_bound {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P)
    {c : ℝ} (hc : 0≤c) (hsmall : SeparableBound.{0} c) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
  bound_of_separable_bound P Y h X hX hc hsmall.lift hh

end Kadison.SeparableTest

end

end
end

end OAI
