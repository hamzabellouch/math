import Mathlib
import OAI.Analysis.Commutator.CyclicCb
import OAI.Analysis.Commutator.RectangularColumn

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

theorem cyclic_matrix_bound_unconditional (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (Δ : A →L[ℂ] (H →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω))
    (X : CStarMatrix ι ι A) :
    ‖matrixAction (fun i j => Δ (X i j))‖ ≤ (16*‖Δ‖)*‖X‖ := by
  have h := cyclic_matrix_bound σ lam Δ hΔ Ω hΩ (4*‖Δ‖) (by positivity)
    (fun v ζ => RectangularColumn.column_bound σ lam Δ hΔ v ζ) X
  convert h using 1
  ring

end Kadison.CyclicColumns

end

end
end

end OAI
