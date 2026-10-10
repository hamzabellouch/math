import OAI.Analysis.KadisonKastler.CornerPullbackVectors

namespace OAI

/-! # Transferring a norm comparison back into a projection corner

The transfer loses no norm: a unitary comparison of the pulled-back
functionals is exactly the comparison of the corresponding corner
functionals. Existence of the comparison unitary is a separate theorem.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem corner_unitary_comparison_norm (φ ψ : A →L[ℂ] ℂ)
    (p v : A) (hp : IsStarProjection p) (hv : star v*v=1)
    (hvp : v*star v=p) (hnorm : ‖v‖ ≤ 1)
    (hψ : cornerFunctional ψ p=ψ) (u : unitary A) :
    ‖sandwichFunctional φ (v*u.val*star v)-ψ‖ =
      ‖sandwichFunctional (sandwichFunctional φ (star v)) u.val -
        sandwichFunctional ψ (star v)‖ := by
  let f := sandwichFunctional (sandwichFunctional φ (star v)) u.val -
    sandwichFunctional ψ (star v)
  have he : sandwichFunctional f v = sandwichFunctional φ (v*u.val*star v)-ψ := by
    dsimp only [f]
    rw [sandwichFunctional_sub,sandwichFunctional_comp,sandwichFunctional_comp,
      sandwichFunctional_comp,hvp,sandwichFunctional_projection _ _ hp,hψ]
  rw [← he]
  exact sandwichFunctional_isometry_norm f v hv hnorm

end

end KadisonKastler

end OAI
