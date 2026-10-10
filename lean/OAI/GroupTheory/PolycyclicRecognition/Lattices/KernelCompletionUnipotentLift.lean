import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentKernelCompletion
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeAutomorphismUnipotent

namespace OAI

/-! # Nilpotent ambient conjugations extend as unipotent Lie automorphisms -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H] [Group G] [Group.IsNilpotent G]
  {i : K →* H} (C : NilpotentKernelCompletion i)

namespace NilpotentKernelCompletion

theorem unipotent_conjugation_extension (j : H →* G) (hj : Function.Injective j)
    (a : MulAut H) (t : G) (hconj : ∀ h, j (a h) = t * j h * t⁻¹)
    (ha : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.toMonoidHom).comp i))
    (hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.symm.toMonoidHom).comp i)) :
    ∃ A : C.carrier ≃ₗ⁅ℝ⁆ C.carrier,
      IsNilpotent (A.toLinearMap - 1) ∧ ∀ h, A (C.embed h) = C.embed (a h) := by
  obtain ⟨B, hB, _, hBe⟩ := C.automorphism_extension a ha hai
  let A := polynomialModelLieEquiv B hB
  have hAe (h : H) : A (C.embed h) = C.embed (a h) := by
    rw [polynomialModelLieEquiv_apply]
    exact hBe h
  refine ⟨A, ?_, hAe⟩
  exact lattice_automorphism_unipotent C.basis C.parameter C.polynomial
    C.parameter.surjective C.embed C.integer_grid j hj a t hconj A.toLinearMap hAe

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
