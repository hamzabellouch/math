import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeAutomorphismUnipotent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelHom
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentLieFlow

namespace OAI

/-! # Extending nilpotent lattice conjugation to a real automorphism flow -/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold ContDiff
variable {L G H : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] [Group H] [Group.IsNilpotent G]

theorem exists_nilpotent_lattice_automorphism_log {d : ℕ} (b : Basis (Fin d) ℝ L)
    (p : L → L) (hp : IsPolynomialInBasis b b p) (hsurj : Function.Surjective p)
    (e : H →* L)
    (hgrid : ∀ z : Fin d → ℤ, ∃ x : H,
      e x = p (b.equivFun.symm (fun i => (z i : ℝ))))
    (j : H →* G) (hj : Function.Injective j)
    (a : H ≃* H) (t : G) (ha : ∀ x, j (a x) = t * j x * t⁻¹)
    (F : L ≃* L) (hF : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ F)
    (he : ∀ x, F (e x) = e (a x)) :
    ∃ D : LieDerivation ℝ L L, ∃ hD : IsNilpotent D.toLinearMap,
      ∀ x, nilpotentDerivationFlow D hD 1 x = F x := by
  let A := polynomialModelLieEquiv F hF
  have hA : IsNilpotent (A.toLinearMap - 1) :=
    lattice_automorphism_unipotent b p hp hsurj e hgrid j hj a t ha A.toLinearMap
      (by intro x; change A (e x) = e (a x); rw [polynomialModelLieEquiv_apply]; exact he x)
  refine ⟨unipotentLieLogarithm A hA, unipotentLieLogarithm_nilpotent A hA, ?_⟩
  intro x
  change unipotentLieFlow A hA 1 x = F x
  rw [unipotentLieFlow_one, polynomialModelLieEquiv_apply]

end PolycyclicRecognition

end

end OAI
