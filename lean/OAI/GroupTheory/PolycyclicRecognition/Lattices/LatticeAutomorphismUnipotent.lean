import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAutomorphismDifference

namespace OAI

/-! # Unipotence of a lattice automorphism induced by nilpotent conjugation

A polynomial surjective coordinate parameter suffices. Its integral grid
only has to land in the lattice; no additive description of that lattice is
assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L G H : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] [Group H] [Group.IsNilpotent G]

theorem lattice_automorphism_unipotent {d : ℕ} (b : Basis (Fin d) ℝ L)
    (p : L → L) (hp : IsPolynomialInBasis b b p) (hsurj : Function.Surjective p)
    (e : H →* L)
    (hgrid : ∀ z : Fin d → ℤ, ∃ x : H,
      e x = p (b.equivFun.symm (fun i => (z i : ℝ))))
    (j : H →* G) (hj : Function.Injective j)
    (a : H ≃* H) (t : G) (ha : ∀ x, j (a x) = t * j x * t⁻¹)
    (A : L →ₗ[ℝ] L) (hA : ∀ x, A (e x) = e (a x)) :
    IsNilpotent (A - 1) := by
  let f : L → L := fun x => A x * (-x)
  let n := Group.nilpotencyClass G
  have hf : IsPolynomialInBasis b b f := polynomial_model_difference A b
  have hs : Function.Semiconj e (fun y => a y * y⁻¹) f := by
    intro x
    change e (a x * x⁻¹) = A (e x) * (-e x)
    rw [map_mul, map_inv, hA, P.inv_eq_neg]
  have hezero (x : H) : f^[n] (e x) = 0 := by
    rw [← hs.iterate_right n x, automorphism_difference_iterate_one j hj a t ha,
      map_one, P.one_eq_zero]
  have hz : IsPolynomialInBasis b b (fun _ : L => (0 : L)) := by
    simpa only [IsPolynomialInBasis, map_zero] using
      (IsCoordinatePolynomial.const (I := Fin d) (0 : Fin d → ℝ))
  have heq : f^[n] ∘ p = fun _ => (0 : L) :=
    ((hf.iterate n).comp hp).ext_integer_grid hz (by
      intro z
      obtain ⟨x, hx⟩ := hgrid z
      change f^[n] (p (b.equivFun.symm (fun i => (z i : ℝ)))) = 0
      rw [← hx]
      exact hezero x)
  apply nilpotent_linear_of_group_difference A n
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact congrFun heq x

end PolycyclicRecognition

end

end OAI
