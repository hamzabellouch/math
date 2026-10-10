import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelDifference

namespace OAI

/-! # Extending lattice identities through a polynomial coordinate parameter

The parameter need not be linear. This permits ordered exponential coordinates
whose integral grid parametrizes a nilpotent lattice.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {d : ℕ} (b : Basis (Fin d) ℝ L)

theorem polynomial_mul_of_parameter_grid {f p : L → L}
    (hf : IsPolynomialInBasis b b f) (hp : IsPolynomialInBasis b b p)
    (hps : Function.Surjective p)
    (hm : ∀ z w : Fin d → ℤ,
      f (p (b.equivFun.symm (fun i => (z i : ℝ))) * p (b.equivFun.symm (fun i => (w i : ℝ)))) =
      f (p (b.equivFun.symm (fun i => (z i : ℝ)))) * f (p (b.equivFun.symm (fun i => (w i : ℝ))))) :
    ∀ x y, f (x * y) = f x * f y := by
  have hmul := coordinatePolynomial_dynkinProduct P.coefficients (basisBracket b)
  have hmul_eq (u v : Fin d → ℝ) :
      dynkinProduct P.coefficients (basisBracket b) u v =
        b.equivFun (b.equivFun.symm u * b.equivFun.symm v) := by
    simpa only [LinearEquiv.apply_symm_apply, ← P.mul_eq] using
      (basis_dynkinProduct b P.coefficients (b.equivFun.symm u) (b.equivFun.symm v))
  have hpl := IsCoordinatePolynomial.comp hp
    (IsCoordinatePolynomial.reindex (Sum.inl : Fin d → Fin d ⊕ Fin d))
  have hpr := IsCoordinatePolynomial.comp hp
    (IsCoordinatePolynomial.reindex (Sum.inr : Fin d → Fin d ⊕ Fin d))
  have hl := IsCoordinatePolynomial.comp hf (hmul.comp (hpl.pair hpr))
  have hr := hmul.comp ((IsCoordinatePolynomial.comp hf hpl).pair
    (IsCoordinatePolynomial.comp hf hpr))
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, hmul_eq,
    LinearEquiv.symm_apply_apply] at hl hr
  have heq := IsCoordinatePolynomial.ext_integer_grid hl hr (by
    intro z
    exact congrArg b.equivFun (hm (z ∘ Sum.inl) (z ∘ Sum.inr)))
  intro x y
  obtain ⟨u, rfl⟩ := hps x
  obtain ⟨v, rfl⟩ := hps y
  apply b.equivFun.injective
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    LinearEquiv.symm_apply_apply] using congrFun heq (Sum.elim (b.equivFun u) (b.equivFun v))

omit P [FiniteDimensional ℝ L] in
theorem polynomial_leftInverse_of_parameter_grid {f g p : L → L}
    (hf : IsPolynomialInBasis b b f) (hg : IsPolynomialInBasis b b g)
    (hp : IsPolynomialInBasis b b p) (hps : Function.Surjective p)
    (h : ∀ z : Fin d → ℤ,
      g (f (p (b.equivFun.symm (fun i => (z i : ℝ))))) =
        p (b.equivFun.symm (fun i => (z i : ℝ)))) : Function.LeftInverse g f := by
  have he : (g ∘ f) ∘ p = p := ((hg.comp hf).comp hp).ext_integer_grid hp h
  intro x
  obtain ⟨y, rfl⟩ := hps x
  exact congrFun he y

def polynomialGroupEquivFromParameter {f g p : L → L}
    (hf : IsPolynomialInBasis b b f) (hg : IsPolynomialInBasis b b g)
    (hp : IsPolynomialInBasis b b p) (hps : Function.Surjective p)
    (hm : ∀ z w : Fin d → ℤ,
      f (p (b.equivFun.symm (fun i => (z i : ℝ))) * p (b.equivFun.symm (fun i => (w i : ℝ)))) =
      f (p (b.equivFun.symm (fun i => (z i : ℝ)))) * f (p (b.equivFun.symm (fun i => (w i : ℝ)))))
    (hl : ∀ z : Fin d → ℤ,
      g (f (p (b.equivFun.symm (fun i => (z i : ℝ))))) = p (b.equivFun.symm (fun i => (z i : ℝ))))
    (hr : ∀ z : Fin d → ℤ,
      f (g (p (b.equivFun.symm (fun i => (z i : ℝ))))) = p (b.equivFun.symm (fun i => (z i : ℝ)))) :
    L ≃* L where
  toFun := f
  invFun := g
  left_inv := polynomial_leftInverse_of_parameter_grid b hf hg hp hps hl
  right_inv := polynomial_leftInverse_of_parameter_grid b hg hf hp hps hr
  map_mul' := polynomial_mul_of_parameter_grid b hf hp hps hm

end PolycyclicRecognition

end

end OAI
