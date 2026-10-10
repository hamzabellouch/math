import Mathlib

namespace OAI

noncomputable section

universe u
namespace Problem346

variable (W : Type u) [AddCommGroup W] [Module ℂ W]

/-- Linear functionals separate points of the symmetric algebra over an infinite field. -/
theorem symAlg_eq_zero_of_lift_eq_zero (p : SymmetricAlgebra ℂ W)
    (h : ∀ φ : Module.Dual ℂ W, SymmetricAlgebra.lift φ p = 0) : p = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let e := SymmetricAlgebra.equivMvPolynomial b
  apply e.injective
  simp only [map_zero]
  apply MvPolynomial.funext
  intro x
  have he : (MvPolynomial.aeval x).comp e.toAlgHom =
      SymmetricAlgebra.lift (b.constr ℂ x) := by
    apply SymmetricAlgebra.algHom_ext
    apply b.ext
    intro i
    simp [e]
  have hx := congrArg (fun f : SymmetricAlgebra ℂ W →ₐ[ℂ] ℂ => f p) he
  simpa using hx.trans (h (b.constr ℂ x))

/-- Evaluation at vectors separates the symmetric algebra on the dual of a finite-dimensional
space. -/
theorem symAlg_dual_eq_zero_of_eval_eq_zero [FiniteDimensional ℂ W]
    (p : SymmetricAlgebra ℂ (Module.Dual ℂ W))
    (h : ∀ x : W, SymmetricAlgebra.lift (Module.Dual.eval ℂ W x) p = 0) : p = 0 := by
  apply symAlg_eq_zero_of_lift_eq_zero
  intro φ
  obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective φ
  exact h x

end Problem346

end

end OAI
