import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateEvaluation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateMatrixRepresentation

namespace OAI

/-! # Polynomial coordinate-orbit representations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {G Q I : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [Group G] [LieGroup (𝓘(ℝ, G)) ⊤ G]
  {m : ℕ} (q : Q → G → ℝ)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q)

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem polynomial_coordinateAction (γ : (I → ℝ) → G)
    (hγ : ∀ a b i, (fun x => q i ((a * γ x) * b)) ∈ multivariatePolynomialFunctions I)
    (v : Fin m → ℝ) (f : Module.Dual ℝ (Fin m → ℝ)) :
    (fun x => f (smoothCoordinateAction q B (γ x) v)) ∈
      multivariatePolynomialFunctions I := by
  let e := (coordinateOrbitSpan q).subtype.comp B.toLinearMap
  apply polynomial_of_multivariate_evaluations e
    (Subtype.coe_injective.comp B.injective) _ ?_ f
  intro a
  change (fun x => (B (smoothCoordinateAction q B (γ x) v) : G → ℝ) a) ∈ _
  simp only [smoothCoordinateAction_eval]
  have hfun (u : G → ℝ) (hu : u ∈ coordinateOrbitSpan q) :
      (fun x => u (a * γ x)) ∈ multivariatePolynomialFunctions I := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨⟨b, i⟩, rfl⟩ := hu
      exact hγ a b i
    | zero => exact (multivariatePolynomialFunctions I).zero_mem
    | add f g _ _ hf hg => exact (multivariatePolynomialFunctions I).add_mem hf hg
    | smul c f _ hf => exact (multivariatePolynomialFunctions I).smul_mem c hf
  exact hfun _ (B v).2

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem polynomial_coordinateMatrix (γ : (I → ℝ) → G)
    (hγ : ∀ a b i, (fun x => q i ((a * γ x) * b)) ∈ multivariatePolynomialFunctions I)
    (i j : Fin m) :
    (fun x => (coordinateMatrixRepresentation q B (γ x) : Matrix (Fin m) (Fin m) ℝ) i j) ∈
      multivariatePolynomialFunctions I := by
  exact polynomial_coordinateAction q B γ hγ (Pi.single j 1) (LinearMap.proj i)

def coordinateMatrixReadout : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Q → ℝ) where
  toFun A i := (B (A.mulVec (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1
  map_add' A C := by
    funext i
    simp only [Matrix.add_mulVec, map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' a A := by
    funext i
    simp only [RingHom.id_apply, Matrix.smul_mulVec, map_smul, Submodule.coe_smul, Pi.smul_apply]

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem coordinateMatrixReadout_apply (g : G) :
    coordinateMatrixReadout q B (coordinateMatrixRepresentation q B g) = fun i => q i g := by
  funext i
  dsimp only [coordinateMatrixReadout, LinearMap.coe_mk, AddHom.coe_mk]
  change (B (((LinearMap.toMatrixAlgEquiv' (smoothCoordinateAction q B g))).mulVec
    (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1 = q i g
  rw [← Matrix.toLin'_apply]
  change (B (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (smoothCoordinateAction q B g))
    (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1 = q i g
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  change (B (smoothCoordinateAction q B g
    (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1 = q i g
  rw [smoothCoordinateAction_eval, B.apply_symm_apply, one_mul]

end PolycyclicRecognition

end

end OAI
