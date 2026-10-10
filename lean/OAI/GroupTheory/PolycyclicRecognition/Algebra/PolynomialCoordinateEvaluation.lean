import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateOperations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteCoordinateSmoothness

namespace OAI

/-! # Polynomial maps detected by point evaluations

A finite-dimensional function space is separated by evaluations. Their span
is the whole dual, so polynomiality at every point gives polynomial coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

def multivariatePolynomialEvaluation (I : Type*) :
    MvPolynomial I ℝ →ₗ[ℝ] ((I → ℝ) → ℝ) where
  toFun p x := MvPolynomial.eval x p
  map_add' p q := by ext x; exact map_add _ p q
  map_smul' a p := by
    ext x
    change MvPolynomial.eval x (a • p) = a * MvPolynomial.eval x p
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.eval_C]

def multivariatePolynomialFunctions (I : Type*) :
    Submodule ℝ ((I → ℝ) → ℝ) := (multivariatePolynomialEvaluation I).range

theorem mem_multivariatePolynomialFunctions {I : Type*} {f : (I → ℝ) → ℝ} :
    f ∈ multivariatePolynomialFunctions I ↔
      ∃ p : MvPolynomial I ℝ, ∀ x, MvPolynomial.eval x p = f x := by
  change (∃ p, multivariatePolynomialEvaluation I p = f) ↔ _
  simp only [funext_iff]
  rfl

theorem coordinatePolynomial_iff_components {I J : Type*}
    {f : (I → ℝ) → (J → ℝ)} : IsCoordinatePolynomial f ↔
      ∀ j, (fun x => f x j) ∈ multivariatePolynomialFunctions I := by
  simp only [IsCoordinatePolynomial, mem_multivariatePolynomialFunctions]
  exact ⟨fun ⟨p, hp⟩ j => ⟨p j, fun x => hp x j⟩,
    fun h => by choose p hp using h; exact ⟨p, fun x j => hp j x⟩⟩

theorem IsCoordinatePolynomial.linear_pi {d : ℕ} {J : Type*}
    (A : (Fin d → ℝ) →ₗ[ℝ] (J → ℝ)) : IsCoordinatePolynomial A := by
  apply coordinatePolynomial_iff_components.mpr
  intro j
  let f : (Fin d → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
    LinearMap.pi (fun _ => (LinearMap.proj j).comp A)
  exact coordinatePolynomial_iff_components.mp (IsCoordinatePolynomial.linear f) 0

variable {I G V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem polynomial_of_multivariate_evaluations
    (e : V →ₗ[ℝ] (G → ℝ)) (he : Function.Injective e)
    (F : (I → ℝ) → V)
    (hF : ∀ g, (fun x => e (F x) g) ∈ multivariatePolynomialFunctions I)
    (f : Module.Dual ℝ V) :
    (fun x => f (F x)) ∈ multivariatePolynomialFunctions I := by
  have hf : f ∈ Submodule.span ℝ (Set.range (coordinateEvaluation e)) := by
    rw [span_coordinateEvaluation e he]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hF g
  | zero => exact (multivariatePolynomialFunctions I).zero_mem
  | add f g _ _ hf hg => exact (multivariatePolynomialFunctions I).add_mem hf hg
  | smul a f _ hf => exact (multivariatePolynomialFunctions I).smul_mem a hf

theorem coordinatePolynomial_of_evaluations
    (e : V →ₗ[ℝ] (G → ℝ)) (he : Function.Injective e)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (F : (I → ℝ) → V)
    (hF : ∀ g, (fun x => e (F x) g) ∈ multivariatePolynomialFunctions I) :
    IsCoordinatePolynomial (fun x => b.equivFun (F x)) := by
  apply coordinatePolynomial_iff_components.mpr
  intro j
  exact polynomial_of_multivariate_evaluations e he F hF
    ((LinearMap.proj j).comp b.equivFun.toLinearMap)

end PolycyclicRecognition

end

end OAI
