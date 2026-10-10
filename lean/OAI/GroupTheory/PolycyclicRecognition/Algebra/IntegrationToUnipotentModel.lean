import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulRepresentationBCH
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteProductGlobalChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSmoothHom

namespace OAI

/-! # Integrating into a concretely represented nilpotent model

Both finite product formulas use a common enlarged bound. Global exponential
coordinates in the target give continuity; the exponential curves then give
smoothness and the prescribed differential.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L E G A : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

theorem integrate_to_unipotent_model
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1
      j.toLinearMap.toContinuousLinearMap)
    (c : ℕ) (hc : ∀ l : List (GroupLieAlgebra (𝓘(ℝ, E)) G),
      c ≤ l.length → (l.map j).prod = 0)
    (f : L →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ φ : L →* G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, E)) ∞ φ ∧
      (∀ x, φ x = Exp (f x)) ∧
      ∀ v, mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, E)) φ 1 v = f v := by
  obtain ⟨chart, hchart⟩ := globalExponentialChart_of_finite_products Exp hExp hnil
    (universalDynkinCoefficients c)
    (fun _ X => finite_bch_of_faithful_nilpotent_representation Exp hExp ρ hρ j hd c
      (fun l hl => hc l hl.le) X)
  obtain ⟨m, d, σ, k, hσ, _, _, hσexp, _, hk⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ L)
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hmul (x y : L) : Exp (f (x * y)) = Exp (f x) * Exp (f y) := by
    have hs := finite_product_of_unipotent_coordinates σ hσ k hσexp (max d c)
      (fun l hl => hk l ((Nat.le_max_left d c).trans hl.le)) ![x, y]
    have ht := finite_bch_of_faithful_nilpotent_representation Exp hExp ρ hρ j hd (max d c)
      (fun l hl => hc l ((Nat.le_max_right d c).trans hl.le)) ![f x, f y]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one] at hs ht
    rw [hs, finiteDynkinPolynomial_map, ht]
    congr 2
    funext i
    fin_cases i <;> rfl
  let φ : L →* G :=
    { toFun := fun x => Exp (f x)
      map_one' := by rw [P.one_eq_zero, map_zero, hExp.map_zero]
      map_mul' := hmul }
  have hcont : Continuous φ := by
    have heq : (φ : L → G) = fun x => chart (f x) := by
      funext x
      exact (hchart _).symm
    rw [heq]
    exact chart.continuous.comp f.toLinearMap.continuous_of_finiteDimensional
  have hs := contMDiff_of_exponential_compatibility
    PolynomialExponentialCoordinates.isGroupExponential_identity hExp φ hcont
    f.toLinearMap (fun _ => rfl)
  refine ⟨φ, hs, fun _ => rfl, ?_⟩
  exact mfderiv_eq_of_exponential_compatibility
    PolynomialExponentialCoordinates.isGroupExponential_identity hExp φ
    (hs.mdifferentiable (by simp)) f.toLinearMap (fun _ => rfl)

end PolycyclicRecognition

end

end OAI
