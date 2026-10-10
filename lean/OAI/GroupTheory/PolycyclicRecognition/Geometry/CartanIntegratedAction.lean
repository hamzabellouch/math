import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConjugationLift
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSemidirectWords

namespace OAI

/-! # The Cartan action, assembled from actual conjugation

The action laws are derived from a faithful ambient inclusion. They are not
assumed for the logarithmically parameterized adjoint automorphisms.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)
  {A G : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Pointwise adjoint automorphisms acquire the exact group action law
because their images under the injective inclusion are conjugations. -/
theorem exists_integrated_cartan_action
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ιN : N →* G) (hιN : Function.Injective ιN) (ιD : D →* G)
    (hN : ∀ x : cartanRootIdeal H, ρ (ιN (ExpN (eN x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (ιD (ExpD (eD h))) = algebraExpUnit (j h)) :
    ∃ φ : D →* MulAut N,
      (∀ d, φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
        (cartanLog H eD ExpD hbijD d)) ∧
      ∀ d g, ιN (φ d g) = ιD d * ιN g * (ιD d)⁻¹ := by
  let a : D → MulAut N := fun d => M.adjointGroupAutomorphism T eN ExpN
    hExpN hbijN dynkinN (cartanLog H eD ExpD hbijD d)
  have ha (d : D) (g : N) : ιN (a d g) = ιD d * ιN g * (ιD d)⁻¹ := by
    have h := M.adjointGroupAutomorphism_eq_conjugation T eN ExpN hExpN hbijN dynkinN
      j ρ hρ ιN (fun h => ιD (ExpD (eD h))) hN hD (cartanLog H eD ExpD hbijD d) g
    simpa only [exp_cartanLog] using h
  exact ⟨conjugationLift ιN ιD hιN a ha, fun _ => rfl, ha⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
