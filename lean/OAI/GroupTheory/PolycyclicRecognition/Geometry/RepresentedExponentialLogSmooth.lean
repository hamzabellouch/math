import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentedExponentialDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothImmersionCancellation

namespace OAI

/-! # Smooth inverse coordinates for a represented real triangular exponential

The global homeomorphism is retained as a separate hypothesis. Its inverse
is smooth because the represented exponential has injective differential
and the represented group coordinates are smooth.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E V L A M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  [TopologicalSpace M] [ChartedSpace E M]

theorem contMDiff_inverse_exponential_chart_of_triangular
    {n : ℕ} (T : TriangularAdjoint L n) (j : L →ₗ⁅ℝ⁆ A)
    (hj : Function.Injective j) (b : V ≃ₗ[ℝ] L) (chart : V ≃ₜ M)
    (ρ : M → A) (hρ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ ρ)
    (hexp : ∀ v, ρ (chart v) = NormedSpace.exp (j (b v))) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ chart.symm := by
  let J : V →L[ℝ] A := (j.toLinearMap.comp b.toLinearMap).toContinuousLinearMap
  let F : V → A := fun v => NormedSpace.exp (J v)
  have hF (v : V) : ContDiffAt ℝ ∞ F v :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (J v)).contDiffAt.comp v J.contDiff.contDiffAt
  have hD (v : V) : HasFDerivAt F ((fderiv ℝ NormedSpace.exp (J v)).comp J) v :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (J v)).differentiableAt.hasFDerivAt.comp v J.hasFDerivAt
  have hi (v : V) : Function.Injective ((fderiv ℝ NormedSpace.exp (J v)).comp J) := by
    intro w z hwz
    apply b.injective
    apply represented_exponential_differential_injective T j hj (b v)
    exact hwz
  have heq : F ∘ chart.symm = ρ := by
    funext g
    have h := hexp (chart.symm g)
    rw [chart.apply_symm_apply] at h
    exact h.symm
  intro g
  apply contMDiffAt_of_comp_of_injective_differential
    chart.symm.continuous.continuousAt (hF _) (hD _) (hi _)
  rw [heq]
  exact hρ g

end PolycyclicRecognition

end

end OAI
