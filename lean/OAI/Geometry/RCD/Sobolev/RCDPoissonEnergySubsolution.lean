import OAI.Geometry.RCD.Sobolev.PoissonEnergySubsolution
import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction
import OAI.Geometry.RCD.Sobolev.PoissonHessianFromScalar

namespace OAI

/-! # The local energy subsolution from the proved RCD Bochner estimate -/

open Set Metric Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_energy_subsolution {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : X) {r : ℝ} (hr : 0<r)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ) (L : ℝ≥0)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (hgrad : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2) :
    ∃ (e : SobolevSpace (hausdorff n X) hX.quadratic) (B : ℝ), 0≤B ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic e =ᵐ[(hausdorff n X).restrict (ball p (2*r))]
        localGamma (hausdorff n X) hX.quadratic f f ∧
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic e x|≤B) ∧
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball p (2*r)) e (2*max (-K) 0) := by
  by_cases hK : K≤0
  · have hs := hX.scalarBochner_nonpositive K n hn hK p
    have hess := hX.poisson_hessian_input_of_scalar hn hs
    exact hess.energy_subsolution (max (-K) 0) (le_max_right _ _)
      (by linarith [le_max_left (-K) 0]) p r hr f c L hf hgrad
  · let h0 := hX.zero_of_nonneg_curvature hn (lt_of_not_ge hK).le
    have hs := h0.scalarBochner_nonpositive 0 n hn le_rfl p
    have hess := h0.poisson_hessian_input_of_scalar hn hs
    exact hess.energy_subsolution (max (-K) 0) (le_max_right _ _)
      (by linarith [le_max_right (-K) 0]) p r hr f c L hf hgrad

end RegularPointCoordinates

end

end OAI
