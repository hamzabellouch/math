import OAI.Geometry.RCD.Sobolev.PoissonGradientInput
import OAI.Geometry.RCD.Sobolev.PoissonSourceEstimates

namespace OAI

/-! # Interior gradient control from the proved Poisson height estimate -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [BorelSpace X] [ProperSpace X] in
/-- The nonnegative replacement defect and a bound on the boundary datum
bound the absolute value of the actual Poisson replacement. -/
theorem replacement_value_bound_of_height (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (q f : SobolevSpace μ hQ) (Ω : Set X) {B H : ℝ} (hBH : B ≤ H)
    (hq : ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ SobolevSpace.toLp μ hQ q x ∧ SobolevSpace.toLp μ hQ q x ≤ B)
    (hh : ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ SobolevSpace.toLp μ hQ (q - f) x ∧ SobolevSpace.toLp μ hQ (q - f) x ≤ H) :
    ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ f x| ≤ H := by
  filter_upwards [hq, hh,
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ q) (SobolevSpace.toLp μ hQ f))]
    with x hx hhx hsub
  rw [map_sub, hsub, Pi.sub_apply] at hhx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [ProperSpace X] in
/-- The gradient input now applies to the constructed replacement:
the required supremum bound is derived from the nonnegative Poisson defect. -/
theorem LocalPoissonGradientInput.bound_of_replacement {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hgradient : LocalPoissonGradientInput hX)
    (hn : 2 ≤ n)
    (p : X) {r c B H : ℝ} (hr : 0 < r) (hcurv : -1 ≤ K * r ^ 2)
    (hH : 0 ≤ H) (hBH : B ≤ H)
    (q f : SobolevSpace (hausdorff n X) hX.quadratic)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8 * r)) f c)
    (hq : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic q x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic q x ≤ B)
    (hh : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic (q - f) x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (q - f) x ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * r)),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (C * (H / r + |c| * r)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := hgradient hn
  exact ⟨C, hC, hbound p r hr hcurv f c H hH hf
    (replacement_value_bound_of_height _ _ q f _ hBH hq hh)⟩

end RegularPointCoordinates

end

end OAI
