import OAI.Geometry.RCD.Harmonic.HarmonicLinearSharp

namespace OAI

/-! # Scalar multiplication of the actual local Sobolev value convergence -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [BorelSpace X] [ProperSpace X] in
theorem sobolev_linear_value_convergence_smul {n : ℕ}
    (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (p : ℕ → X) (r : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (w : ℕ → SobolevSpace μ hQ) (L : Euclidean n →L[ℝ] ℝ)
    {S c : ℝ} (hc : 0 < c)
    (hconv : ∀ W : ℝ, 0 < W → W < S → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp μ hQ (w k) x-L (V k x)| ≤ δ) :
    ∀ W : ℝ, 0 < W → W < S → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp μ hQ (c • w k) x-(c • L) (V k x)| ≤ δ := by
  intro W hW hWS δ hδ
  filter_upwards [hconv W hW hWS (δ/c) (div_pos hδ hc)] with k hk
  have he : SobolevSpace.toLp μ hQ (c • w k) =ᵐ[μ]
      fun x => c*SobolevSpace.toLp μ hQ (w k) x := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [hk,ae_restrict_of_ae he] with x hx heq
  rw [heq]
  change |c*SobolevSpace.toLp μ hQ (w k) x-c*L (V k x)| ≤ δ
  rw [← mul_sub,abs_mul,abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left hx hc.le).trans_eq (by field_simp)

end RegularPointCoordinates

end

end OAI
