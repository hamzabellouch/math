import OAI.Geometry.RCD.Sobolev.SharpRecoveryEnergy
import OAI.Geometry.RCD.Sobolev.CompactGradientRepresentative

namespace OAI

/-! # Global gradient bounds for the actual compact recoveries -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem compact_recovery_scaled_gradient_bound (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} {c : ℝ} {ψ : Euclidean n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (V : ℕ → X → Euclidean n) (q : ℕ → SobolevSpace μ hQ)
    (hzero : ∀ k, ∀ᵐ x ∂μ, x∉ball (p k) (c*r k) → SobolevSpace.toLp μ hQ (q k) x=0)
    (hgrad : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (c*r k)),
        r k*SobolevSpace.minimalSlope μ hQ (q k) x≤‖fderiv ℝ ψ (V k x)‖+δ) :
    ∃ Q : ℝ, 0≤Q ∧ ∀ᶠ k in atTop, ∀ᵐ x ∂μ,
      r k^2*localGamma μ hQ (q k) (q k) x≤Q^2 := by
  let G := smoothGradientTest hψ hs
  let Q := ‖G‖+1
  refine ⟨Q,by dsimp only [Q]; positivity,?_⟩
  filter_upwards [hgrad 1 zero_lt_one] with k hk
  have hfull := supported_recovery_slope μ hQ (q k) measurableSet_ball
    (fun x => add_nonneg (norm_nonneg _) zero_le_one) (hzero k) hk
  filter_upwards [hfull,localGamma_self μ hQ (q k),
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (q k))] with x hx he hn
  have hb : ‖fderiv ℝ ψ (V k x)‖≤‖G‖ := by
    exact (le_abs_self (G (V k x))).trans (G.norm_coe_le_norm (V k x))
  rw [he]
  have hn' := mul_nonneg (hr k).le hn
  have hh : r k*SobolevSpace.minimalSlope μ hQ (q k) x≤Q := hx.trans (by dsimp only [Q]; linarith)
  simpa only [mul_pow] using pow_le_pow_left₀ hn' hh 2

end RegularPointCoordinates

end

end OAI
