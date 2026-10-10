import OAI.Geometry.RCD.Sobolev.EnergyDensityLimits
import OAI.Geometry.RCD.Sobolev.WeightedGammaJointLimit
import OAI.Geometry.RCD.Sobolev.WeightedL2SquareLimit

namespace OAI

/-! # The Bochner limit with an arbitrary bounded Sobolev test -/

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem bochner_sobolev_limit {us Gs : ℕ → SobolevSpace μ hQ} {u G : SobolevSpace μ hQ}
    {ds : ℕ → Lp ℝ 2 μ} {d : Lp ℝ 2 μ} (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (us k) x ≤ L)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u)) (hd : Tendsto ds atTop (𝓝 d))
    (hGs : ∀ k, SobolevSpace.toLp μ hQ (Gs k) =ᵐ[μ] localGamma μ hQ (us k) (us k))
    (hG : SobolevSpace.toLp μ hQ G =ᵐ[μ] localGamma μ hQ u u)
    {B : ℝ} (hB : 0 ≤ B) (hE : ∀ k, energyForm μ hQ (Gs k) (Gs k) ≤ B)
    (w : SobolevSpace μ hQ) {v : X → ℝ} (hv : Measurable v) (C : ℝ≥0)
    (hC : ∀ x, |v x| ≤ C) (K : ℝ)
    (hb : ∀ k, energyForm μ hQ (Gs k) w +
      2 * K * inner ℝ (SobolevSpace.toLp μ hQ w) (SobolevSpace.toLp μ hQ (Gs k)) -
      2 * (∫ x, v x * (ds k x) ^ 2 ∂μ) - 2 * weightedGamma μ hQ (ds k) (us k) w ≤ 0) :
    energyForm μ hQ G w + 2 * K * inner ℝ (SobolevSpace.toLp μ hQ w) (SobolevSpace.toLp μ hQ G) -
      2 * (∫ x, v x * (d x) ^ 2 ∂μ) - 2 * weightedGamma μ hQ d u w ≤ 0 := by
  have h₁ := gamma_representatives_energy_tendsto μ hQ L hus hu hconv hGs hG hB hE w
  have h₂ : Tendsto (fun k => inner ℝ (SobolevSpace.toLp μ hQ w)
      (SobolevSpace.toLp μ hQ (Gs k))) atTop
      (𝓝 (inner ℝ (SobolevSpace.toLp μ hQ w) (SobolevSpace.toLp μ hQ G))) :=
    tendsto_const_nhds.inner (gamma_representatives_tendsto μ hQ L hus hu hconv hGs hG)
  have h₃ := weightedL2_square_tendsto μ hv C hC hd
  have h₄ := weightedGamma_joint_tendsto μ hQ w L hus hu hconv hd
  exact le_of_tendsto (((h₁.add (h₂.const_mul (2 * K))).sub
    (h₃.const_mul 2)).sub (h₄.const_mul 2)) (Eventually.of_forall hb)

end RegularPointCoordinates

end OAI
