import OAI.Geometry.RCD.Sobolev.WeightedSobolevIntegralLower

namespace OAI

/-! # Stability of weighted Sobolev energy under bounded weight convergence

First use domination by the fixed gradient pairing in space, then the
uniform Sobolev norm bound in time. No joint pointwise gradient field is
assumed.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weightedGamma_weight_tendsto
    (w : ℕ → X → ℝ) (v : X → ℝ) (hw : ∀ k, AEStronglyMeasurable (w k) μ)
    {M : ℝ≥0} (hM : ∀ k, ∀ᵐ x ∂μ, ‖w k x‖ ≤ M)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun k => w k x) atTop (𝓝 (v x)))
    (f g : SobolevSpace μ Q) :
    Tendsto (fun k => weightedGamma μ Q (w k) f g) atTop (𝓝 (weightedGamma μ Q v f g)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (M:ℝ)*|localGamma μ Q f g x|)
  · intro k
    exact (hw k).mul (localGamma_memL1 μ Q f g).aestronglyMeasurable
  · exact (localGamma_memL1 μ Q f g).abs.const_mul M
  · intro k
    filter_upwards [hM k] with x hx
    rw [norm_mul,Real.norm_eq_abs (localGamma μ Q f g x)]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  · filter_upwards [hc] with x hx
    exact hx.mul_const _

theorem weighted_energy_time_weight_tendsto
    [ProperSpace X] {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (w : ℕ → X → ℝ) (v : X → ℝ) (hw : ∀ k, AEStronglyMeasurable (w k) μ)
    {M : ℝ≥0} (hM : ∀ k, ∀ᵐ x ∂μ, ‖w k x‖ ≤ M)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun k => w k x) atTop (𝓝 (v x)))
    (u : Y → SobolevSpace μ Q) (hu : AEStronglyMeasurable u ν)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ t ∂ν, ‖u t‖ ≤ C)
    (θ : Y → ℝ) (hθ : Integrable θ ν) :
    Tendsto (fun k => ∫ t, θ t*weightedGamma μ Q (w k) (u t) (u t) ∂ν) atTop
      (𝓝 (∫ t, θ t*weightedGamma μ Q v (u t) (u t) ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => |θ t| * ((M:ℝ)*C*C))
  · intro k
    exact hθ.aestronglyMeasurable.mul
      ((weightedGammaCLM μ Q (hw k) (hM k)).aestronglyMeasurable_comp₂ hu hu)
  · exact hθ.abs.mul_const _
  · intro k
    filter_upwards [hb] with t ht
    rw [norm_mul,Real.norm_eq_abs (θ t)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (weightedGamma_norm_le μ Q (hM k) (u t) (u t)).trans (by gcongr)
  · exact Eventually.of_forall fun t =>
      (weightedGamma_weight_tendsto μ Q w v hw hM hc (u t) (u t)).const_mul (θ t)

end RegularPointCoordinates

end

end OAI
