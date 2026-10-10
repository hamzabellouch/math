import OAI.Geometry.RCD.Sobolev.SobolevWeakEnergyLower

namespace OAI

/-! # Two approximations to one gradient have vanishing pairwise error -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weighted_gradient_pair_le_two
    {φ : X → ℝ} (hφ : AEStronglyMeasurable φ μ) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B) (hφ0 : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (u v f : SobolevSpace μ Q) :
    weightedGamma μ Q φ (u-v) (u-v) ≤
      2*weightedGamma μ Q φ (u-f) (u-f)+2*weightedGamma μ Q φ (v-f) (v-f) := by
  let P := weightedGammaCLM μ Q hφ hB
  have hn : 0 ≤ P ((u-f)+(v-f)) ((u-f)+(v-f)) :=
    weightedGamma_nonneg_of_weight μ Q hφ0 _
  have huv : P u v = P v u := weightedGamma_comm μ Q φ _ _
  have huf : P u f = P f u := weightedGamma_comm μ Q φ _ _
  have hvf : P v f = P f v := weightedGamma_comm μ Q φ _ _
  change P (u-v) (u-v) ≤ 2*P (u-f) (u-f)+2*P (v-f) (v-f)
  simp only [map_add,map_sub,add_apply,sub_apply] at hn ⊢
  linarith only [hn,huv,huf,hvf]

theorem weighted_gradient_pair_tendsto_zero
    {φ : X → ℝ} (hφ : AEStronglyMeasurable φ μ) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B) (hφ0 : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (u v : ℕ → SobolevSpace μ Q) (f : SobolevSpace μ Q)
    (hu : Tendsto (fun k => weightedGamma μ Q φ (u k-f) (u k-f)) atTop (𝓝 0))
    (hv : Tendsto (fun k => weightedGamma μ Q φ (v k-f) (v k-f)) atTop (𝓝 0)) :
    Tendsto (fun k => weightedGamma μ Q φ (u k-v k) (u k-v k)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun k => weightedGamma_nonneg_of_weight μ Q hφ0 (u k-v k))
    (fun k => weighted_gradient_pair_le_two μ Q hφ hB hφ0 (u k) (v k) f)
  simpa only [mul_zero,zero_add] using (hu.const_mul 2).add (hv.const_mul 2)

end RegularPointCoordinates

end

end OAI
