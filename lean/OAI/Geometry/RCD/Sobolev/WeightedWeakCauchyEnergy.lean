import OAI.Geometry.RCD.Sobolev.SobolevWeakEnergyLower

namespace OAI

/-! # A local energy Cauchy bound passes to the weak Sobolev limit -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weighted_energy_le_of_weak_cauchy
    (u : ℕ → SobolevSpace μ Q) (v : SobolevSpace μ Q)
    (hweak : ∀ ℓ : SobolevSpace μ Q →L[ℝ] ℝ,
      Tendsto (fun k => ℓ (u k)) atTop (𝓝 (ℓ v)))
    {η : X → ℝ} (hη : AEStronglyMeasurable η μ) {M : ℝ≥0}
    (hM : ∀ᵐ x ∂μ, ‖η x‖ ≤ M) (hη0 : ∀ᵐ x ∂μ, 0 ≤ η x)
    (i : ℕ) {A : ℝ}
    (hA : ∀ᶠ j in atTop, weightedGamma μ Q η (u i-u j) (u i-u j) ≤ A) :
    weightedGamma μ Q η (u i-v) (u i-v) ≤ A := by
  let P := weightedGammaCLM μ Q hη hM
  let f := u i-v
  have hp : Tendsto (fun j => P (u i-u j) f) atTop (𝓝 (P f f)) := by
    have hh : Tendsto (fun j => P (u i) f-P (u j) f) atTop
        (𝓝 (P (u i) f-P v f)) := tendsto_const_nhds.sub (hweak (P.flip f))
    change Tendsto (fun j => P (u i-u j) f) atTop (𝓝 (P (u i-v) f))
    simpa only [map_sub,sub_apply] using hh
  have hl : Tendsto (fun j => 2*P (u i-u j) f-P f f) atTop (𝓝 (P f f)) := by
    simpa only [two_mul,add_sub_cancel_right] using (hp.const_mul 2).sub_const (P f f)
  apply le_of_tendsto hl
  filter_upwards [hA] with j hj
  have hn : 0 ≤ P (u j-v) (u j-v) := weightedGamma_nonneg_of_weight μ Q hη0 _
  have hs : P (u i) v = P v (u i) := weightedGamma_comm μ Q η _ _
  have ht : P (u j) v = P v (u j) := weightedGamma_comm μ Q η _ _
  have hu : P (u i) (u j) = P (u j) (u i) := weightedGamma_comm μ Q η _ _
  change P (u i-u j) (u i-u j) ≤ A at hj
  dsimp only [f]
  simp only [map_sub,sub_apply] at hn hj ⊢
  linarith only [hn,hj,hs,ht,hu]

end RegularPointCoordinates

end

end OAI
