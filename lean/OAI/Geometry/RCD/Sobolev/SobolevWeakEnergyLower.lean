import OAI.Geometry.RCD.Sobolev.BoundedHilbertImageWeak
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Weak Sobolev convergence and positive weighted energy bounds

Strong L2 convergence and a bounded Sobolev norm suffice. No compactness
or convergence of the gradients is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem bounded_sobolev_functional_tendsto
    (u : ℕ → SobolevSpace μ Q) (v : SobolevSpace μ Q)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖u k‖ ≤ C)
    (hc : Tendsto (fun k => SobolevSpace.toLp μ Q (u k)) atTop
      (𝓝 (SobolevSpace.toLp μ Q v))) (ℓ : SobolevSpace μ Q →L[ℝ] ℝ) :
    Tendsto (fun k => ℓ (u k)) atTop (𝓝 (ℓ v)) := by
  let T := SobolevSpace.toLpCLM μ Q
  have hT : Function.Injective T := fun f g h => Subtype.ext h
  have hh := bounded_hilbert_image_inner_tendsto T hT u v hC hb hc
    ((InnerProductSpace.toDual ℝ (SobolevSpace μ Q)).symm ℓ)
  simpa only [InnerProductSpace.toDual_symm_apply] using hh

omit [ProperSpace X] in
theorem weightedGamma_nonneg_of_weight {η : X → ℝ} (hη : ∀ᵐ x ∂μ, 0 ≤ η x)
    (v : SobolevSpace μ Q) : 0 ≤ weightedGamma μ Q η v v := by
  apply integral_nonneg_of_ae
  filter_upwards [hη,localGamma_self μ Q v] with x hx hg
  rw [hg]
  exact mul_nonneg hx (sq_nonneg _)

theorem weighted_energy_lower_eventually
    (u : ℕ → SobolevSpace μ Q) (v : SobolevSpace μ Q)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖u k‖ ≤ C)
    (hc : Tendsto (fun k => SobolevSpace.toLp μ Q (u k)) atTop
      (𝓝 (SobolevSpace.toLp μ Q v)))
    {η : X → ℝ} (hη : AEStronglyMeasurable η μ) {M : ℝ≥0}
    (hM : ∀ᵐ x ∂μ, ‖η x‖ ≤ M) (hη0 : ∀ᵐ x ∂μ, 0 ≤ η x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, weightedGamma μ Q η v v-δ ≤ weightedGamma μ Q η (u k) (u k) := by
  let P := weightedGammaCLM μ Q hη hM
  have hp : Tendsto (fun k => P (u k) v) atTop (𝓝 (P v v)) :=
    bounded_sobolev_functional_tendsto μ Q u v hC hb hc (P.flip v)
  have hl : Tendsto (fun k => 2*P (u k) v-P v v) atTop (𝓝 (P v v)) := by
    simpa only [two_mul,add_sub_cancel_right] using (hp.const_mul 2).sub_const (P v v)
  have he : ∀ᶠ k in atTop, P v v-δ < 2*P (u k) v-P v v :=
    hl.eventually (lt_mem_nhds (by linarith))
  filter_upwards [he] with k hk
  have hn : 0 ≤ P (u k-v) (u k-v) := weightedGamma_nonneg_of_weight μ Q hη0 _
  have hs : P v (u k) = P (u k) v := weightedGamma_comm μ Q η v (u k)
  simp only [map_sub,sub_apply] at hn
  rw [hs] at hn
  change P v v-δ ≤ P (u k) (u k)
  linarith

theorem weighted_energy_le_of_bounded_L2_limit
    (u : ℕ → SobolevSpace μ Q) (v : SobolevSpace μ Q)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖u k‖ ≤ C)
    (hc : Tendsto (fun k => SobolevSpace.toLp μ Q (u k)) atTop
      (𝓝 (SobolevSpace.toLp μ Q v)))
    {η : X → ℝ} (hη : AEStronglyMeasurable η μ) {M : ℝ≥0}
    (hM : ∀ᵐ x ∂μ, ‖η x‖ ≤ M) (hη0 : ∀ᵐ x ∂μ, 0 ≤ η x)
    {A : ℝ} (he : Tendsto (fun k => weightedGamma μ Q η (u k) (u k)) atTop (𝓝 A)) :
    weightedGamma μ Q η v v ≤ A := by
  let P := weightedGammaCLM μ Q hη hM
  have hp : Tendsto (fun k => P (u k) v) atTop (𝓝 (P v v)) :=
    bounded_sobolev_functional_tendsto μ Q u v hC hb hc (P.flip v)
  have hbound (k : ℕ) : 2*P (u k) v-P v v ≤ P (u k) (u k) := by
    have hn : 0 ≤ P (u k-v) (u k-v) := weightedGamma_nonneg_of_weight μ Q hη0 _
    have hs : P v (u k) = P (u k) v := weightedGamma_comm μ Q η v (u k)
    simp only [map_sub,sub_apply] at hn
    rw [hs] at hn
    linarith
  have hl := (hp.const_mul 2).sub_const (P v v)
  have hres := le_of_tendsto_of_tendsto hl he (Eventually.of_forall hbound)
  change 2*weightedGamma μ Q η v v-weightedGamma μ Q η v v ≤ A at hres
  linarith

end RegularPointCoordinates

end

end OAI
