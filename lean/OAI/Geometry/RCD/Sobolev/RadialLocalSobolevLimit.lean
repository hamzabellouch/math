import OAI.Geometry.RCD.Sobolev.RadialLocalSobolev
import OAI.Geometry.RCD.Metric.CompactSupportedL2Limit
import OAI.Geometry.RCD.Sobolev.SobolevWeakEnergyLower

namespace OAI

/-! # Local Lipschitz limits in the original Sobolev space

The radial realizations converge strongly in L2 and weakly in H1.
Positive bounded weights therefore give the expected energy lower bound.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

theorem radialLocalSobolev_L2_limit (z : X) {r : ℝ} (hr : 0 < r)
    (F : ℕ → X → ℝ) (f : X → ℝ) (L A : ℝ≥0)
    (hF : ∀ k, LipschitzOnWith L (F k) (closedBall z (2*r)))
    (hf : LipschitzOnWith L f (closedBall z (2*r)))
    (hFb : ∀ k, ∀ x ∈ closedBall z (2*r), |F k x| ≤ A)
    (hfb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A)
    (hc : ∀ x ∈ closedBall z (2*r), Tendsto (fun k => F k x) atTop (𝓝 (f x))) :
    Tendsto (fun k => SobolevSpace.toLp μ Q
      (radialLocalSobolev μ Q z hr (hF k) (hFb k))) atTop
      (𝓝 (SobolevSpace.toLp μ Q (radialLocalSobolev μ Q z hr hf hfb))) := by
  apply compact_supported_L2_limit μ measurableSet_closedBall
    (isCompact_closedBall z (2*r)).measure_lt_top.ne
    _ _ (fun k x => radialCutoff z r x*F k x) (fun x => radialCutoff z r x*f x)
    (fun k => radialLocalSobolev_coe μ Q z hr (hF k) (hFb k))
    (radialLocalSobolev_coe μ Q z hr hf hfb) A.coe_nonneg
    (fun k => (radial_local_lipschitz_cutoff z hr (hF k) (hFb k)).2)
    (radial_local_lipschitz_cutoff z hr hf hfb).2
  · intro k x hx
    rw [radialCutoff_eq_zero z hr
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hx)),zero_mul]
  · intro x hx
    rw [radialCutoff_eq_zero z hr
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hx)),zero_mul]
  · intro x hx
    exact (hc x hx).const_mul _

theorem radialLocalSobolev_weak_limit (z : X) {r : ℝ} (hr : 0 < r)
    (F : ℕ → X → ℝ) (f : X → ℝ) (L A : ℝ≥0)
    (hF : ∀ k, LipschitzOnWith L (F k) (closedBall z (2*r)))
    (hf : LipschitzOnWith L f (closedBall z (2*r)))
    (hFb : ∀ k, ∀ x ∈ closedBall z (2*r), |F k x| ≤ A)
    (hfb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A)
    (hc : ∀ x ∈ closedBall z (2*r), Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (ℓ : SobolevSpace μ Q →L[ℝ] ℝ) :
    Tendsto (fun k => ℓ (radialLocalSobolev μ Q z hr (hF k) (hFb k))) atTop
      (𝓝 (ℓ (radialLocalSobolev μ Q z hr hf hfb))) := by
  obtain ⟨C,hC,hbound⟩ := radialLocalSobolev_uniform_bound μ Q z hr L A
  exact bounded_sobolev_functional_tendsto μ Q _ _ hC
    (fun k => hbound _ (hF k) (hFb k))
    (radialLocalSobolev_L2_limit μ Q z hr F f L A hF hf hFb hfb hc) ℓ

end RegularPointCoordinates

end

end OAI
