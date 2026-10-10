import OAI.Geometry.RCD.Heat.ScaledHeatLimitTimeBound
import OAI.Geometry.RCD.Sobolev.ContinuousSobolevPairingBound

namespace OAI

/-! # Pointwise time bounds on the good time slices

Full support transfers the quantitative compact-test estimate to every
point of the interior spatial ball. No pointwise bound on the viscous
Laplacians is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_limit_pointwise_time_bound (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hcont : ∀ t ∈ Ioo δ 1, t ∉ N → ContinuousOn (G t) (closedBall z r))
    (hconv : ∀ t ∈ Ioo δ 1, t ∉ N → TendstoUniformly
      (fun k (x : closedBall z r) => hX.fixedGaugeScaledPotential hn p ν
        (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x) (fun x => G t x) atTop) :
    ∃ C : ℝ≥0, ∀ s ∈ Ioo δ 1, s ∉ N → ∀ t ∈ Ioo δ 1, t ∉ N →
      ∀ x ∈ ball z r, |G t x-G s x| ≤ C * |t-s| := by
  let μ := hausdorff n X
  let := hX.openPos K n
  obtain ⟨C,hC,hpair⟩ := hX.scaled_heat_limit_pairing_time_bound hn p hK ν ρ hρ hρ0 hB hν
    F hF ε hε hε1 hε0 z hR hdist G ι hι N hr hδ hconv
  refine ⟨⟨C,hC⟩,?_⟩
  intro s hs hsN t ht htN
  apply continuous_abs_sub_le_of_sobolev_pairings μ hX.quadratic isOpen_ball
    (isCompact_closedBall z r) ball_subset_closedBall (G t) (G s)
    (hcont t ht htN) (hcont s hs hsN) (C*|t-s|)
  intro φ hφs hφb
  have hh := hpair φ hφs 1 hφb s hs hsN t ht htN
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
