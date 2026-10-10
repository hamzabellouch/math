import OAI.Geometry.RCD.Heat.ScaledHeatTransportLimit
import OAI.Geometry.RCD.Heat.AlmostMonotoneAllTimes

namespace OAI

/-! # Every interior time of the actual small-noise heat limit

The one-sided time error tends to zero along the original subsequence.
Thus the continuous limit removes the exceptional times from convergence,
as well as from the transport comparison.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_uniform_all_times (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) (z : X)
    (H : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ) (hN : N.Countable)
    (hlocal : ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ →
      ∃ L : ℝ≥0, LipschitzOnWith L (Function.uncurry H) (Ioo δ 1 ×ˢ closedBall z r))
    (hlim : ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
      ∀ t ∈ Ioo δ 1, t ∉ N →
        TendstoUniformly (fun k (x : closedBall z r) =>
          hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
          (fun x => H t x) atTop)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Ioo δ 1) :
    TendstoUniformly (fun k (x : closedBall z r) =>
      hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
      (fun x => H t x) atTop := by
  obtain ⟨L,hL⟩ := hlocal (r+1) (by linarith) δ hδ
  let e := fun k => ε (ι k)*((n:ℝ)/δ+(n:ℝ)*|K|/2)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_mul,e,Function.comp_def] using (hε0.comp hι.tendsto_atTop).mul_const
      ((n:ℝ)/δ+(n:ℝ)*|K|/2)
  apply almost_monotone_uniform_all_times N hN _ (fun s (x : closedBall z r) => H s x)
    e he L L.coe_nonneg _ _ (hlim r hr δ hδ) ht
  · intro s hs u hu x
    have hx : (x : X) ∈ closedBall z (r+1) :=
      mem_closedBall.mpr (by linarith [mem_closedBall.mp x.property])
    have hh := hL.dist_le_mul (s,(x : X)) ⟨hs,hx⟩ (u,(x : X)) ⟨hu,hx⟩
    simpa only [Function.uncurry_apply_pair,Prod.dist_eq,dist_self,
      Real.dist_eq,max_eq_left (abs_nonneg (s-u))] using hh
  · intro k s u hs hsu _hu x
    rw [hX.fixedGaugeScaledPotential_eq hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z hs x,
      hX.fixedGaugeScaledPotential_eq hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z
        (hs.trans hsu) x]
    have hh := hX.scaled_compact_heat_potential_interior_time_lower hn p hK
      ν ρ hρ hρ0 hB hν (F (ι k)) (hF (ι k)) (hε (ι k)) (hε1 (ι k)) hδ hs hsu x
    dsimp only [e]
    linarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
