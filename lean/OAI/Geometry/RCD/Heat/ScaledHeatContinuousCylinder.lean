import OAI.Geometry.RCD.Heat.ScaledHeatLimitPointwiseTime
import OAI.Geometry.RCD.Sobolev.RemoveExceptionalTimes

namespace OAI

/-! # Continuous local cylinders for the prescribed small-noise heat limit

The same good-time limit extends through its exceptional times. Both the
time and space Lipschitz constants are uniform on each interior cylinder.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_continuous_cylinder_of_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ) (hN : N.Countable)
    (hdata : ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
      ∃ (L : ℝ≥0) (M : ℝ), 0 ≤ M ∧ ∀ t, t ∈ Ioo δ 1 → t ∉ N →
        LipschitzOnWith L (G t) (closedBall z r) ∧
        (∀ x ∈ closedBall z r, |G t x| ≤ M) ∧
        TendstoUniformly (fun k (x : closedBall z r) =>
          hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
          (fun x => G t x) atTop)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ (U : ℝ → closedBall z r → ℝ) (C L : ℝ≥0),
      (∀ x, LipschitzWith C (fun t => U t x)) ∧
      (∀ t ∈ Ioo δ 1, LipschitzWith L (U t)) ∧
      (∀ t ∈ Ioo δ 1, t ∉ N → ∀ x, U t x = G t x) ∧
      LipschitzOnWith (C+L) (Function.uncurry U) (Ioo δ 1 ×ˢ univ) := by
  obtain ⟨L,M,_hM,hgood⟩ := hdata (2*r) (by positivity) δ hδ
  obtain ⟨C,hC⟩ := hX.scaled_heat_limit_pointwise_time_bound hn p hK ν ρ hρ hρ0 hB hν
    F hF ε hε hε1 hε0 z hR hdist G ι hι N (by positivity : 0 ≤ 2*r) hδ
    (fun t ht htN => (hgood t ht htN).1.continuousOn)
    (fun t ht htN => (hgood t ht htN).2.2)
  have htime (x : closedBall z r) :
      LipschitzOnWith C (fun t => G t x) (Ioo δ 1 \ N) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have hx : (x:X) ∈ ball z (2*r) := by
      have hh := mem_closedBall.mp x.property
      apply mem_ball.mpr
      linarith
    simpa only [Real.dist_eq] using hC t ht.1 ht.2 s hs.1 hs.2 x hx
  have hspace (t : ℝ) (ht : t ∈ Ioo δ 1) (htN : t ∉ N) :
      LipschitzWith L (fun x : closedBall z r => G t x) := by
    intro x y
    apply (hgood t ht htN).1
    · exact closedBall_subset_closedBall (by linarith) x.property
    · exact closedBall_subset_closedBall (by linarith) y.property
  obtain ⟨U,hU⟩ := remove_countable_times N hN (fun t (x : closedBall z r) => G t x) C L htime hspace
  exact ⟨U,C,L,hU⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
