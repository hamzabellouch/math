import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential
import OAI.Geometry.RCD.Heat.ScaledCompactSpacetimeBound

namespace OAI

/-! # Uniform local bounds for the fixed-gauge heat family -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem fixed_gauge_local_bounds (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    ∃ L A : ℝ≥0, ∀ (F : C(S,ℝ)), (∀ a, 0 < F a) →
      ∀ ε (hε : 0 < ε), ε ≤ 1 → ∀ t ∈ Icc δ 1,
        LipschitzOnWith L (hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t)
          (closedBall z r) ∧
        ∀ x ∈ closedBall z r, |hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x| ≤ A := by
  obtain ⟨C,D,_hC,_hD,hLip⟩ := hX.compact_heat_factor_scaled_lipschitz hn p
  obtain ⟨M,hM,hBound⟩ := hX.scaled_compact_heat_spacetime_bounded hn p hK
    ν ρ hρ hρ0 hB hν z R hR hdist hδ hr
  let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| *(4*C/δ+16*D*(R+8*(r+1))^2/δ^2)),Real.sqrt_nonneg _⟩
  refine ⟨L,⟨M,hM⟩,?_⟩
  intro F hF ε hε hε1 t ht
  constructor
  · have hl := hLip ν ρ hρ hρ0 hB hν F hF hε hε1 hδ ht.1 ht.2
      z R hR hdist (r := r+1) (by linarith)
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hX.fixedGaugeScaledPotential_eq hn p ν F ε hε δ hδ z ht.1 x,
      hX.fixedGaugeScaledPotential_eq hn p ν F ε hε δ hδ z ht.1 y,dist_sub_right]
    exact hl.dist_le_mul x (mem_ball.mpr (by linarith [mem_closedBall.mp hx]))
      y (mem_ball.mpr (by linarith [mem_closedBall.mp hy]))
  · intro x hx
    rw [hX.fixedGaugeScaledPotential_eq hn p ν F ε hε δ hδ z ht.1 x]
    exact hBound F hF hε hε1 ht.1 ht.2 x hx

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
