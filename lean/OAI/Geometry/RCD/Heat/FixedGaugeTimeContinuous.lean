import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential
import OAI.Geometry.RCD.Heat.ScaledHeatTimePairing

namespace OAI

/-! # Joint continuity of the fixed-gauge heat potential -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem fixedGaugeScaledPotential_continuous
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S,ℝ)) (hF : ∀ a, 0 < F a) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z : X) :
    Continuous (Function.uncurry (hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z)) := by
  obtain ⟨_D,hH,_hD,_hd⟩ := hX.compact_heat_scaled_time_data hn p
    ν ρ hρ hρ0 hB hν F hF hε
  let T := fun q : ℝ × X => (max δ q.1,q.2)
  have hT : Continuous T := (continuous_const.max continuous_fst).prodMk continuous_snd
  have hc : Continuous (fun q : ℝ × X => ε * Real.log
      (∫ a, hX.canonicalHeatKernel hn p (ε*(max δ q.1)/2) q.2 a * F a ∂ν)) := by
    apply continuousOn_univ.mp
    exact hH.comp hT.continuousOn (fun q _ =>
      ⟨hδ.trans_le (le_max_left δ q.1),mem_univ _⟩)
  have hh := hc.sub (continuous_const : Continuous (fun _ : ℝ × X =>
    ε * Real.log (hX.compactHeatFactor hn p ν F ε hε z)))
  exact hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
