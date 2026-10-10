import OAI.Geometry.RCD.Metric.CompactFactorCenteredCompactness
import OAI.Geometry.RCD.Metric.CompactFactorDerivative
import OAI.Geometry.RCD.Metric.MonotoneSpatialMeasurable

namespace OAI

/-! # Measurability of actual heat potentials on interior time cylinders

Clipping at a positive time margin gives a globally defined measurable
function and agrees with the original potential throughout the cylinder.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_compact_heat_potential_continuous_time
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (x : X) :
    Continuous (fun t => hX.scaledCompactHeatPotential hn p ν F ε (max δ t)
      (div_pos (mul_pos hε (hδ.trans_le (le_max_left δ t))) (by norm_num)) x) := by
  obtain ⟨_f,_hf,_he,hder⟩ := hX.compact_heat_factor_derivative hn p ν ρ hρ hρ0 hB hν F
  let H := fun t => ∫ a, hX.canonicalHeatKernel hn p t x a * F a ∂ν
  have hH : ContinuousOn H (Ioi 0) := fun t ht => (hder t ht x).continuousAt.continuousWithinAt
  let τ := fun t : ℝ => ε * max δ t / 2
  have hτ : Continuous τ := by dsimp only [τ]; fun_prop
  have hτ0 (t : ℝ) : 0 < τ t := div_pos (mul_pos hε (hδ.trans_le (le_max_left δ t))) (by norm_num)
  have hc : Continuous (fun t => H (τ t)) := hH.comp_continuous hτ hτ0
  have hp (t : ℝ) : 0 < H (τ t) := hX.compactHeatFactor_positive hn p ν F hF (τ t) (hτ0 t) x
  have hlog : Continuous (fun t => Real.log (H (τ t))) :=
    hc.log (fun t => (hp t).ne')
  exact continuous_const.mul hlog

theorem scaled_compact_heat_potential_continuous_space
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) (ε t : ℝ) (ht : 0 < ε*t/2) :
    Continuous (hX.scaledCompactHeatPotential hn p ν F ε t ht) := by
  change Continuous (fun x => ε * Real.log (hX.compactHeatFactor hn p ν F (ε*t/2) ht x))
  exact continuous_const.mul ((hX.compactHeatFactor hn p ν F (ε*t/2) ht).continuous.log
    (fun x => (hX.compactHeatFactor_positive hn p ν F hF _ _ x).ne'))

theorem scaled_compact_heat_potential_measurable
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Measurable (fun q : ℝ × X => hX.scaledCompactHeatPotential hn p ν F ε (max δ q.1)
      (div_pos (mul_pos hε (hδ.trans_le (le_max_left δ q.1))) (by norm_num)) q.2) := by
  exact continuous_sections_measurable
    (fun t x => hX.scaledCompactHeatPotential hn p ν F ε (max δ t)
      (div_pos (mul_pos hε (hδ.trans_le (le_max_left δ t))) (by norm_num)) x)
    (fun t => hX.scaled_compact_heat_potential_continuous_space hn p ν F hF ε (max δ t)
      (div_pos (mul_pos hε (hδ.trans_le (le_max_left δ t))) (by norm_num)))
    (fun x => hX.scaled_compact_heat_potential_continuous_time hn p ν ρ hρ hρ0 hB hν F hF hε hδ x)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
