import OAI.Geometry.RCD.Metric.ScaledCompactPotentialMeasurable

namespace OAI

/-! # One measurable reference-time gauge for the actual scaled potential -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

def fixedGaugeScaledPotential {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (F : C(S, ℝ))
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (z : X) (t : ℝ) (x : X) : ℝ :=
  hX.scaledCompactHeatPotential hn p ν F ε (max δ t)
    (div_pos (mul_pos hε (hδ.trans_le (le_max_left δ t))) (by norm_num)) x -
  ε * Real.log (hX.compactHeatFactor hn p ν F ε hε z)

theorem fixedGaugeScaledPotential_eq {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (F : C(S, ℝ))
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (z : X) {t : ℝ} (ht : δ ≤ t) (x : X) :
    hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x =
      hX.scaledCompactHeatPotential hn p ν F ε t
        (div_pos (mul_pos hε (hδ.trans_le ht)) (by norm_num)) x -
      ε * Real.log (hX.compactHeatFactor hn p ν F ε hε z) := by
  simp only [fixedGaugeScaledPotential,max_eq_right ht]

theorem fixedGaugeScaledPotential_measurable
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z : X) :
    Measurable (Function.uncurry (hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z)) :=
  (hX.scaled_compact_heat_potential_measurable hn p ν ρ hρ hρ0 hB hν F hF hε hδ).sub measurable_const

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
