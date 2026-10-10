import OAI.Geometry.RCD.Heat.CompactHeatScalingData
import OAI.Geometry.RCD.Heat.CompactHeatBridge

namespace OAI

/-! # The actual probability densities of the compact scaling sequence -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}

namespace CompactHeatScalingData
variable (D : hX.CompactHeatScalingData hn p μ ν ε hε)

def interpolationDensity (k : ℕ) (t : Ioo (0 : ℝ) 1) : X → ℝ :=
  fun x =>
    hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t)
      (mul_pos (div_pos (hε k) (by norm_num)) t.property.1) x *
    hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t))
      (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)) x

theorem interpolationDensity_continuous (k : ℕ) (t : Ioo (0 : ℝ) 1) :
    Continuous (D.interpolationDensity k t) :=
  Continuous.mul (ContinuousMap.continuous _) (ContinuousMap.continuous _)

theorem interpolationDensity_pos (k : ℕ) (t : Ioo (0 : ℝ) 1) (x : X) :
    0 < D.interpolationDensity k t x :=
  mul_pos (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x)
    (hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x)

theorem interpolationDensity_probability (k : ℕ) (t : Ioo (0 : ℝ) 1) :
    IsProbabilityMeasure ((hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (D.interpolationDensity k t x))) := by
  apply hX.compact_heat_bridge_probability hn p μ ν (D.left k) (D.right k)
    (fun a => (D.left_pos k a).le) (fun b => (D.right_pos k b).le)
  intro a
  have he : ε k/4*(t:ℝ)+ε k/4*(1-t)=ε k/4 := by ring
  rw [he]
  exact D.row k a

end CompactHeatScalingData
end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
