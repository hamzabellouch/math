import OAI.Geometry.RCD.Transport.SubplanReduced
import OAI.Geometry.RCD.Transport.ReducedChordScaling

namespace OAI

/-! # The exact reduced bound at the original subplan mass -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem subplan_reduced (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (κ : Measure C(Time,X)) (hk : κ ≤ π) (hk0 : κ univ ≠ 0) :
    ∀ t, ReducedRenyiChordBound (hausdorff n X) K N κ t := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hk
  have hN1 : 1 < N := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  intro t
  apply reduced_chord_of_smul (hausdorff n X) κ
    (ENNReal.inv_ne_zero.mpr (measure_ne_top κ univ))
    (ENNReal.inv_ne_top.mpr hk0) _ _ hN1 t
    (hX.normalized_subplan_reduced hn hK hN a π hg hp hC hc κ hk hk0 t)
  · exact (Measure.map_mono hk (measurable_path_eval 0)).absolutelyContinuous.trans
      (Measure.absolutelyContinuous_of_le_smul (hc 0))
  · exact (Measure.map_mono hk (measurable_path_eval 1)).absolutelyContinuous.trans
      (Measure.absolutelyContinuous_of_le_smul (hc 1))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
