import OAI.Geometry.RCD.Heat.CompactHeatReferenceMass
import OAI.Geometry.RCD.Heat.CenteredActionLower

namespace OAI

/-! # The actual uniform-law heat limit has zero reference trajectory -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem uniform_heat_action_center {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (hν : ν.map Subtype.val = uniformOn (hausdorff n X) S)
    (z : X) {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ S)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (H : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι)
    (hconv : hX.CompactHeatConverges hn p ν (fun _ => 1) ε hε z ι H)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : H t z = 0 := by
  have hδ : 0 < t/2 := by linarith [ht.1]
  have hti : t ∈ Ioo (t/2) 1 := ⟨by linarith [ht.1],ht.2⟩
  let a := fun k => ε (ι k)
  have ha : ∀ k, 0 < a k := fun k => hε (ι k)
  have ha0 : Tendsto a atTop (𝓝 0) := hε0.comp hι.tendsto_atTop
  have htime := hX.compact_heat_reference_scaled_log hn p ν hν z hr hball a ha ha0 hδ
  have href := hX.compact_heat_reference_scaled_log hn p ν hν z hr hball a ha ha0
    (by norm_num : (0:ℝ) < 1)
  have hz := (hconv 0 le_rfl (t/2) hδ t hti).tendsto_at ⟨z,mem_closedBall_self le_rfl⟩
  have hh : Tendsto (fun k => hX.fixedGaugeScaledPotential hn p ν 1 (a k) (ha k)
      (t/2) hδ z t z) atTop (𝓝 0) := by
    have he (k : ℕ) : hX.fixedGaugeScaledPotential hn p ν 1 (a k) (ha k) (t/2) hδ z t z =
        a k*Real.log (hX.compactHeatFactor hn p ν 1 (a k*(t/2)) (mul_pos (ha k) hδ) z) -
        a k*Real.log (hX.compactHeatFactor hn p ν 1 (a k*1) (mul_pos (ha k) zero_lt_one) z) := by
      rw [hX.fixedGaugeScaledPotential_eq hn p ν 1 (a k) (ha k) (t/2) hδ z hti.1.le z]
      simp only [scaledCompactHeatPotential,mul_one]
      simp only [show a k*t/2 = a k*(t/2) by ring]
    simpa only [sub_zero,he] using htime.sub href
  exact tendsto_nhds_unique hz hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
