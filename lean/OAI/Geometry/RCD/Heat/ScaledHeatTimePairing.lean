import OAI.Geometry.RCD.Heat.ScaledHeatLogTimeData
import OAI.Geometry.RCD.Heat.CompactTimePairing
import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # A continuous time derivative for the actual scaled heat factors

The derivative uses the actual L2 heat source, with no choice of
pointwise time null sets. Compact spatial pairings are treated by the
subsequent weak time equation.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_scaled_time_data
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {ε : ℝ} (hε : 0 < ε) :
    let H := fun t x => ε * Real.log
      (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a * F a ∂ν)
    ∃ D : ℝ → X → ℝ,
      ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ) ∧
      ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ) ∧
      ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => H s x) (D t x) t := by
  intro H
  let μ := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨f,_hf,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hB hν F
  have hp (t : ℝ) (ht : 0 < t) (x : X) : 0 < kernelHeat μ Q hk t f x := by
    rw [← he t ht x]
    exact hX.compactHeatFactor_positive hn p ν F hF t ht x
  let V := fun t x => ε * Real.log (kernelHeat μ Q hk (ε*t/2) f x)
  let D := fun t x => ε*(ε/2) *
    (kernelHeatGeneratorSource μ Q hk (ε*t/2) f x / kernelHeat μ Q hk (ε*t/2) f x)
  obtain ⟨hV,hD,hdV⟩ := scaled_positive_heat_log_time_data μ Q hk f hε hp
  have hval (t : ℝ) (ht : 0 < t) (x : X) : H t x = V t x := by
    dsimp only [H,V]
    rw [← he (ε*t/2) (div_pos (mul_pos hε ht) (by norm_num)) x]
    rfl
  have hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ) :=
    hV.congr (fun q hq => hval q.1 hq.1 q.2)
  have hd (t : ℝ) (ht : 0 < t) (x : X) : HasDerivAt (fun s => H s x) (D t x) t := by
    apply (hdV t ht x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hval s hs x
  exact ⟨D,hH,hD,hd⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
