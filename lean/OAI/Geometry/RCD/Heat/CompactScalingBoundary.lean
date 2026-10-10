import OAI.Geometry.RCD.Heat.CompactHeatKernelScaling
import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential

namespace OAI

/-! # Exact logarithmic boundary identities for compact heat scaling

These identities use the actual normalization equations of the positive
kernel scaling pair. The reference-time gauge cancels in differences.
-/

open Set MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_scaling_log_boundary {S T : Set X} [CompactSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν] (F : S → ℝ) (G : C(T, ℝ))
    (hF : ∀ a, 0 < F a) (hG : ∀ b, 0 < G b) {τ : ℝ} (hτ : 0 < τ)
    (hr : ∀ a, F a*(∫ b, hX.canonicalHeatKernel hn p τ a b*G b ∂ν)=1) (a : S) :
    Real.log (F a) = -Real.log (hX.compactHeatFactor hn p ν G τ hτ a) := by
  have hm : F a * hX.compactHeatFactor hn p ν G τ hτ a = 1 := hr a
  have hh := congrArg Real.log hm
  rw [Real.log_mul (hF a).ne' (hX.compactHeatFactor_positive hn p ν G hG τ hτ a).ne',
    Real.log_one] at hh
  linarith

theorem compact_scaling_centered_boundary {S T : Set X} [CompactSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν] (F : S → ℝ) (G : C(T, ℝ))
    (hF : ∀ a, 0 < F a) (hG : ∀ b, 0 < G b)
    {ε δ t : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (ht : δ ≤ t)
    (hr : ∀ a, F a*(∫ b, hX.canonicalHeatKernel hn p (ε*t/2) a b*G b ∂ν)=1)
    (z : X) (a b : S) :
    ε*(Real.log (F a)-Real.log (F b)) =
      hX.fixedGaugeScaledPotential hn p ν G ε hε δ hδ z t b -
      hX.fixedGaugeScaledPotential hn p ν G ε hε δ hδ z t a := by
  have hτ : 0 < ε*t/2 := div_pos (mul_pos hε (hδ.trans_le ht)) (by norm_num)
  rw [hX.compact_scaling_log_boundary hn p ν F G hF hG hτ hr a,
    hX.compact_scaling_log_boundary hn p ν F G hF hG hτ hr b,
    hX.fixedGaugeScaledPotential_eq hn p ν G ε hε δ hδ z ht b,
    hX.fixedGaugeScaledPotential_eq hn p ν G ε hε δ hδ z ht a]
  simp only [scaledCompactHeatPotential]
  ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
