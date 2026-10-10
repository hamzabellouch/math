import OAI.Geometry.RCD.Heat.CompactHeatBridge
import OAI.Geometry.RCD.Heat.CompactHeatKernelScaling

namespace OAI

/-! # One scaling pair gives every interior heat-bridge law

The endpoint factors are selected once before the interpolation time.
Every interior law is a probability with a positive continuous density.
No optimal-transport limit or second-variation formula is assumed here.
-/

open Set MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_interpolation {S T : Set X} [CompactSpace S] [CompactSpace T]
    (hS0 : S.Nonempty) (hT0 : T.Nonempty) (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (τ : ℝ) (hτ : 0 < τ) :
    ∃ (F : C(S, ℝ)) (G : C(T, ℝ)),
      (∀ a, 0 < F a) ∧ (∀ b, 0 < G b) ∧
      (∀ a, F a*(∫ b, hX.canonicalHeatKernel hn p τ a b*G b ∂ν)=1) ∧
      (∀ b, G b*(∫ a, hX.canonicalHeatKernel hn p τ a b*F a ∂μ)=1) ∧
      ∀ (s : ℝ) (hs : 0 < s) (hst : s < τ),
        IsProbabilityMeasure ((hausdorff n X).withDensity
          (fun x => ENNReal.ofReal (hX.compactHeatFactor hn p μ F s hs x *
            hX.compactHeatFactor hn p ν G (τ-s) (sub_pos.mpr hst) x))) ∧
        ∀ x, 0 < hX.compactHeatFactor hn p μ F s hs x *
          hX.compactHeatFactor hn p ν G (τ-s) (sub_pos.mpr hst) x := by
  obtain ⟨F,G,hF,hG,hr,hc⟩ := hX.compact_heat_kernel_scaling hn p
    (isCompact_iff_compactSpace.mpr inferInstance) (isCompact_iff_compactSpace.mpr inferInstance)
    hS0 hT0 μ ν τ hτ
  refine ⟨F,G,hF,hG,hr,hc,?_⟩
  intro s hs hst
  constructor
  · apply hX.compact_heat_bridge_probability hn p μ ν F G
      (fun a => (hF a).le) (fun b => (hG b).le) s (τ-s) hs (sub_pos.mpr hst)
    simpa only [add_sub_cancel] using hr
  · intro x
    exact mul_pos (hX.compactHeatFactor_positive hn p μ F hF s hs x)
      (hX.compactHeatFactor_positive hn p ν G hG (τ-s) (sub_pos.mpr hst) x)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
