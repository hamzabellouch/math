import OAI.Geometry.RCD.Heat.CompactHeatFactors
import OAI.Geometry.RCD.Heat.ContinuousKernelBridge

namespace OAI

/-! # The actual intermediate heat-bridge law has mass one -/

open Set Filter MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_bridge_probability {S T : Set X} [CompactSpace S] [CompactSpace T]
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : C(S, ℝ)) (G : C(T, ℝ)) (hF : ∀ a, 0 ≤ F a) (hG : ∀ b, 0 ≤ G b)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hrow : ∀ a, F a*(∫ b, hX.canonicalHeatKernel hn p (s+t) a b*G b ∂ν)=1) :
    IsProbabilityMeasure ((hausdorff n X).withDensity
      (fun x => ENNReal.ofReal
        (hX.compactHeatFactor hn p μ F s hs x * hX.compactHeatFactor hn p ν G t ht x))) := by
  let L := hX.compactHeatFactorKernel hn p S s hs
  let R := hX.compactHeatFactorKernel hn p T t ht
  let inc : S × T → X × X := fun z => (z.1.val,z.2.val)
  have hi : Continuous inc :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hk := hX.canonicalHeatKernel_continuous_joint hn p (s+t) (add_pos hs ht)
  let kernel : C(S × T, ℝ) :=
    ⟨(fun z : X × X => hX.canonicalHeatKernel hn p (s+t) z.1 z.2) ∘ inc,hk.comp hi⟩
  have hint (a : S) (b : T) : Integrable (fun x => L (x,a)*R (x,b)) (hausdorff n X) := by
    convert hX.canonicalHeatKernel_product_integrable hn p s t hs ht a b using 1
    funext x
    change hX.canonicalHeatKernel hn p s x a * hX.canonicalHeatKernel hn p t x b =
      hX.canonicalHeatKernel hn p s a x * hX.canonicalHeatKernel hn p t x b
    rw [hX.canonicalHeatKernel_symmetric hn p s x a]
  have hc (a : S) (b : T) : (∫ x, L (x,a)*R (x,b) ∂hausdorff n X)=kernel (a,b) := by
    calc
      _ = ∫ x, hX.canonicalHeatKernel hn p s a x * hX.canonicalHeatKernel hn p t x b
          ∂hausdorff n X := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change hX.canonicalHeatKernel hn p s x a * hX.canonicalHeatKernel hn p t x b = _
          rw [hX.canonicalHeatKernel_symmetric hn p s x a]
      _ = _ := hX.canonicalHeatKernel_convolution hn p s t hs ht a b
  exact continuous_kernel_bridge_probability μ ν (hausdorff n X) L R kernel F G
    (fun x a => hX.canonicalHeatKernel_nonneg hn p s x a)
    (fun x b => hX.canonicalHeatKernel_nonneg hn p t x b) hF hG hint hc hrow

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
