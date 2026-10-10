import OAI.Geometry.RCD.Heat.KernelHeatLogarithmicEquation
import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # The local logarithmic equation for constructed endpoint factors -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_log_equation {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ C)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {t : ℝ} (ht : 0 < t)
    {Ω : Set X} (hΩ : IsCompact Ω) :
    ∃ (u v : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
      (hX.compactHeatFactor hn p ν F t ht =ᵐ[hausdorff n X]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u) ∧
      IsWeakLaplacian (hausdorff n X) hX.quadratic v q ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[(hausdorff n X).restrict Ω]
        fun x => Real.log (hX.compactHeatFactor hn p ν F t ht x)) ∧
      (∀ᵐ x ∂(hausdorff n X).restrict Ω,
        HasDerivAt (fun s => Real.log (∫ a, hX.canonicalHeatKernel hn p s x a*F a ∂ν))
          (q x + localGamma (hausdorff n X) hX.quadratic v v x) t) ∧
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
        localGamma (hausdorff n X) hX.quadratic v w =ᵐ[(hausdorff n X).restrict Ω]
          fun x => localGamma (hausdorff n X) hX.quadratic u w x /
            hX.compactHeatFactor hn p ν F t ht x := by
  obtain ⟨f,hf,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hC hν F
  obtain ⟨D,hD⟩ := hf
  have hfun : hX.compactHeatFactor hn p ν F t ht =
      kernelHeat (hausdorff n X) hX.quadratic
        (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f := funext (he t ht)
  obtain ⟨u,v,q,hu,hq,hv,hd,hmix⟩ := hX.kernelHeat_logarithmic_equation hn p
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f D hD ht hΩ
    (fun x _ => by rw [← hfun]; exact hX.compactHeatFactor_positive hn p ν F hF t ht x)
  refine ⟨u,v,q,hfun ▸ hu,hq,?_,?_,?_⟩
  · simpa only [hfun] using hv
  · filter_upwards [hd] with x hx
    apply hx.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact congrArg Real.log (he s hs x)
  · intro w
    simpa only [hfun] using hmix w

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
