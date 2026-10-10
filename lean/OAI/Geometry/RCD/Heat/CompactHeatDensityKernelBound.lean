import OAI.Geometry.RCD.Heat.CompactHeatScalingDensity
import OAI.Geometry.RCD.Heat.ScalingKernelProductBound

namespace OAI

/-! # Kernel bridge bounds for the actual interpolation density -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationDensity_kernel_bound (k : ℕ) (t : Ioo (0:ℝ) 1) (x : X) {C : ℝ}
    (hbound : ∀ (a : S) (b : T),
      hX.canonicalHeatKernel hn p (ε k/4*t) x a *
        hX.canonicalHeatKernel hn p (ε k/4*(1-t)) x b ≤
          C*hX.canonicalHeatKernel hn p (ε k/4) a b) :
    D.interpolationDensity k t x ≤ C := by
  change (∫ a : S, hX.canonicalHeatKernel hn p (ε k/4*t) x a*D.left k a ∂μ)*
    (∫ b : T, hX.canonicalHeatKernel hn p (ε k/4*(1-t)) x b*D.right k b ∂ν) ≤ C
  have hc : 0 < ε k/4 := div_pos (hε k) (by norm_num)
  have hs := mul_pos hc t.property.1
  have ht := mul_pos hc (sub_pos.mpr t.property.2)
  let inc : S × T → X × X := fun q => (q.1.val,q.2.val)
  have hi : Continuous inc := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)
  let ker : C(S × T,ℝ) := ⟨(fun q : X × X => hX.canonicalHeatKernel hn p (ε k/4) q.1 q.2) ∘ inc,
    (hX.canonicalHeatKernel_continuous_joint hn p (ε k/4) hc).comp hi⟩
  let left : C(S,ℝ) := ⟨fun a => hX.canonicalHeatKernel hn p (ε k/4*t) x a,
    (hX.canonicalHeatKernel_continuous_right hn p (ε k/4*t) hs x).comp continuous_subtype_val⟩
  let right : C(T,ℝ) := ⟨fun b => hX.canonicalHeatKernel hn p (ε k/4*(1-t)) x b,
    (hX.canonicalHeatKernel_continuous_right hn p (ε k/4*(1-t)) ht x).comp continuous_subtype_val⟩
  have hrow : ∀ a : S, D.left k a*(∫ b, ker (a,b)*D.right k b ∂ν)=1 := D.row k
  have hratio : ∀ (a : S) (b : T), left a*right b ≤ C*ker (a,b) := hbound
  exact scaling_kernel_product_bound μ ν ker (D.left k) (D.right k)
    (fun a => (D.left_pos k a).le) (fun b => (D.right_pos k b).le) hrow left right hratio

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
