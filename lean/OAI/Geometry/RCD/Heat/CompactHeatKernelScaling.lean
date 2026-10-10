import OAI.Geometry.RCD.Heat.PositiveKernelScaling
import OAI.Geometry.RCD.Heat.CanonicalStrictPositivity

namespace OAI

/-! # Actual positive-time heat kernel scaling on compact supports

The endpoint laws here are probability measures on the compact supports.
They may be the laws with bounded densities used in the entropic
approximation. The kernel is the constructed RCD heat kernel.
-/

open Set MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_kernel_scaling {S T : Set X} (hS : IsCompact S) (hT : IsCompact T)
    (hS0 : S.Nonempty) (hT0 : T.Nonempty) (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) (ht : 0 < t) :
    ∃ (F : C(S, ℝ)) (G : C(T, ℝ)),
      (∀ x, 0 < F x) ∧ (∀ y, 0 < G y) ∧
      (∀ x, F x*(∫ y, hX.canonicalHeatKernel hn p t x y*G y ∂ν)=1) ∧
      (∀ y, G y*(∫ x, hX.canonicalHeatKernel hn p t x y*F x ∂μ)=1) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let inc : S × T → X × X := fun z => (z.1.val,z.2.val)
  have hi : Continuous inc :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hk := hX.canonicalHeatKernel_continuous_joint hn p t ht
  let kernel : C(S × T, ℝ) :=
    ⟨(fun z : X × X => hX.canonicalHeatKernel hn p t z.1 z.2) ∘ inc,hk.comp hi⟩
  obtain ⟨x₀,hx₀⟩ := hS0
  obtain ⟨y₀,hy₀⟩ := hT0
  exact continuous_positive_kernel_scaling μ ν kernel
    (fun x y => hX.canonicalHeatKernel_pos hn p t ht x y) ⟨x₀,hx₀⟩ ⟨y₀,hy₀⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
