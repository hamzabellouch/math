import OAI.Geometry.RCD.Heat.HeatPairMeasure
import Mathlib.Probability.Kernel.Composition.WithDensity

namespace OAI

/-! # Almost-everywhere symmetry of the jointly measurable heat density -/

open Set Filter MeasureTheory Metric TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal Topology ProbabilityTheory

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatJointDensity_withDensity (t : ℝ) (ht : 0 < t) (x : X) :
    (hausdorff n X).withDensity (fun y => ENNReal.ofReal (hX.heatJointDensity hn p t ht x y)) =
      hX.heatRadonMeasure hn p t ht x := by
  let μ := hausdorff n X
  let ν := hX.heatRadonMeasure hn p t ht x
  calc
    _ = μ.withDensity (ν.rnDeriv μ) := by
      apply withDensity_congr_ae
      filter_upwards [hX.heatJointDensity_ae hn p t ht x, Measure.rnDeriv_ne_top ν μ] with y hy hfin
      rw [hy]
      exact ENNReal.ofReal_toReal hfin
    _ = ν := Measure.withDensity_rnDeriv_eq _ _ (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x)

theorem heatPairMeasure_withDensity (t : ℝ) (ht : 0 < t) :
    hX.heatPairMeasure hn p t ht =
      ((hausdorff n X).prod (hausdorff n X)).withDensity
        (fun xy => ENNReal.ofReal (hX.heatJointDensity hn p t ht xy.1 xy.2)) := by
  let μ := hausdorff n X
  let κ := Kernel.const X μ
  let f (x y : X) := ENNReal.ofReal (hX.heatJointDensity hn p t ht x y)
  have hf : Measurable (Function.uncurry f) :=
    (hX.heatJointDensity_measurable hn p t ht).ennreal_ofReal
  have he : κ.withDensity f = hX.heatMarkovKernel hn p t ht := by
    apply Kernel.ext
    intro x
    rw [Kernel.withDensity_apply _ hf]
    exact hX.heatJointDensity_withDensity hn p t ht x
  let : IsSFiniteKernel (κ.withDensity f) := by rw [he]; infer_instance
  calc
    _ = μ ⊗ₘ κ.withDensity f := by rw [he]; rfl
    _ = (μ ⊗ₘ κ).withDensity (Function.uncurry f) := Measure.compProd_withDensity hf
    _ = _ := by rw [Measure.compProd_const]; rfl

/-- Self-adjointness gives genuine product-almost-everywhere symmetry
of the constructed density. -/
theorem heatJointDensity_symmetric_ae (t : ℝ) (ht : 0 < t) :
    ∀ᵐ xy ∂(hausdorff n X).prod (hausdorff n X),
      hX.heatJointDensity hn p t ht xy.1 xy.2 = hX.heatJointDensity hn p t ht xy.2 xy.1 := by
  let μ := hausdorff n X
  let m := μ.prod μ
  let f (xy : X × X) := ENNReal.ofReal (hX.heatJointDensity hn p t ht xy.1 xy.2)
  have hf : Measurable f := (hX.heatJointDensity_measurable hn p t ht).ennreal_ofReal
  have hswap : (m.withDensity f).map Prod.swap = m.withDensity (f ∘ Prod.swap) := by
    ext A hA
    rw [Measure.map_apply measurable_swap hA, withDensity_apply f (measurable_swap hA),
      withDensity_apply (f ∘ Prod.swap) hA]
    have H := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).setLIntegral_comp_preimage
      hA (hf.comp measurable_swap)
    simpa only [Function.comp_apply, Prod.swap_swap] using H
  have he : m.withDensity f = m.withDensity (f ∘ Prod.swap) := by
    rw [← hswap]
    have H := hX.heatPairMeasure_symm hn p t ht
    rw [hX.heatPairMeasure_withDensity hn p t ht] at H
    exact H
  have hae : f =ᵐ[m] f ∘ Prod.swap :=
    (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable (hf.comp measurable_swap).aemeasurable).mp he
  filter_upwards [hae] with xy hxy
  have H := congrArg ENNReal.toReal hxy
  change (ENNReal.ofReal (hX.heatJointDensity hn p t ht xy.1 xy.2)).toReal =
    (ENNReal.ofReal (hX.heatJointDensity hn p t ht xy.2 xy.1)).toReal at H
  simpa only [ENNReal.toReal_ofReal (hX.heatJointDensity_nonneg hn p t ht _ _)] using H

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
