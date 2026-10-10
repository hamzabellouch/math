import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.FiniteKernelMixture

variable {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def weightedKernel (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) : Kernel X Y where
  toFun x := ∑ i, w i x • κ i x
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun i _ => (hw i).mul (Kernel.measurable_coe (κ i) hs))

noncomputable def normalizedKernel (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) : Kernel X Y :=
  weightedKernel κ (fun i x => w i x / ∑ j, w j x)
    (fun i => (hw i).div (Finset.measurable_sum _ (fun j _ => hw j)))

noncomputable def diagonalReplacementKernel (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) : Kernel X X :=
  normalizedKernel
    (fun o : Option I => match o with
      | none => Kernel.id
      | some i => Kernel.const X (ν i))
    (fun o x => match o with
      | none => q
      | some i => p i * u i x)
    (fun o => by cases o with
      | none => exact measurable_const
      | some i => exact measurable_const.mul (hu i))

end Invariant233.FiniteKernelMixture

end OAI
