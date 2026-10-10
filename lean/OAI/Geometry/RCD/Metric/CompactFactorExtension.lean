import OAI.Geometry.RCD.Heat.CompactKernelFactor
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

namespace OAI

/-! # Zero extension of continuous weights on compact endpoint supports

The extension is bounded and measurable and belongs to L² for locally
finite measures. Continuity across the support boundary is not needed.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def compactFactorExtension {S : Set X} (F : C(S, ℝ)) : X → ℝ :=
  Function.extend Subtype.val F (fun _ => 0)

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem compactFactorExtension_coe {S : Set X} (F : C(S, ℝ)) (x : S) :
    compactFactorExtension F x=F x := Subtype.val_injective.extend_apply _ _ x

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactFactorExtension_off {S : Set X} (F : C(S, ℝ)) {x : X} (hx : x ∉ S) :
    compactFactorExtension F x=0 := by
  apply Function.extend_apply'
  rintro ⟨y,hy⟩
  exact hx (hy ▸ y.property)

theorem compactFactorExtension_measurable {S : Set X} (hS : MeasurableSet S) (F : C(S, ℝ)) :
    Measurable (compactFactorExtension F) :=
  (MeasurableEmbedding.subtype_coe hS).measurable_extend F.continuous.measurable measurable_const

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactFactorExtension_bounded {S : Set X} (hS : IsCompact S) (F : C(S, ℝ)) :
    ∃ C : ℝ≥0, ∀ x, |compactFactorExtension F x| ≤ C := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  refine ⟨‖F‖₊,fun x => ?_⟩
  by_cases hx : x ∈ S
  · have he := compactFactorExtension_coe F ⟨x,hx⟩
    rw [he]
    exact F.norm_coe_le_norm ⟨x,hx⟩
  · rw [compactFactorExtension_off F hx,abs_zero]
    exact NNReal.coe_nonneg _

theorem compactFactorExtension_memLp {S : Set X} (hS : IsCompact S) (F : C(S, ℝ))
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] : MemLp (compactFactorExtension F) 2 μ := by
  have hm := compactFactorExtension_measurable hS.isClosed.measurableSet F
  obtain ⟨C,hC⟩ := compactFactorExtension_bounded hS F
  have he : S.indicator (compactFactorExtension F) = compactFactorExtension F := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx,compactFactorExtension_off F hx]
  rw [← he,memLp_indicator_iff_restrict hS.isClosed.measurableSet]
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  exact MemLp.of_bound hm.aestronglyMeasurable (C : ℝ)
    (Eventually.of_forall fun x => hC x)

end RegularPointCoordinates

end

end OAI
