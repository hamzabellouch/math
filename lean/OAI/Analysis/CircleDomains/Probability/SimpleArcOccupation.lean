import OAI.Analysis.CircleDomains.Modulus.PathHausdorffLength
import Mathlib.MeasureTheory.Measure.Comap

namespace OAI

/-! Exact arclength occupation of an injective continuous path. This
identifies weighted path cost with the Hausdorff integral on its image. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem arc_variation_eq_hausdorff_interval
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : C(PathTime, X)) {a b : PathTime} (hab : a ≤ b)
    (hinj : InjOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) = (μH[1] : Measure X) (γ '' Icc a b) := by
  apply le_antisymm
  · exact simple_arc_variation_le_length γ ordConnected_Icc γ.continuous.continuousOn hinj
  · have h := path_hausdorff_length_le_variation (γ.comp (timeClip a b))
    rw [variation_timeClip γ hab] at h
    convert h using 1
    congr 1
    rw [ContinuousMap.coe_comp, range_comp, range_timeClip hab]

theorem simple_arc_length_measure
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) (hinj : Injective γ.val) :
    pathLengthMeasure γ = (μH[1] : Measure X).comap γ.val := by
  have he : MeasurableEmbedding γ.val := γ.val.continuous.isClosedEmbedding hinj |>.measurableEmbedding
  apply Measure.ext_of_Icc
  intro a b hab
  rw [pathLengthMeasure_Icc γ hab, he.comap_apply]
  exact arc_variation_eq_hausdorff_interval γ.val hab hinj.injOn

theorem simple_arc_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) (hinj : Injective γ.val) :
    pathOccupation γ = (μH[1] : Measure X).restrict (range γ.val) := by
  have he : MeasurableEmbedding γ.val := γ.val.continuous.isClosedEmbedding hinj |>.measurableEmbedding
  rw [pathOccupation, simple_arc_length_measure γ hinj]
  exact he.map_comap _

theorem simple_arc_weighted_cost
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) (hinj : Injective γ.val) (g : X → ℝ≥0∞) :
    (∫⁻x, g x ∂pathOccupation γ) = ∫⁻x in range γ.val, g x ∂(μH[1] : Measure X) := by
  rw [simple_arc_occupation γ hinj]

theorem simple_arc_rectifiable_of_finite_length
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : C(PathTime, X)) (hinj : Injective γ)
    (hlen : (μH[1] : Measure X) (range γ) < ∞) : BoundedVariationOn γ univ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (simple_arc_variation_le_length γ ordConnected_univ
    γ.continuous.continuousOn hinj.injOn)
  simpa only [image_univ] using hlen

end CircleDomainRigidity

end

end OAI
