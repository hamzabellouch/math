import OAI.Analysis.FiniteFactor.CrossedProduct.Cocycle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceCircleRepresentative (x : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco 1 0 x).val

theorem sourceCircleRepresentative_measurable : Measurable sourceCircleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

theorem sourceCircleRepresentative_coe (x : ℝ) :
    sourceCircleRepresentative (x : AddCircle (1 : ℝ)) = Int.fract x := by
  have hx : Int.fract x ∈ Set.Ico (0 : ℝ) (0+1) :=
    ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one x⟩
  have he := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0) hx
  rw [AddCircle.coe_fract] at he
  exact congrArg Subtype.val he

theorem sourceCircle_mk_preserving :
    MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ)) unitIntervalMeasure volume := by
  simpa [unitIntervalMeasure, restrict_Ico_eq_restrict_Ioc] using
    AddCircle.measurePreserving_mk 1 0

theorem sourceCircleRepresentative_preserving :
    MeasurePreserving sourceCircleRepresentative volume unitIntervalMeasure := by
  refine ⟨sourceCircleRepresentative_measurable, ?_⟩
  rw [← sourceCircle_mk_preserving.map_eq,
    Measure.map_map sourceCircleRepresentative_measurable sourceCircle_mk_preserving.measurable]
  have he : (sourceCircleRepresentative ∘ ((↑) : ℝ → AddCircle (1 : ℝ))) =ᵐ[unitIntervalMeasure] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [Function.comp_apply, sourceCircleRepresentative_coe]
    exact Int.fract_eq_self.mpr hx
  rw [Measure.map_congr he, Measure.map_id]

/-- Translation modulo one preserves the exact real representative measure. -/
theorem unitInterval_rotate_preserving (a : ℝ) :
    MeasurePreserving (fun x : ℝ => Int.fract (x+a)) unitIntervalMeasure unitIntervalMeasure := by
  have hh := sourceCircleRepresentative_preserving.comp
    ((measurePreserving_add_right (volume : Measure (AddCircle (1 : ℝ))) (a : AddCircle (1 : ℝ))).comp
      sourceCircle_mk_preserving)
  convert hh using 1
  funext x
  simpa only [Function.comp_apply, ← AddCircle.coe_add] using (sourceCircleRepresentative_coe (x+a)).symm

/-- All integer iterates of the countable source rotation preserve its actual
infinite product measure. This is not an assumed action property. -/
theorem coordinateRotate_preserving {ι : Type*} (θ : ι → ℝ) (k : ℤ) :
    MeasurePreserving (coordinateRotate θ k)
      (Measure.infinitePi (fun _ : ι => unitIntervalMeasure))
      (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) := by
  have hm (i : ι) : Measurable (fun x : ℝ => Int.fract (x+(k : ℝ)*θ i)) :=
    (unitInterval_rotate_preserving _).measurable
  refine ⟨Measurable.of_eval (fun i => (hm i).comp (measurable_pi_apply i)), ?_⟩
  unfold coordinateRotate
  rw [Measure.infinitePi_map_pi _ hm]
  simp_rw [(unitInterval_rotate_preserving _).map_eq]

end
end FiniteFactor

end OAI
