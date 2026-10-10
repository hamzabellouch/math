import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.ProductMeasure

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_circleRepresentative :
    MeasurePreserving
      (fun x : UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 x) : ℝ))
      volume (volume.restrict (Ico (0 : ℝ) 1)) := by
  have hmk : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ico 0 (0 + 1))) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    exact AddCircle.measurePreserving_mk 1 0
  have hs := hmk.comp (measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (s := Ico 0 (0 + 1)) measurableSet_Ico)
  have he : MeasurePreserving (AddCircle.measurableEquivIco (1 : ℝ) 0).symm
      (Measure.comap Subtype.val (volume : Measure ℝ)) volume := hs
  have hi := MeasurePreserving.symm (AddCircle.measurableEquivIco (1 : ℝ) 0).symm he
  convert (measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (s := Ico 0 (0 + 1)) measurableSet_Ico).comp hi using 1
  · rfl
  · simp

theorem measurePreserving_productRepresentative {ι : Type*} (i : ι) :
    MeasurePreserving
      (fun x : ι → UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact measurePreserving_circleRepresentative.comp
    (measurePreserving_eval_infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)) i)

end Invariant233.CocycleSupport

end OAI
