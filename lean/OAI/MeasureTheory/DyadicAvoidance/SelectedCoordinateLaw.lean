import Mathlib

namespace OAI

universe u_I u_K u_B

open MeasureTheory ProbabilityTheory

namespace Problem310.SelectedCoordinateLaw

/-- Reading any injective family of coordinates of an iid finite table is
measure preserving onto the corresponding smaller product table. -/
theorem measurePreserving_injective_coordinates
    {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype I] [Fintype K] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr) :
    MeasurePreserving (fun ω : K → B => fun i => ω (addr i))
      (Measure.pi (fun _ : K => ν)) (Measure.pi (fun _ : I => ν)) := by
  have hind : iIndepFun (fun k (ω : K → B) => ω k)
      (Measure.pi (fun _ : K => ν)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨Measurable.of_eval (fun i => measurable_pi_apply (addr i)), ?_⟩
  have h := (hind.precomp hinj).map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (addr i)).aemeasurable)
  rw [h]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : K => ν) (addr i)).map_eq

end Problem310.SelectedCoordinateLaw

end OAI
