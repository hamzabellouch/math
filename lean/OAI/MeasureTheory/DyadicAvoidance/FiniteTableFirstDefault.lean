import OAI.MeasureTheory.DyadicAvoidance.FirstDefault

namespace OAI

universe u_K

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FirstDefault

/-- Transport of the finite-depth survival law to actual finite spatial
selector tables. The center lookup need only select distinct coordinates;
unused table entries are integrated out automatically. -/
theorem measure_no_default_finite_table {M d : ℕ} {K : Type u_K} [Fintype K]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ b, ν {b} = (2 : ENNReal)⁻¹)
    (center : BoundedAddress M d → K) (hinj : Function.Injective center) :
    (Measure.pi (fun _ : K => ν))
        (⋃ f : Path M d, {ω | ∀ i : Tests f,
          ω (center (boundedAddress f i)) = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  apply measure_no_default_bounded
    (Measure.pi (fun _ : K => ν)) (fun a ω => ω (center a))
  · intro a
    exact measurable_pi_apply _
  · have hi : iIndepFun (fun k (ω : K → Bool) => ω k)
        (Measure.pi (fun _ : K => ν)) :=
      iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    exact hi.precomp hinj
  · intro a b
    rw [(measurePreserving_eval (fun _ : K => ν) (center a)).measure_preimage
      (measurableSet_singleton b).nullMeasurableSet]
    exact hfair b

end Problem310.FirstDefault

end

end OAI
