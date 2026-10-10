import OAI.Analysis.CircleDomains.Sobolev.CircleProjectionIntegrable

namespace OAI

/-! The four quarter-arc coordinate functions of a measurable bounded
field have the integrability needed for the projection identity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem quadrant_components_integrable {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) (s t : Bool) :
    IntervalIntegrable (fun θ => (F (quadrantPoint c r s t θ)).re) volume 0 (Real.pi/2) ∧
    IntervalIntegrable (fun θ => (F (quadrantPoint c r s t θ)).im) volume 0 (Real.pi/2) := by
  have hq : Continuous (quadrantPoint c r s t) := by
    change Continuous (fun θ => c + (r : ℂ) * Complex.equivRealProdCLM.symm
      (quadrantSign s * Real.cos θ, quadrantSign t * Real.sin θ))
    fun_prop
  have hbound (θ : ℝ) : ‖F (quadrantPoint c r s t θ)‖ ≤ B :=
    hb _ (by rw [mem_closedBall,quadrantPoint_dist,abs_of_nonneg hr])
  constructor
  · exact intervalIntegrable_of_measurable_bound
      (Complex.measurable_re.comp (hF.comp hq.measurable)) hB
      (fun θ _ => (Complex.abs_re_le_norm _).trans (hbound θ))
  · exact intervalIntegrable_of_measurable_bound
      (Complex.measurable_im.comp (hF.comp hq.measurable)) hB
      (fun θ _ => (Complex.abs_im_le_norm _).trans (hbound θ))

end CircleDomainRigidity

end

end OAI
