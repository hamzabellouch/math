import OAI.Analysis.BernoulliCone.IntegratedPrimitive

namespace OAI

universe uα

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Bernoulli
open scoped _root_.Bernoulli

theorem integral_nonneg_of_dominated_upper_limit {α : Type uα} [MeasurableSpace α]
    {μ:Measure α} {R:ℕ→α→ℝ} {D C:α→ℝ}
    (hR:∀n,Integrable (R n) μ) (hD:Integrable D μ) (hC:Integrable C μ)
    (hbound:∀n,∀ᵐ x ∂μ,‖R n x‖≤C x)
    (hpos:∀n,0≤∫x,R n x ∂μ)
    (hlim:∀ᵐ x ∂μ,∀η:ℝ,0<η → ∀ᶠ n in atTop,R n x<D x+η) :
    0≤∫x,D x ∂μ := by
  let E:=fun n x=>max (R n x-D x) 0
  have hEn n:∫x,E n x ∂μ≥0:=integral_nonneg (fun x=>le_max_right _ _)
  have hEb n:∀ᵐ x ∂μ,‖E n x‖≤C x+‖D x‖:=by
    filter_upwards [hbound n] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · calc
        R n x-D x ≤ ‖R n x-D x‖ := le_abs_self _
        _ ≤ ‖R n x‖+‖D x‖ := norm_sub_le _ _
        _ ≤ C x+‖D x‖ := add_le_add hx le_rfl
    · exact add_nonneg ((norm_nonneg _).trans hx) (norm_nonneg _)
  have hEi n:Integrable (E n) μ:=
    (hC.add hD.norm).mono' (((hR n).aestronglyMeasurable.aemeasurable.sub hD.aestronglyMeasurable.aemeasurable).max aemeasurable_const).aestronglyMeasurable (hEb n)
  have hEc:∀ᵐ x ∂μ,Tendsto (fun n=>E n x) atTop (𝓝 0):=by
    filter_upwards [hlim] with x hx
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun n=>ha.trans_le (le_max_right _ _)
    · intro b hb
      exact (hx b hb).mono fun n hn=>max_lt (by linarith) hb
  have ht:Tendsto (fun n=>∫x,E n x ∂μ) atTop (𝓝 0):=by
    simpa using tendsto_integral_of_dominated_convergence (C+fun x=>‖D x‖)
      (fun n=>(hEi n).aestronglyMeasurable) (hC.add hD.norm) hEb hEc
  have hi n:0≤(∫x,D x ∂μ)+(∫x,E n x ∂μ):=by
    rw [←integral_add hD (hEi n)]
    refine (hpos n).trans (integral_mono_ae (hR n) (hD.add (hEi n)) ?_)
    filter_upwards [] with x
    have hh:=le_max_left (R n x-D x) 0
    change R n x≤D x+max (R n x-D x) 0
    linarith
  have h:=ge_of_tendsto (tendsto_const_nhds.add ht) (Eventually.of_forall hi)
  simpa using h
end Bernoulli

end
end

end OAI
