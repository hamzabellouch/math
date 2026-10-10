import Mathlib

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open MeasureTheory Filter Set
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma normalized_defect_moment_tendsto_zero
    (D t : Ω → ℝ) (hD : Measurable D) (ht : Measurable t)
    (hDp : ∀ x, 0 ≤ D x) (htp : ∀ x, 0 ≤ t x)
    (hzero : ∀ x, t x = 0 → D x = 0)
    (hint : Integrable (fun x => D x/(t x)^4) μ) :
    Tendsto (fun r : ℝ => ∫ x, ({x | t x ≤ r}.indicator D x)/r^4 ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let F : ℝ → Ω → ℝ := fun r x => ({x | t x ≤ r}.indicator D x)/r^4
  have hmeas (r : ℝ) : AEStronglyMeasurable (F r) μ :=
    ((hD.indicator (ht measurableSet_Iic)).div_const _).aestronglyMeasurable
  have hbound : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ᵐ x ∂μ, ‖F r x‖ ≤ D x/(t x)^4 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply Eventually.of_forall
    intro x
    have hrp : 0 < r := hr
    by_cases hx : t x ≤ r
    · simp only [F,Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx,Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hDp x) (by positivity : 0 ≤ r^4))]
      by_cases hz : t x = 0
      · simp only [hzero x hz,zero_div,le_refl]
      · exact div_le_div_of_nonneg_left (hDp x)
          (pow_pos (lt_of_le_of_ne (htp x) (Ne.symm hz)) 4)
          (pow_le_pow_left₀ (htp x) hx 4)
    · simp only [F,Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hx,zero_div,norm_zero]
      exact div_nonneg (hDp x) (by positivity)
  have hlim (x : Ω) : Tendsto (fun r => F r x) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    by_cases hz : t x = 0
    · have he : ∀ r, F r x = 0 := by
        intro r
        by_cases hx : t x ≤ r
        · simp only [F,Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx,hzero x hz,zero_div]
        · simp only [F,Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hx,zero_div]
      simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) _ _)
    · have hp : 0 < t x := lt_of_le_of_ne (htp x) (Ne.symm hz)
      have he : ∀ᶠ r in 𝓝[>] (0:ℝ), F r x = 0 := by
        filter_upwards [(nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) (gt_mem_nhds hp)] with r hr
        simp only [F,Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right (not_le.mpr hr),zero_div]
      exact tendsto_const_nhds.congr' (he.mono (fun _ hr => hr.symm))
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun x => D x/(t x)^4) (Eventually.of_forall hmeas) hbound hint (Eventually.of_forall hlim)
end TamingCompatibility

end
end

end OAI
