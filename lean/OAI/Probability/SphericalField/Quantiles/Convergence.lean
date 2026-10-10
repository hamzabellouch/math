import Mathlib
import OAI.Probability.SphericalField.Quantiles.Entropy
import OAI.Probability.SphericalField.Fields.BoundedPressure
import OAI.Probability.SphericalField.Quantiles.Stationary

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma BoundedField.round_tendsto {B : ℝ} (q : BoundedField B) (u : Time) :
    Tendsto (fun N => q.round N u) atTop (𝓝 (q u)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (g := fun N => (1:ℝ)/(N+1:ℕ)) (fun N => dist_nonneg) ?_ ?_
  · intro N; rw [Real.dist_eq]; exact q.round_error N u
  · exact_mod_cast tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

lemma quantileTail_tendsto {B : ℝ} (qN : ℕ → BoundedField B) (q : BoundedField B)
    (hB : B < 1) (hq : ∀ u, Tendsto (fun N => qN N u) atTop (𝓝 (q u))) {t : ℝ} (ht : t ≤ B) :
    Tendsto (fun N => quantileTail ((qN N).toQuantile hB.le) t) atTop
      (𝓝 (quantileTail (q.toQuantile hB.le) t)) := by
  unfold quantileTail
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
  · intro N
    exact (measurable_const.sub ((qN N).measurable.max measurable_const)).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact ae_of_all _ fun u => by
      change ‖1-max (qN N u) t‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (max_le ((qN N).le_bound u |>.trans hB.le) (ht.trans hB.le)))]
      linarith [le_max_left (qN N u) t,(qN N).nonneg u]
  · exact ae_of_all _ fun u => ((hq u).max tendsto_const_nhds).const_sub 1

lemma quantileA_tendsto_fixed {B r : ℝ} (qN : ℕ → BoundedField B) (q : BoundedField B)
    (hB : B < 1) (hq : ∀ u, Tendsto (fun N => qN N u) atTop (𝓝 (q u))) (hr : r ∈ Icc 0 B) :
    Tendsto (fun N => quantileA ((qN N).toQuantile hB.le) r) atTop
      (𝓝 (quantileA (q.toQuantile hB.le) r)) := by
  unfold quantileA
  simp_rw [intervalIntegral.integral_of_le hr.1]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1/(1-B)^2)
  · intro N
    exact (measurable_const.div (((quantileTail_lipschitz _ ((qN N).toQuantile_measurable hB.le)).continuous.measurable).pow_const 2)).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(quantileTail ((qN N).toQuantile hB.le) t)^2)]
    exact quantileA_integrand_bound _ ((qN N).toQuantile_measurable hB.le) hB
      (ae_of_all _ (qN N).le_bound) (ht.2.trans hr.2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact tendsto_const_nhds.div ((quantileTail_tendsto qN q hB hq (ht.2.trans hr.2)).pow 2)
      (pow_ne_zero _ (ne_of_gt ((sub_pos.mpr hB).trans_le (quantileTail_lower _
        (q.toQuantile_measurable hB.le) (ae_of_all _ q.le_bound) (ht.2.trans hr.2)))))

lemma quantileA_tendsto_moving {B : ℝ} (qN : ℕ → BoundedField B) (q : BoundedField B)
    (hB : B < 1) (hq : ∀ u, Tendsto (fun N => qN N u) atTop (𝓝 (q u))) (u : Time) :
    Tendsto (fun N => quantileA ((qN N).toQuantile hB.le) (qN N u)) atTop
      (𝓝 (quantileA (q.toQuantile hB.le) (q u))) := by
  have hd : Tendsto (fun N => quantileA ((qN N).toQuantile hB.le) (qN N u)-
      quantileA ((qN N).toQuantile hB.le) (q u)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    refine squeeze_zero (g := fun N => (1/(1-B)^2)*|qN N u-q u|) (fun _ => abs_nonneg _) (fun N => quantileA_abs_sub_le _
      ((qN N).toQuantile_measurable hB.le) hB (ae_of_all _ (qN N).le_bound)
      ⟨(qN N).nonneg u,(qN N).le_bound u⟩ ⟨q.nonneg u,q.le_bound u⟩) ?_
    have ht := (((hq u).sub (tendsto_const_nhds (x := q u))).abs.const_mul (1/(1-B)^2))
    simpa only [sub_self,abs_zero,mul_zero] using ht
  have hf := quantileA_tendsto_fixed qN q hB hq ⟨q.nonneg u,q.le_bound u⟩
  simpa only [sub_add_cancel,zero_add] using hd.add hf

lemma BoundedField.stationary_tendsto {B : ℝ} (qN : ℕ → BoundedField B) (q : BoundedField B)
    (hB : B < 1) (hq : ∀ u, Tendsto (fun N => qN N u) atTop (𝓝 (q u))) (u : Time) :
    Tendsto (fun N => (qN N).stationary hB u) atTop (𝓝 (q.stationary hB u)) :=
  (quantileA_tendsto_moving qN q hB hq u).div_const 2

lemma BoundedField.L1_tendsto {H : ℝ} (fN : ℕ → BoundedField H) (f : BoundedField H)
    (hf : ∀ u, Tendsto (fun N => fN N u) atTop (𝓝 (f u))) :
    Tendsto (fun N => fieldL1 (fN N) f) atTop (𝓝 0) := by
  have ht : Tendsto (fun N => ∫ u, |fN N u-f u| ∂timeLaw) atTop
      (𝓝 (∫ _u : Time, (0:ℝ) ∂timeLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => H)
    · intro N; exact (((fN N).measurable.sub f.measurable).abs).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      exact ae_of_all _ fun u => by
        rw [Real.norm_eq_abs,abs_abs,abs_le]
        constructor <;> linarith [(fN N).nonneg u,(fN N).le_bound u,f.nonneg u,f.le_bound u]
    · exact ae_of_all _ fun u => by simpa using ((hf u).sub (tendsto_const_nhds (x := f u))).abs
  simpa [fieldL1] using ht

lemma boundedSphericalFieldValue_tendsto_L1 {H : ℝ} (fN : ℕ → BoundedField H) (f : BoundedField H)
    (hf : Tendsto (fun N => fieldL1 (fN N) f) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun N => boundedSphericalFieldValue (fN N) n) atTop (𝓝 (boundedSphericalFieldValue f n)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (g := fun N => sphericalContinuityConstant n H*fieldL1 (fN N) f) (fun N => dist_nonneg) (fun N => ?_) (by simpa using hf.const_mul (sphericalContinuityConstant n H))
  simpa only [Real.dist_eq] using boundedSphericalFieldValue_L1_continuous (fN N) f n

lemma entropy_quantileTrial_tendsto {B : ℝ} (qN : ℕ → BoundedField B) (q : BoundedField B)
    (hB : B < 1) (hq : ∀ u, Tendsto (fun N => qN N u) atTop (𝓝 (q u))) :
    Tendsto (fun N => (entropy (quantileTrial ((qN N).toQuantile hB.le))).toReal) atTop
      (𝓝 (entropy (quantileTrial (q.toQuantile hB.le))).toReal) := by
  have hI : Tendsto (fun N => ∫ t in (0:ℝ)..B, (quantileTail ((qN N).toQuantile hB.le) t)⁻¹)
      atTop (𝓝 (∫ t in (0:ℝ)..B, (quantileTail (q.toQuantile hB.le) t)⁻¹)) := by
    simp_rw [intervalIntegral.integral_of_le q.bound_nonneg]
    apply tendsto_integral_of_dominated_convergence (fun _ => (1-B)⁻¹)
    · intro N
      exact (((quantileTail_lipschitz _ ((qN N).toQuantile_measurable hB.le)).continuous.measurable).inv).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hd := quantileTail_lower _ ((qN N).toQuantile_measurable hB.le) (ae_of_all _ (qN N).le_bound) ht.2
      rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr ((sub_pos.mpr hB).le.trans hd))]
      exact inv_anti₀ (sub_pos.mpr hB) hd
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (quantileTail_tendsto qN q hB hq ht.2).inv₀ (ne_of_gt ((sub_pos.mpr hB).trans_le
        (quantileTail_lower _ (q.toQuantile_measurable hB.le) (ae_of_all _ q.le_bound) ht.2)))
  have he (f : BoundedField B) : (entropy (quantileTrial (f.toQuantile hB.le))).toReal =
      max (((∫ t in (0:ℝ)..B, (quantileTail (f.toQuantile hB.le) t)⁻¹)+Real.log (1-B))/2) 0 := by
    rw [entropy_quantileTrial _ (f.toQuantile_measurable hB.le) B f.bound_nonneg hB
      (ae_of_all _ f.le_bound),ENNReal.toReal_ofReal']
  simp_rw [he]
  exact ((hI.add tendsto_const_nhds).div_const 2).max tendsto_const_nhds

lemma BoundedField.integral_mul_tendsto {H K : ℝ} (fN : ℕ → BoundedField H) (f : BoundedField H)
    (gN : ℕ → BoundedField K) (g : BoundedField K)
    (hf : ∀ u, Tendsto (fun N => fN N u) atTop (𝓝 (f u)))
    (hg : ∀ u, Tendsto (fun N => gN N u) atTop (𝓝 (g u))) :
    Tendsto (fun N => ∫ u, fN N u*gN N u ∂timeLaw) atTop (𝓝 (∫ u, f u*g u ∂timeLaw)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => H*K)
  · intro N; exact ((fN N).measurable.mul (gN N).measurable).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ((fN N).nonneg u) ((gN N).nonneg u))]
      exact mul_le_mul ((fN N).le_bound u) ((gN N).le_bound u) ((gN N).nonneg u) f.bound_nonneg
  · exact ae_of_all _ fun u => (hf u).mul (hg u)

end SphericalPerceptron
end
end

end OAI
