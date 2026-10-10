import OAI.Probability.FreeIsing.Gaussian.TreeResponseSource
import OAI.Probability.FreeIsing.Gaussian.VarianceLower
import OAI.Probability.FreeIsing.Trees.ResponseFieldBound

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.GaussianTreeResponse

theorem varianceLower_mul_response_sq_le_integral_source
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (h : TreeVertex d → ℝ)
    (E : Finset (TreeVertex d)) (r : E) (v : TreeVertex d) (a : ℝ)
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ≥0} (ht : (t : ℝ) ≤ T) :
    GaussianVarianceLower.varianceLower T (|a| + (d : ℝ) * beta) *
        response beta E r v h ^ 2 ≤
      ∫ z, TreePathResponse.covariance beta (Function.update h r (a + z)) E r v ^ 2
        ∂gaussianReal 0 t := by
  classical
  have hK : 0 ≤ |a| + (d : ℝ) * beta :=
    add_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hb)
  have hm : Measurable (fun z : ℝ =>
      TreePathResponse.field beta (Function.update h r (a + z)) E r) := by
    apply (TreePathResponse.measurable_field beta E r).comp
    fun_prop
  have hlower := GaussianVarianceLower.varianceLower_le_integral hT hK ht hm
    (TreePathResponse.field_update_source_noise_bound hb h E r a)
  have heq (z : ℝ) :
      TreePathResponse.covariance beta (Function.update h r (a + z)) E r v ^ 2 =
      (1 - Real.tanh (TreePathResponse.field beta
        (Function.update h r (a + z)) E r) ^ 2) ^ 2 * response beta E r v h ^ 2 := by
    rw [TreePathResponse.covariance_eq_variance_mul_response beta _ r.property,
      TreePathResponse.tanh_field beta _ r.property, mul_pow]
    congr 1
    exact congrArg (fun x : ℝ => x ^ 2)
      ((TreePathResponse.response_update_source beta h r.property v (a + z) (h r)).trans
        (by rw [Function.update_eq_self]))
  simp_rw [heq]
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right hlower (sq_nonneg _)

lemma finiteField_update_source {d : ℕ} (E : Finset (TreeVertex d)) (r : E)
    (h x : TreeVertex d → ℝ) (y : E → ℝ) (z : ℝ) :
    (fun u => h u + Function.updateFinset x E (Function.update y r z) u) =
      Function.update (fun u => h u + Function.updateFinset x E y u) r (h r + z) := by
  classical
  funext u
  by_cases hu : u = r
  · subst u
    simp only [Function.update_self, Function.updateFinset, dite_eq_left r.property]
  · rw [Function.update_of_ne hu]
    by_cases hue : u ∈ E
    · simp only [Function.updateFinset, dite_eq_left hue]
      rw [Function.update_of_ne (show (⟨u, hue⟩ : E) ≠ r from
        fun he => hu (congrArg Subtype.val he))]
    · simp only [Function.updateFinset, dite_eq_right hue]

theorem varianceLower_mul_integral_finiteRow_sq_le_raw
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (t : TreeVertex d → ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    {E : Finset (TreeVertex d)} (hE : ConnectedFinset E) (r : E)
    (hrnil : r.1.1 = []) (ht : (t r : ℝ) ≤ T)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) :
    GaussianVarianceLower.varianceLower T (|h r| + (d : ℝ) * beta) *
      (∫ y, finiteRow beta E r h x v y ^ 2
        ∂Measure.pi (fun u : E => gaussianReal 0 (t u))) ≤
      ∫ y, GaussianTreeCovariance.finiteRow beta E r h x v y ^ 2
        ∂Measure.pi (fun u : E => gaussianReal 0 (t u)) := by
  classical
  let c := GaussianVarianceLower.varianceLower T (|h r| + (d : ℝ) * beta)
  have hc : 0 ≤ c := (GaussianVarianceLower.varianceLower_pos _ _).le
  have hi := integrable_finiteRow_sq hb (fun _ => 0) t hE r.property hrnil h x v
  have hj := GaussianTreeCovariance.integrable_finiteRow_sq hb
    (fun _ => 0) t hE r.property hrnil h x v
  have hm : Measurable (fun y : E → ℝ => ENNReal.ofReal (c * finiteRow beta E r h x v y ^ 2)) := by
    unfold finiteRow
    split_ifs
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_mul
      apply Measurable.pow_const
      apply (measurable_response beta E r v).comp
      fun_prop
    · exact measurable_const
  have hn : Measurable (fun y : E → ℝ => ENNReal.ofReal
      (GaussianTreeCovariance.finiteRow beta E r h x v y ^ 2)) := by
    unfold GaussianTreeCovariance.finiteRow
    split_ifs
    · apply Measurable.ennreal_ofReal
      apply Measurable.pow_const
      apply (GaussianTreeCovariance.measurable_covariance beta E r v).comp
      fun_prop
    · exact measurable_const
  change c * (∫ y, finiteRow beta E r h x v y ^ 2 ∂_) ≤ _
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hi.const_mul c)
    (Filter.Eventually.of_forall fun _ => mul_nonneg hc (sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hj (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_le_of_lmarginal_le {r} hm hn
  intro y
  simp only [lmarginal_singleton, finiteRow_update_source, lintegral_const,
    measure_univ, mul_one]
  by_cases hv : v ∈ E
  · have hs := varianceLower_mul_response_sq_le_integral_source hb
      (fun u => h u + Function.updateFinset x E y u) E r v (h r) hT ht
    have hslice : Integrable (fun z : ℝ =>
        GaussianTreeCovariance.finiteRow beta E r h x v (Function.update y r z) ^ 2)
        (gaussianReal 0 (t r)) := by
      simpa only [GaussianTreeCovariance.finiteRow, ite_eq_left hv] using
        GaussianTreeCovariance.integrable_covariance_sq hb
          (X := fun z => Function.updateFinset x E (Function.update y r z)) (by fun_prop)
          hE r.property (fun u _ => by simp [hrnil]) h v hv
    have heq (z : ℝ) :
        GaussianTreeCovariance.finiteRow beta E r h x v (Function.update y r z) =
        TreePathResponse.covariance beta
          (Function.update (fun u => h u + Function.updateFinset x E y u) r (h r + z)) E r v := by
      simp only [GaussianTreeCovariance.finiteRow, ite_eq_left hv,
        GaussianTreeCovariance.covariance, TreePathResponse.covariance, finiteField_update_source]
    have hs' : c * finiteRow beta E r h x v y ^ 2 ≤
        ∫ z, GaussianTreeCovariance.finiteRow beta E r h x v (Function.update y r z) ^ 2
          ∂gaussianReal 0 (t r) := by
      simpa only [c, finiteRow, ite_eq_left hv, heq] using hs
    have he := ENNReal.ofReal_le_ofReal hs'
    rw [ofReal_integral_eq_lintegral_ofReal hslice
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)] at he
    simpa only [mul_one] using he
  · simp only [finiteRow, GaussianTreeCovariance.finiteRow, ite_eq_right hv,
      zero_pow (by decide : 2 ≠ 0), mul_zero, ENNReal.ofReal_zero, lintegral_zero, le_refl]

end Problem367.GaussianTreeResponse

end

end OAI
