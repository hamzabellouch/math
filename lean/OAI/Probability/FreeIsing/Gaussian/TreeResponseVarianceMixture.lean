import OAI.Probability.FreeIsing.Gaussian.TreeResponseVarianceComparison

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

lemma varianceLower_antitone_field {T A K : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hAK : A ≤ K) :
    GaussianVarianceLower.varianceLower T K ≤ GaussianVarianceLower.varianceLower T A := by
  unfold GaussianVarianceLower.varianceLower
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply GaussianVarianceLower.squared_variance_lower_on_abs_le
  · linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ T + 1 + A)]
    linarith

theorem varianceLower_mul_integral_shiftedRow_sq_le_raw
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (t : TreeVertex d → ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    {E : Finset (TreeVertex d)} (hE : ConnectedFinset E) (r : E)
    (hrnil : r.1.1 = []) (ht : (t r : ℝ) ≤ T)
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    {K : ℝ} (_hK : 0 ≤ K) (hbound : ∀ ω, |H ω r| ≤ K)
    (x : TreeVertex d → ℝ) (v : TreeVertex d) :
    GaussianVarianceLower.varianceLower T (K + (d : ℝ) * beta) *
      (∫ p, shiftedRow beta E r H x v p ^ 2
        ∂μ.prod (Measure.pi (fun u : E => gaussianReal 0 (t u)))) ≤
      ∫ p : Ω × (E → ℝ),
        GaussianTreeCovariance.finiteRow beta E r (H p.1) x v p.2 ^ 2
        ∂μ.prod (Measure.pi (fun u : E => gaussianReal 0 (t u))) := by
  classical
  have hi := integrable_shiftedRow_sq μ hb (fun _ => 0) t hE r.property hrnil H hH x v
  have hj : Integrable (fun p : Ω × (E → ℝ) =>
      GaussianTreeCovariance.finiteRow beta E r (H p.1) x v p.2 ^ 2)
      (μ.prod (Measure.pi (fun u : E => gaussianReal 0 (t u)))) := by
    by_cases hv : v ∈ E
    · simpa only [GaussianTreeCovariance.finiteRow, ite_eq_left hv, zero_add] using
        GaussianTreeCovariance.integrable_covariance_sq hb
          (P := μ.prod (Measure.pi (fun u : E => gaussianReal 0 (t u))))
          (X := fun p : Ω × (E → ℝ) =>
            fun u => H p.1 u + Function.updateFinset x E p.2 u)
          (by fun_prop) hE r.property (fun u _ => by simp [hrnil]) (fun _ => 0) v hv
    · simp only [GaussianTreeCovariance.finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
      exact integrable_zero _ _ _
  rw [integral_prod _ hi, integral_prod _ hj, ← integral_const_mul]
  apply integral_mono (hi.integral_prod_left.const_mul _) hj.integral_prod_left
  intro ω
  have hc := varianceLower_antitone_field hT
    (add_nonneg (abs_nonneg (H ω r)) (mul_nonneg (Nat.cast_nonneg d) hb))
    (show |H ω r| + (d : ℝ) * beta ≤ K + (d : ℝ) * beta by linarith [hbound ω])
  calc
    _ ≤ GaussianVarianceLower.varianceLower T (|H ω r| + (d : ℝ) * beta) *
        (∫ y, finiteRow beta E r (H ω) x v y ^ 2
          ∂Measure.pi (fun u : E => gaussianReal 0 (t u))) :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg (fun _ => sq_nonneg _))
    _ ≤ _ := varianceLower_mul_integral_finiteRow_sq_le_raw hb t hT hE r hrnil ht (H ω) x v

end Problem367.GaussianTreeResponse

end

end OAI
