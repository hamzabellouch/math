import OAI.Analysis.FreeEntropy.GaussianConvolutionBounds

namespace OAI

universe u1

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedGradient_measurable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (s : ℝ) (i : ι) : StronglyMeasurable (fun x => smoothedGradient μ s x i) := by
  exact (((normalGradient_continuous s i).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).integral_prod_right'
 theorem smoothedSecond_measurable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (s : ℝ) (i : ι) : StronglyMeasurable (fun x => smoothedSecond μ s x i) := by
  exact (((normalSecond_continuous s i).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).integral_prod_right'
 theorem smoothedTime_measurable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (s : ℝ) : StronglyMeasurable (smoothedTimeDerivative μ s) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => normalTimeDerivative s (z.1-z.2)) := by
    unfold normalTimeDerivative normalKernel
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'
 theorem smoothedSecond_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (_hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedSecond μ s x i| ≤ (((‖x‖+K)^2/a^2)+1/a)*smoothedDensity μ s x := by
  have hs0 := ha.trans_le hs
  have hi : Integrable (fun y => normalSecond s (x-y) i) μ := integrable_of_normBound μ hμ ((normalSecond_continuous s i).comp (continuous_const.sub continuous_id))
  calc
    _ ≤ ∫y,|normalSecond s (x-y) i| ∂μ := by simpa only [smoothedSecond,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => normalSecond s (x-y) i)
    _ ≤ ∫y,(((‖x‖+K)^2/a^2)+1/a)*normalKernel s (x-y) ∂μ := by
      apply integral_mono_ae hi.norm ((normalKernel_integrable_finite μ hs0 x).const_mul _)
      filter_upwards [hμ] with y hy
      unfold normalSecond
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (normalKernel_pos _ _)]
      apply mul_le_mul_of_nonneg_right _ (normalKernel_pos _ _).le
      have hn0 : |(x-y) i| ≤ ‖x-y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i
      have hn : |(x-y) i| ≤ ‖x‖+K := hn0.trans ((norm_sub_le x y).trans (add_le_add le_rfl hy))
      have hn2 : ((x-y) i)^2 ≤ (‖x‖+K)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hn 2
      calc
        _ ≤ |((x-y) i)^2/s^2|+|1/s| := abs_sub _ _
        _ = ((x-y) i)^2/s^2+1/s := by rw [abs_of_nonneg (by positivity),abs_of_pos (by positivity)]
        _ ≤ _ := add_le_add
          ((div_le_div_of_nonneg_right hn2 (sq_nonneg s)).trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ ha.le hs 2)))
          (one_div_le_one_div_of_le ha hs)
    _ = _ := integral_const_mul _ _
 theorem smoothedSecond_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedSecond μ s x i| ≤ (2*(1+K^2)/a^2+1/a)*(1+‖x‖^2)*smoothedDensity μ s x := by
  apply (smoothedSecond_bound μ ha hs hK hμ x i).trans
  apply mul_le_mul_of_nonneg_right _ (smoothedDensity_pos μ (ha.trans_le hs) x).le
  have hq : 1 ≤ 1+‖x‖^2 := le_add_of_nonneg_right (sq_nonneg _)
  have hn : (‖x‖+K)^2 ≤ 2*(1+K^2)*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖-K),mul_nonneg (sq_nonneg K) (sq_nonneg ‖x‖)]
  have h := div_le_div_of_nonneg_right hn (sq_nonneg a)
  have h' := mul_le_mul_of_nonneg_left hq (show 0 ≤ 1/a by positivity)
  convert add_le_add h h' using 1 <;> ring
 theorem smoothedGradient_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedGradient μ s x i| ≤ ((1+K)/a)*(1+‖x‖^2)*smoothedDensity μ s x := by
  apply (smoothedGradient_bound μ ha hs hK hμ x i).trans
  apply mul_le_mul_of_nonneg_right _ (smoothedDensity_pos μ (ha.trans_le hs) x).le
  have h : ‖x‖+K ≤ (1+K)*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖-1/2),mul_nonneg hK (sq_nonneg ‖x‖)]
  convert div_le_div_of_nonneg_right h ha.le using 1 ; ring
 theorem smoothedTime_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) :
    |smoothedTimeDerivative μ s x| ≤ ((Fintype.card ι:ℝ)/2*(2*(1+K^2)/a^2+1/a))*(1+‖x‖^2)*smoothedDensity μ s x := by
  classical
  have hmem : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  rw [smoothed_heatEquation μ (isCompact_closedBall _ _) hmem,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2:ℝ)*∑i,|smoothedSecond μ s x i| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1/2:ℝ)*∑_i : ι,(2*(1+K^2)/a^2+1/a)*(1+‖x‖^2)*smoothedDensity μ s x :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => smoothedSecond_polynomial_bound μ ha hs hK hμ x i)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
 theorem smoothedLog_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b) (hD0 : 0 ≤ D)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (hK : 0 ≤ K)
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (x : EuclideanSpace ℝ ι) :
    |Real.log (smoothedDensity μ s x)| ≤ (D+(1+K^2)/a)*(1+‖x‖^2) := by
  apply (smoothedDensity_log_bound μ ha hs hD0 hD hK hμ x).trans
  have h : ‖x‖^2+K^2 ≤ (1+K^2)*(1+‖x‖^2) := by nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg ‖x‖)]
  have h' := div_le_div_of_nonneg_right h ha.le
  have h'' : D ≤ D*(1+‖x‖^2) := by nlinarith [mul_nonneg hD0 (sq_nonneg ‖x‖)]
  convert add_le_add h'' h' using 1 ; ring
end FiniteEntropySeparation

end

end OAI
