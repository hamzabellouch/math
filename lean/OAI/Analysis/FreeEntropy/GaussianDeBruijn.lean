import OAI.Analysis.FreeEntropy.CoordinateIBP

namespace OAI

universe u1

noncomputable section
open MeasureTheory Filter Set Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
def classicalEntropy (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) : ℝ :=
  -(∫x,smoothedDensity μ s x*Real.log (smoothedDensity μ s x))
def classicalFisher (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) : ℝ :=
  ∑i,∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x
 theorem smoothedEntropy_hasDeriv_time (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (_hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t => smoothedDensity μ t x*Real.log (smoothedDensity μ t x))
      ((1+Real.log (smoothedDensity μ s x))*smoothedTimeDerivative μ s x) s := by
  have hm : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  have hd := smoothedDensity_hasDeriv_time μ (isCompact_closedBall _ _) hm hs x
  have hp := (smoothedDensity_pos μ hs x).ne'
  convert hd.mul (hd.log hp) using 1 ; try rfl
  field_simp [hp]
  ring
 theorem classicalEntropy_hasDeriv_integral (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) :
    HasDerivAt (classicalEntropy μ)
      (-(∫x,(1+Real.log (smoothedDensity μ s x))*smoothedTimeDerivative μ s x)) s := by
  let a := s/2
  let b := s+1
  have ha : 0<a := by dsimp [a]; linarith
  have hb : 0<b := by dsimp [b]; linarith
  obtain ⟨D,hD0,hD⟩ := normal_prefactor_bounded (ι := ι) (b := b) ha
  let L := 1+D+(1+K^2)/a
  let T := (Fintype.card ι:ℝ)/2*(2*(1+K^2)/a^2+1/a)
  let A := Real.exp (D+K^2/(2*b))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => smoothedDensity μ t x*Real.log (smoothedDensity μ t x))
    (F' := fun t x => (1+Real.log (smoothedDensity μ t x))*smoothedTimeDerivative μ t x)
    (μ := volume) (s := Icc a b) (bound := fun x => (L*T*A)*(1+‖x‖^2)^2*Real.exp (-(1/(4*b))*‖x‖^2))
    (x₀ := s) (Icc_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hd.2.neg
  · filter_upwards [Icc_mem_nhds (show a<s by dsimp [a]; linarith) (show s<b by dsimp [b]; linarith)] with t ht
    have ht0 := ha.trans_le ht.1
    exact ((smoothedDensity_continuous μ ht0).mul (smoothedLog_continuous μ ht0)).aestronglyMeasurable
  · exact smoothedEntropy_integrable μ hs hK hμ
  · exact ((continuous_const.add (smoothedLog_continuous μ hs)).stronglyMeasurable.mul (smoothedTime_measurable μ s)).aestronglyMeasurable
  · exact ae_of_all _ (fun x t ht => by
      have ht0 := ha.trans_le ht.1
      have hp := (smoothedDensity_pos μ ht0 x).le
      have hlog : |1+Real.log (smoothedDensity μ t x)| ≤ L*(1+‖x‖^2) := by
        have h := smoothedLog_polynomial_bound μ ha ht hD0 (hD t ht) hK hμ x
        have h' := abs_add_le (1:ℝ) (Real.log (smoothedDensity μ t x))
        norm_num only [abs_one] at h'
        dsimp [L]; nlinarith [sq_nonneg ‖x‖]
      have htime := smoothedTime_polynomial_bound μ ha ht.1 hK hμ x
      have hden := (smoothedDensity_bounds μ ha ht (hD t ht) hK hμ x).2
      have he : -‖x‖^2/(4*b)=-(1/(4*b))*‖x‖^2 := by ring
      rw [he] at hden
      rw [Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ (L*(1+‖x‖^2))*(T*(1+‖x‖^2)*smoothedDensity μ t x) := mul_le_mul hlog htime (abs_nonneg _) (by positivity)
        _ = (L*T)*(1+‖x‖^2)^2*smoothedDensity μ t x := by ring
        _ ≤ (L*T)*(1+‖x‖^2)^2*(A*Real.exp (-(1/(4*b))*‖x‖^2)) := mul_le_mul_of_nonneg_left hden (by positivity)
        _ = _ := by ring)
  · convert (polynomial_gaussian_integrable (E := EuclideanSpace ℝ ι) (c := 1/(4*b)) (by positivity) 2).const_mul (L*T*A) using 1
    funext x; ring
  · exact ae_of_all _ (fun x t ht => smoothedEntropy_hasDeriv_time μ hK hμ (ha.trans_le ht.1) x)
 theorem smoothed_score_ibp [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) (i : ι) :
    (∫x,(1+Real.log (smoothedDensity μ s x))*smoothedSecond μ s x i) =
      -(∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x) := by
  have hm : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  have hiSecond := smoothedLog_mul_integrable μ hs hK hμ (smoothedSecond_measurable μ s i)
    (2*(1+K^2)/s^2+1/s) (by positivity) (fun x => smoothedSecond_polynomial_bound μ hs le_rfl hK hμ x i)
  have hiGradient := smoothedLog_mul_integrable μ hs hK hμ (smoothedGradient_measurable μ s i)
    ((1+K)/s) (by positivity) (fun x => smoothedGradient_polynomial_bound μ hs le_rfl hK hμ x i)
  have he : (fun x => (smoothedGradient μ s x i/smoothedDensity μ s x)*smoothedGradient μ s x i) =
      fun x => (smoothedGradient μ s x i)^2/smoothedDensity μ s x := by funext x; ring
  have hiScore : Integrable (fun x => (smoothedGradient μ s x i/smoothedDensity μ s x)*smoothedGradient μ s x i) := by
    rw [he]; exact smoothedScore_integrable μ hs hK hμ i
  have hibp := integral_coordinate_ibp i (fun x => 1+Real.log (smoothedDensity μ s x))
    (fun x => smoothedGradient μ s x i/smoothedDensity μ s x)
    (fun x => smoothedGradient μ s x i) (fun x => smoothedSecond μ s x i) ?_ ?_ hiSecond hiScore hiGradient
  · simpa only [he] using hibp
  · intro x r
    convert ((smoothedDensity_hasDeriv_coordinate μ (isCompact_closedBall _ _) hm s x i r).log (smoothedDensity_pos μ hs _).ne').const_add 1 using 1
  · intro x r
    exact smoothedGradient_hasDeriv_coordinate μ (isCompact_closedBall _ _) hm s x i r
 theorem classicalEntropy_hasDeriv (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) :
    HasDerivAt (classicalEntropy μ) ((1/2:ℝ)*classicalFisher μ s) s := by
  classical
  have hm : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  convert classicalEntropy_hasDeriv_integral μ hK hμ hs using 1 ; try rfl
  simp_rw [smoothed_heatEquation μ (isCompact_closedBall _ _) hm]
  simp_rw [mul_left_comm _ (1/2:ℝ)]
  rw [integral_const_mul]
  simp_rw [mul_sum]
  rw [integral_finsetSum]
  · simp_rw [smoothed_score_ibp μ hK hμ hs]
    simp only [sum_neg_distrib,classicalFisher]
    ring
  · intro i hi
    exact smoothedLog_mul_integrable μ hs hK hμ (smoothedSecond_measurable μ s i)
      (2*(1+K^2)/s^2+1/s) (by positivity) (fun x => smoothedSecond_polynomial_bound μ hs le_rfl hK hμ x i)
 theorem classicalFisher_nonneg (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : 0 ≤ classicalFisher μ s := by
  apply sum_nonneg
  intro i hi
  apply integral_nonneg
  intro x
  exact div_nonneg (sq_nonneg _) (smoothedDensity_pos μ hs x).le
end FiniteEntropySeparation

end

end OAI
