import OAI.Analysis.LpDimension.StableRetractions

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u uF

namespace SubpolynomialLp

def powerIntensity (p : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity (fun r => ENNReal.ofReal (p*r^(-p-1)))

lemma powerIntensity_integral (p : ℝ) (hp : 0 < p) {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) :
    (∫ r, f r ∂powerIntensity p) = ∫ r in Set.Ioi 0, (p*r^(-p-1)) • f r := by
  rw [powerIntensity, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun r => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [ENNReal.toReal_ofReal (mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt hr) _))]

lemma powerIntensity_restrict_integral (p : ℝ) (hp : 0 < p) {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Set.Ioi 0) :
    (∫ r in s, f r ∂powerIntensity p) = ∫ r in s, (p*r^(-p-1)) • f r := by
  rw [powerIntensity, restrict_withDensity hs, Measure.restrict_restrict hs,
    Set.inter_eq_left.mpr hs0,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun r => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with r hr
  have hr0 := hs0 hr
  rw [ENNReal.toReal_ofReal (mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt hr0) _))]

lemma powerIntensity_tail (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    powerIntensity p (Set.Ioi a) = ENNReal.ofReal (a^(-p)) := by
  rw [powerIntensity, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi ha.le)]
  have hn : ∀ᵐ r ∂volume.restrict (Set.Ioi a), 0 ≤ p*r^(-p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := ha.trans hr
    positivity
  have hi : IntegrableOn (fun r : ℝ => p*r^(-p-1)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p-1 < -1) ha).const_mul p
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -p-1 < -1) ha]
  congr 1
  rw [show -p-1+1 = -p by ring]
  field_simp


lemma powerIntensity_large_moment (p q a : ℝ) (hp : 0 < p) (hqp : q < p)
    (ha : 0 < a) :
    (∫ r in Set.Ioi a, r^q ∂powerIntensity p) = p/(p-q)*a^(q-p) := by
  rw [powerIntensity_restrict_integral p hp _ measurableSet_Ioi (Set.Ioi_subset_Ioi ha.le)]
  have he : (fun r : ℝ => (p*r^(-p-1)) • r^q) =ᵐ[volume.restrict (Set.Ioi a)]
      fun r => p*r^(q-p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := ha.trans hr
    simp only [smul_eq_mul, mul_assoc, ← Real.rpow_add hr0]
    congr 2
    ring
  rw [integral_congr_ae he, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : q-p-1 < -1) ha]
  rw [show q-p-1+1 = q-p by ring]
  rw [show q-p = -(p-q) by ring, neg_div_neg_eq]
  ring

lemma powerIntensity_critical_moment (p a b : ℝ) (hp : 0 < p) (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Set.Ioc a b, r^p ∂powerIntensity p) = p*Real.log (b/a) := by
  rw [powerIntensity_restrict_integral p hp _ measurableSet_Ioc
    (fun r hr => ha.trans hr.1)]
  have he : (fun r : ℝ => (p*r^(-p-1)) • r^p) =ᵐ[volume.restrict (Set.Ioc a b)]
      fun r => p*r⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := ha.trans hr.1
    simp only [smul_eq_mul, mul_assoc, ← Real.rpow_add hr0]
    rw [show -p-1+p = -1 by ring, Real.rpow_neg_one]
  rw [integral_congr_ae he, integral_const_mul, ← intervalIntegral.integral_of_le hab,
    integral_inv_of_pos ha (ha.trans_le hab)]


def stableKernel (p t r : ℝ) : ℝ := (Real.cos (t*r)-1)*r^(-p-1)

lemma stableKernel_abs_le_quadratic (p t r : ℝ) (hr : 0 < r) :
    |stableKernel p t r| ≤ (t^2/2)*r^(1-p) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := t*r)
  have he : |Real.cos (t*r)-1| ≤ (t*r)^2/2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    linarith
  calc
    |stableKernel p t r| = |Real.cos (t*r)-1| * r^(-p-1) := by
      rw [stableKernel, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    _ ≤ ((t*r)^2/2)*r^(-p-1) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = (t^2/2)*r^(1-p) := by
      have heq : r^2*r^(-p-1) = r^(1-p) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
        congr 1
        norm_num
        ring
      calc
        ((t*r)^2/2)*r^(-p-1) = (t^2/2)*(r^2*r^(-p-1)) := by ring
        _ = _ := by rw [heq]

lemma stableKernel_abs_le_large (p t r : ℝ) (hr : 0 ≤ r) :
    |stableKernel p t r| ≤ 2*r^(-p-1) := by
  rw [stableKernel, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr _)
  calc
    |Real.cos (t*r)-1| ≤ |Real.cos (t*r)| + |(1:ℝ)| := abs_sub _ _
    _ ≤ 2 := by have := Real.abs_cos_le_one (t*r); norm_num at *; linarith

lemma stableKernel_integrable (p t : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    IntegrableOn (stableKernel p t) (Set.Ioi 0) := by
  have hs : IntegrableOn (stableKernel p t) (Set.Ioc 0 1) := by
    have hi : IntegrableOn (fun r : ℝ => r^(1-p)) (Set.Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 1-p)).1
    exact (hi.const_mul (t^2/2)).mono' (by unfold stableKernel; fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simpa only [Real.norm_eq_abs] using stableKernel_abs_le_quadratic p t r hr.1)
  have hl : IntegrableOn (stableKernel p t) (Set.Ioi 1) := by
    exact ((integrableOn_Ioi_rpow_of_lt (by linarith : -p-1 < -1) zero_lt_one).const_mul 2).mono'
      (by unfold stableKernel; fun_prop) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        simpa only [Real.norm_eq_abs] using stableKernel_abs_le_large p t r (le_trans (by norm_num) (le_of_lt hr)))
  have hset : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext r
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h,_⟩|h)
      · exact h
      · linarith
    · intro h
      by_cases h' : r ≤ 1
      · exact Or.inl ⟨h,h'⟩
      · exact Or.inr (lt_of_not_ge h')
  rw [← hset]
  exact hs.union hl

lemma stableKernel_scaling_pos (p t : ℝ) (ht : 0 < t) :
    (∫ r in Set.Ioi 0, stableKernel p t r) =
      t^p * ∫ r in Set.Ioi 0, stableKernel p 1 r := by
  have he : (fun r => stableKernel p t r) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun r => t^(p+1) * stableKernel p 1 (t*r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [stableKernel, one_mul, Real.mul_rpow ht.le (le_of_lt hr)]
    rw [show t^(p+1)*((Real.cos (t*r)-1)*(t^(-p-1)*r^(-p-1))) =
      (Real.cos (t*r)-1)*((t^(p+1)*t^(-p-1))*r^(-p-1)) by ring,
      ← Real.rpow_add ht, show p+1+(-p-1) = 0 by ring, Real.rpow_zero, one_mul]
  rw [integral_congr_ae he, integral_const_mul,
    integral_comp_mul_left_Ioi (stableKernel p 1) 0 ht, mul_zero, smul_eq_mul,
    ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add ht]
  congr 2
  ring

lemma stableKernel_scaling (p t : ℝ) (hp : 0 < p) :
    (∫ r in Set.Ioi 0, stableKernel p t r) =
      |t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have he : stableKernel p t = stableKernel p (-t) := by
      funext r
      simp [stableKernel, neg_mul, Real.cos_neg]
    rw [he, stableKernel_scaling_pos p (-t) (neg_pos.mpr ht), abs_of_neg ht]
  · subst t
    simp [stableKernel, Real.zero_rpow hp.ne']
  · rw [stableKernel_scaling_pos p t ht, abs_of_pos ht]

end SubpolynomialLp

end

end OAI
