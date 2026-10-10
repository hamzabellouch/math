import OAI.Probability.PosteriorReplicas.Information.EntropyTest

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma abs_le_pos_add_exp_neg (x : ℝ) : |x| ≤ max x 0 + Real.exp (-x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx), max_eq_right (le_of_not_ge hx)]
    linarith [Real.add_one_le_exp (-x)]

lemma integrable_llr_of_positive {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) (hi : Integrable (fun x => max (llr μ ν x) 0) μ) :
    Integrable (llr μ ν) μ := by
  apply (hi.add (integrable_exp_neg_llr μ ν hac)).mono' (by fun_prop)
  exact ae_of_all _ (fun x => by simpa using abs_le_pos_add_exp_neg (llr μ ν x))

lemma likelihood_positive_log_bound {w a : ℝ} (hw : 0 ≤ w) (ha : 0 < a) (m : ℕ) :
    (w*a⁻¹^m) * max (Real.log (w*a⁻¹^m)) 0 ≤
      1+w^4 + (2*(m:ℝ)) * (w*a⁻¹^(m+1)) := by
  by_cases hw0 : w = 0
  · simp [hw0]
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hrp : 0 < w*a⁻¹^m := mul_pos hwp (pow_pos (inv_pos.mpr ha) _)
  have hlog : max (Real.log (w*a⁻¹^m)) 0 ≤ w*a⁻¹^m :=
    max_le (Real.log_le_self hrp.le) hrp.le
  by_cases hlarge : a⁻¹^m ≤ max 1 w
  · have hwmax : w ≤ max 1 w := le_max_right _ _
    have hmpos : 0 ≤ max 1 w := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
    have hr : w*a⁻¹^m ≤ (max 1 w)^2 := by
      simpa [pow_two] using mul_le_mul hwmax hlarge (by positivity) hmpos
    have hsq : (w*a⁻¹^m)^2 ≤ (max 1 w)^4 := by
      have ht := (sq_le_sq₀ hrp.le (sq_nonneg _)).mpr hr
      simpa only [← pow_mul] using ht
    have hm4 : (max 1 w)^4 ≤ 1+w^4 := by
      by_cases h : w ≤ 1
      · rw [max_eq_left h]
        norm_num
        positivity
      · rw [max_eq_right (le_of_not_ge h)]
        linarith
    calc
      _ ≤ (w*a⁻¹^m)^2 := by nlinarith [mul_le_mul_of_nonneg_left hlog hrp.le]
      _ ≤ 1+w^4 := hsq.trans hm4
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hwa : w ≤ a⁻¹^m := (le_max_right 1 w).trans (le_of_not_ge hlarge)
    have h1a : 1 ≤ a⁻¹^m := (le_max_left 1 w).trans (le_of_not_ge hlarge)
    have hlw := Real.log_le_log hwp hwa
    have hlognon : 0 ≤ Real.log (a⁻¹^m) := Real.log_nonneg h1a
    have hlogupper : max (Real.log (w*a⁻¹^m)) 0 ≤ 2*(m:ℝ)*a⁻¹ := by
      rw [Real.log_mul hw0 (pow_ne_zero _ (inv_ne_zero ha.ne'))]
      have ha' := (Real.log_le_self (inv_pos.mpr ha).le)
      rw [Real.log_pow] at hlw hlognon
      rw [Real.log_pow]
      have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
      have ht := mul_le_mul_of_nonneg_left ha' hm
      apply max_le <;> nlinarith
    calc
      _ ≤ (w*a⁻¹^m) * (2*(m:ℝ)*a⁻¹) := mul_le_mul_of_nonneg_left hlogupper hrp.le
      _ = (2*(m:ℝ)) * (w*a⁻¹^(m+1)) := by rw [pow_succ]; ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma replica_likelihood_integrable {X : Type*} [MeasurableSpace X]
    (R : Measure X) [IsFiniteMeasure R] {w a : X → ℝ} (hw : Measurable w) (ha : Measurable a)
    (hwp : ∀ᵐ x ∂ R, 0 ≤ w x) (hap : ∀ᵐ x ∂ R, 0 < a x) (m : ℕ)
    (hw4 : Integrable (fun x => w x^4) R)
    (hwa : Integrable (fun x => w x*(a x)⁻¹^(m+1)) R)
    [IsFiniteMeasure (R.withDensity (fun x => ENNReal.ofReal (w x*(a x)⁻¹^m)))] :
    Integrable (fun x => Real.log (w x*(a x)⁻¹^m))
      (R.withDensity (fun x => ENNReal.ofReal (w x*(a x)⁻¹^m))) := by
  let g : X → ℝ≥0∞ := fun x => ENNReal.ofReal (w x*(a x)⁻¹^m)
  have hg : Measurable g := by unfold g; fun_prop
  have hp : Integrable (fun x => max (Real.log (w x*(a x)⁻¹^m)) 0) (R.withDensity g) := by
    rw [integrable_withDensity_iff_integrable_smul' hg (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    apply (((integrable_const 1).add hw4).add (hwa.const_mul (2*(m:ℝ)))).mono' (by fun_prop)
    filter_upwards [hwp,hap] with x hwx hax
    rw [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change (ENNReal.ofReal (w x*(a x)⁻¹^m)).toReal * _ ≤ _
    rw [ENNReal.toReal_ofReal (mul_nonneg hwx (pow_nonneg (inv_nonneg.mpr hax.le) _))]
    exact likelihood_positive_log_bound hwx hax m
  have he : llr (R.withDensity g) R =ᵐ[R.withDensity g]
      (fun x => Real.log (w x*(a x)⁻¹^m)) := by
    apply (llr_withDensity_ae R hg).trans
    filter_upwards [(withDensity_absolutelyContinuous R g).ae_le hwp,
      (withDensity_absolutelyContinuous R g).ae_le hap] with x hwx hax
    dsimp only [g]
    rw [ENNReal.toReal_ofReal (by positivity)]
  exact (integrable_llr_of_positive (R.withDensity g) R (withDensity_absolutelyContinuous R g)
    (hp.congr (he.symm.fun_comp (fun x => max x 0)))).congr he

end PosteriorReplicas
end

end OAI
