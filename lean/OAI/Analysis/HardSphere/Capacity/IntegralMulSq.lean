import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HardSphere.RayCapacity

lemma integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hi : inner ℝ F G=∫ x, f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp [F,G,hx,hy,mul_comm]
  have hnF : ‖F‖^2=∫ x, (f x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [F,hx,pow_two]
  have hnG : ‖G‖^2=∫ x, (g x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp [G,hx,pow_two]
  rw [← hi,← hnF,← hnG,← mul_pow,← sq_abs (inner ℝ F G)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm F G)

lemma interval_memLp_two {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq (hf.mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)).mpr
  exact hf.pow 2 |>.integrableOn_Icc |>.mono_set Ioc_subset_Icc_self

lemma inv_sq_integral {r s : ℝ} (hr : 0<r) (hrs : r ≤ s) :
    (∫ t : ℝ in r..s, (t⁻¹)^2)=r⁻¹-s⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ ↦ (t⁻¹)^2) (uIcc r s) := by
    rw [uIcc_of_le hrs]
    exact (continuousOn_id.inv₀ (fun t ht ↦ (hr.trans_le ht.1).ne')).pow 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ ↦ -(t⁻¹)) (f' := fun t ↦ (t⁻¹)^2) (a := r) (b := s) ?_
    hc.intervalIntegrable
  · simpa only [neg_sub_neg] using h
  · intro t ht
    rw [uIcc_of_le hrs] at ht
    convert (hasDerivAt_inv (hr.trans_le ht.1).ne').neg using 1
    simp

lemma ray_pointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r s : ℝ} (hr : 0<r) (hrs : r ≤ s) :
    ‖f s-f r‖^2 ≤ (r⁻¹-s⁻¹)*(∫ t in r..s, ‖deriv f t‖^2*t^2) := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfg : ContinuousOn (fun t : ℝ ↦ ‖deriv f t‖*t) (Icc r s) :=
    (hdc.norm.mul continuous_id).continuousOn
  have hig : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc r s) :=
    continuousOn_id.inv₀ (fun t ht ↦ (hr.trans_le ht.1).ne')
  have hcauchy := integral_mul_sq_le (interval_memLp_two hig) (interval_memLp_two hfg)
  have hprod : (∫ t in Ioc r s, t⁻¹*(‖deriv f t‖*t))=∫ t in r..s, ‖deriv f t‖ := by
    rw [intervalIntegral.integral_of_le hrs]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    field_simp [(hr.trans ht.1).ne']
  have hgrad : (∫ t in Ioc r s, (‖deriv f t‖*t)^2)=∫ t in r..s, ‖deriv f t‖^2*t^2 := by
    rw [intervalIntegral.integral_of_le hrs]
    simp only [mul_pow]
  have hinv : (∫ t in Ioc r s, (t⁻¹)^2)=r⁻¹-s⁻¹ := by
    rw [← intervalIntegral.integral_of_le hrs,inv_sq_integral hr hrs]
  rw [hprod,hgrad,hinv] at hcauchy
  have hdis := norm_sub_le_integral_of_norm_deriv_le_of_le hrs
    hf.continuous.continuousOn (hf.differentiable (by norm_num)).differentiableOn
    (ae_of_all _ (fun _ _ ↦ le_rfl)) (hdc.norm.intervalIntegrable r s)
  exact (pow_le_pow_left₀ (norm_nonneg _) hdis 2).trans hcauchy

lemma ray_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r R : ℝ} (hr : 0<r) (hR : 0≤R)
    (hz : ∀ t ∈ Icc (0:ℝ) r, f t=0) :
    (∫ t in (0:ℝ)..R, ‖f t‖^2*t^2) ≤
      R^3/(3*r)*(∫ t in (0:ℝ)..R, ‖deriv f t‖^2*t^2) := by
  have hdc := hf.continuous_deriv (by norm_num)
  have hgrad : Continuous (fun t : ℝ ↦ ‖deriv f t‖^2*t^2) :=
    (hdc.norm.pow 2).mul (continuous_id.pow 2)
  let A := ∫ t in (0:ℝ)..R, ‖deriv f t‖^2*t^2
  have hA : 0≤A := intervalIntegral.integral_nonneg_of_forall hR
    (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb (s : ℝ) (hs : s∈Icc (0:ℝ) R) : ‖f s‖^2 ≤ r⁻¹*A := by
    by_cases hsr : s ≤ r
    · rw [hz s ⟨hs.1,hsr⟩,norm_zero,zero_pow (by decide)]
      exact mul_nonneg (inv_nonneg.mpr hr.le) hA
    · have hrs : r ≤ s := le_of_lt (lt_of_not_ge hsr)
      have hp := ray_pointwise hf hr hrs
      rw [hz r ⟨hr.le,le_rfl⟩,sub_zero] at hp
      have hI : 0≤∫ t in r..s, ‖deriv f t‖^2*t^2 :=
        intervalIntegral.integral_nonneg_of_forall hrs (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hIA : (∫ t in r..s, ‖deriv f t‖^2*t^2)≤A :=
        intervalIntegral.integral_mono_interval hr.le hrs hs.2
          (ae_of_all _ (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))) (hgrad.intervalIntegrable 0 R)
      apply hp.trans
      exact (mul_le_mul_of_nonneg_right (sub_le_self _ (inv_nonneg.mpr (hr.le.trans hrs))) hI).trans
        (mul_le_mul_of_nonneg_left hIA (inv_nonneg.mpr hr.le))
  have h := intervalIntegral.integral_mono_on (μ := volume) hR
    (((hf.continuous.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R)
    ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 R)
    (fun t ht ↦ mul_le_mul_of_nonneg_right (hb t ht) (sq_nonneg t))
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq] at h
  rw [intervalIntegral.integral_const_mul,integral_pow] at h
  norm_num at h
  convert h using 1; dsimp [A]; ring

lemma ray_lintegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r R B : ℝ} (hr : 0<r) (hR : 0≤R)
    (hRB : R≤B) (hz : ∀ t ∈ Icc (0:ℝ) r, f t=0)
    {g : ℝ → ℝ} (hg : Continuous g) (hgn : ∀t, 0≤g t)
    (hgrad : ∀t∈Icc (0:ℝ) R, ‖deriv f t‖^2 ≤ g t) :
    (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (‖f t‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (g t)) := by
  have hB := hR.trans hRB
  have hdc := hf.continuous_deriv (by norm_num)
  have hgi : IntervalIntegrable (fun t ↦ g t*t^2) volume 0 R := (hg.mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hfi : IntervalIntegrable (fun t ↦ ‖f t‖^2*t^2) volume 0 R :=
    ((hf.continuous.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hdi : IntervalIntegrable (fun t ↦ ‖deriv f t‖^2*t^2) volume 0 R := ((hdc.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hR hdi hgi
    (fun t ht ↦ mul_le_mul_of_nonneg_right (hgrad t ht) (sq_nonneg t))
  have hbound := (ray_integral hf hr hR hz).trans
    (mul_le_mul_of_nonneg_left hmono (by positivity : 0≤R^3/(3*r)))
  have hcoef : R^3/(3*r) ≤ B^3/(3*r) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hR hRB 3) (by positivity)
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_right hcoef
    (intervalIntegral.integral_nonneg_of_forall hR (fun t ↦ mul_nonneg (hgn t) (sq_nonneg t))))
  rw [intervalIntegral.integral_of_le hR,intervalIntegral.integral_of_le hR] at hfinal
  have hfI : (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (‖f t‖^2))=
      ENNReal.ofReal (∫ t in Ioc (0:ℝ) R, ‖f t‖^2*t^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioc 0 R)) (f := fun t ↦ ‖f t‖^2*t^2)
      hfi.1
      (ae_of_all _ (fun t ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  have hgI : (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (g t))=
      ENNReal.ofReal (∫ t in Ioc (0:ℝ) R, g t*t^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioc 0 R)) (f := fun t ↦ g t*t^2)
      hgi.1
      (ae_of_all _ (fun t ↦ mul_nonneg (hgn t) (sq_nonneg _)))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (hgn t),mul_comm]
  rw [hfI,hgI,← ENNReal.ofReal_mul (by positivity : 0≤B^3/(3*r))]
  exact ENNReal.ofReal_le_ofReal hfinal

end HardSphere.RayCapacity

end

end OAI
