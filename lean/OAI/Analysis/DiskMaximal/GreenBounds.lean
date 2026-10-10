import OAI.Analysis.DiskMaximal.Kernels

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace PlanePotential

lemma integral_affine (F : ℂ → ℝ) (x : ℂ) (t : ℝ) :
    (∫ z : ℂ, F (x+t • (z-x))) = (t^2)⁻¹ * ∫ y : ℂ, F y := by
  calc
    _ = ∫ w : ℂ, F (x+t • w) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fun w : ℂ => F (x+t • w)) (-x)
    _ = |(t^2)⁻¹| * ∫ y, F (x+y) := by
      simpa only [Complex.finrank_real_complex,smul_eq_mul] using
        Measure.integral_comp_smul volume (fun y : ℂ => F (x+y)) t
    _ = _ := by rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),integral_add_left_eq_self]

lemma integrable_affine_iff (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun z : ℂ => F (x+t • (z-x))) ↔ Integrable F := by
  constructor
  · intro h
    have h1 : Integrable (fun z : ℂ => F (x+t • z)) := by
      simpa only [add_sub_cancel_right] using h.comp_add_right x
    have h2 := (integrable_comp_smul_iff volume (fun z : ℂ => F (x+z)) ht).mp h1
    simpa only [add_neg_cancel_left] using h2.comp_add_left (-x)
  · intro h
    simpa only [sub_eq_add_neg] using ((h.comp_add_left x).comp_smul ht).comp_add_right (-x)

lemma integral_affine_reverse (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℂ, F y) = t^2 * ∫ z : ℂ, F (x+t • (z-x)) := by
  rw [integral_affine]
  field_simp

lemma segment_ftc {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x z : ℂ) :
    (∫ t in Ioc (0:ℝ) 1, fderiv ℝ g (x+t • (z-x)) (z-x)) = g z-g x := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => g (x+s • (z-x)))
      (fderiv ℝ g (x+t • (z-x)) (z-x)) t := by
    have hline : HasDerivAt (fun s : ℝ => x+s • (z-x)) (z-x) t := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const (z-x)).const_add x
    exact ((hg.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t hline
  have hc : Continuous (fun t : ℝ => fderiv ℝ g (x+t • (z-x)) (z-x)) := by
    exact ((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),one_smul,
    add_sub_cancel,zero_smul,add_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)

def segmentForm (ψ g : ℂ → ℝ) (x : ℂ) (t : ℝ) (z : ℂ) : ℝ :=
  ψ z*fderiv ℝ g (x+t • (z-x)) (z-x)
def pullbackForm (ψ g : ℂ → ℝ) (x : ℂ) (t : ℝ) (y : ℂ) : ℝ :=
  ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)*fderiv ℝ g y (y-x)

lemma pullback_identity (ψ g : ℂ → ℝ) (x z : ℂ) {t : ℝ} (ht : 0 < t) :
    pullbackForm ψ g x t (x+t • (z-x)) = (t^2)⁻¹*segmentForm ψ g x t z := by
  have ha : x+t⁻¹ • (x+t • (z-x)-x) = z := by simp [ht.ne']
  unfold pullbackForm segmentForm
  rw [ha,add_sub_cancel_left,map_smul,smul_eq_mul]
  have hp : t^(-3:ℝ) = (t^3)⁻¹ := by
    rw [show (-3:ℝ) = ((-3:ℤ):ℝ) by norm_num,Real.rpow_intCast,zpow_neg,zpow_ofNat]
  rw [hp]
  field_simp

lemma segmentForm_continuous {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2) := by
  unfold segmentForm
  exact (hψ.comp continuous_snd).mul
    (((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply (by fun_prop))

lemma segmentForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    Integrable (segmentForm ψ g x t) := by
  apply ((segmentForm_continuous hψ hg x).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  exact hψc.mul_right

lemma pullbackForm_measurable {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Measurable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2) := by
  unfold pullbackForm
  have ha : Measurable (fun p : ℝ × ℂ => x+p.1⁻¹ • (p.2-x)) := by measurability
  exact ((hψ.measurable.comp ha).mul (measurable_fst.pow_const _)).mul
    ((((hg.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (by fun_prop)).measurable)

lemma pullbackForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    Integrable (pullbackForm ψ g x t) := by
  apply (integrable_affine_iff _ x ht.ne').mp
  simpa only [pullback_identity ψ g x _ ht] using
    (segmentForm_integrable_column hψ hψc hg x t).const_mul ((t^2)⁻¹)

lemma pullback_column_integral (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, pullbackForm ψ g x t y) = ∫ z, segmentForm ψ g x t z := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht]
  rw [integral_const_mul]
  field_simp

lemma pullback_column_norm (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, ‖pullbackForm ψ g x t y‖) = ∫ z, ‖segmentForm ψ g x t z‖ := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht,norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  rw [integral_const_mul]
  field_simp

lemma segmentForm_bound {ψ g : ℂ → ℝ} {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D)
    (x : ℂ) (t : ℝ) (z : ℂ) :
    ‖segmentForm ψ g x t z‖ ≤ |ψ z| *D*‖z-x‖ := by
  rw [segmentForm,norm_mul,Real.norm_eq_abs]
  calc
    _ ≤ |ψ z| *(‖fderiv ℝ g (x+t • (z-x))‖*‖z-x‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ g _).le_opNorm _) (abs_nonneg _)
    _ ≤ |ψ z| *(D*‖z-x‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

lemma segment_weight_integrable {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (x : ℂ) (D : ℝ) :
    Integrable (fun z : ℂ => |ψ z| *D*‖z-x‖) := by
  apply (show Continuous (fun z : ℂ => |ψ z| *D*‖z-x‖) by fun_prop).integrable_of_hasCompactSupport
  exact (hψc.norm.mul_right).mul_right

/-- Absolute integrability justifies the double integral even at t approaching zero. -/
theorem pullbackForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (pullbackForm_measurable hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pullbackForm_integrable_column hψ hψc hg x ht.1
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| *D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [pullback_column_norm ψ g x ht.1,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma segmentForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (segmentForm_continuous hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ (fun t => segmentForm_integrable_column hψ hψc hg x t)
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| * D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma green_pullback (ψ g : ℂ → ℝ) (x y : ℂ) :
    fderiv ℝ g y (green ψ x y) = -∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y := by
  simp only [green,map_smul,smul_eq_mul,greenScalar,pullbackForm,integral_mul_const,neg_mul]

/-- The true segment-kernel representation, with Fubini justified absolutely. -/
theorem green_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, fderiv ℝ g y (green ψ x y)) = g x-∫ z, ψ z*g z := by
  have hseg := segmentForm_integrable hψ hψc hg hD x
  have hpull := pullbackForm_integrable hψ hψc hg hD x
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hψgi : Integrable (fun z => ψ z*g z) :=
    (hψ.mul hg.continuous).integrable_of_hasCompactSupport hψc.mul_right
  calc
    _ = -(∫ y, ∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y) := by
      simp_rw [green_pullback]; rw [integral_neg]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ y, pullbackForm ψ g x t y) := by
      rw [← integral_integral_swap hpull]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ z, segmentForm ψ g x t z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact pullback_column_integral ψ g x ht.1
    _ = -(∫ z, ∫ t in Ioc (0:ℝ) 1, segmentForm ψ g x t z) := by
      rw [integral_integral_swap hseg]
    _ = -(∫ z, ψ z*(g z-g x)) := by
      simp_rw [segmentForm,integral_const_mul,segment_ftc hg]
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hψgi (hψi.mul_const _),integral_mul_const,hψ1]
      ring

end PlanePotential

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace PlanePotential
lemma lintegral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫⁻ x in ball (0:ℂ) r, ENNReal.ofReal (‖x‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_near ha hr)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) a)),integral_norm_rpow_near ha hr]

lemma lintegral_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    (∫⁻ x : ℂ in {x | r < ‖x‖}, ENNReal.ofReal (‖x‖^a)) =
      ENNReal.ofReal (2*Real.pi*(-r^(a+2)/(a+2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_far ha hr)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) a)),integral_norm_rpow_far ha hr]

lemma lintegral_translated_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) (y : ℂ) :
    (∫⁻ x in ball y r, ENNReal.ofReal (‖x-y‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← lintegral_norm_rpow_near ha hr,← lintegral_indicator measurableSet_ball,
    ← lintegral_indicator measurableSet_ball]
  have heq : (ball y r).indicator (fun x => ENNReal.ofReal (‖x-y‖^a)) =
      fun x => (ball (0:ℂ) r).indicator (fun w => ENNReal.ofReal (‖w‖^a)) (x-y) := by
    funext x
    simp only [indicator,mem_ball,dist_eq_norm,sub_zero]
  rw [heq]
  exact lintegral_add_right_eq_self (fun x : ℂ => (ball 0 r).indicator
    (fun w => ENNReal.ofReal (‖w‖^a)) x) (-y)

lemma lintegral_translated_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) (y : ℂ) :
    (∫⁻ x : ℂ in {x | r < ‖x-y‖}, ENNReal.ofReal (‖x-y‖^a)) =
      ENNReal.ofReal (2*Real.pi*(-r^(a+2)/(a+2))) := by
  rw [← lintegral_norm_rpow_far ha hr,
    ← lintegral_indicator (show MeasurableSet {x : ℂ | r < ‖x-y‖} from measurableSet_lt measurable_const (by fun_prop)),
    ← lintegral_indicator (measurableSet_lt measurable_const measurable_norm)]
  exact lintegral_add_right_eq_self (fun x : ℂ => ({x | r < ‖x‖}).indicator
    (fun w => ENNReal.ofReal (‖w‖^a)) x) (-y)

lemma norm_power_bound {F : ℂ → ℂ} {C q : ℝ} (hC : 0 ≤ C) (x y : ℂ)
    (hF : ‖F x‖ ≤ C*‖x-y‖^q) :
    (ENNReal.ofReal ‖F x‖)^(3/2:ℝ) ≤
      ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(q*(3/2:ℝ))) := by
  calc
    _ = ENNReal.ofReal (‖F x‖^(3/2:ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)
    _ ≤ ENNReal.ofReal ((C*‖x-y‖^q)^(3/2:ℝ)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hF (by norm_num))
    _ = _ := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg _) _),← Real.rpow_mul (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]

lemma kernel_near_three_halves {F : ℂ → ℂ} {E : Set ℂ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (y : ℂ) (hE : E ⊆ ball y r)
    (hF : ∀ x ∈ E, ‖F x‖ ≤ C*‖x-y‖^(-1:ℝ)) :
    (∫⁻ x in E, (ENNReal.ofReal ‖F x‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (C^(3/2:ℝ)*(4*Real.pi*r^(1/2:ℝ))) := by
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      convert norm_power_bound hC x y (hF x hx) using 1
      norm_num
    _ ≤ ∫⁻ x in ball y r, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) :=
      lintegral_mono_set hE
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_translated_near (by norm_num : (-2:ℝ) < -3/2) hr y,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
      congr 1
      norm_num
      exact Or.inl (by ring)

lemma kernel_far_three_halves {F : ℂ → ℂ} {E : Set ℂ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (y : ℂ) (hE : E ⊆ {x | r < ‖x-y‖})
    (hF : ∀ x ∈ E, ‖F x‖ ≤ C*‖x-y‖^(-2:ℝ)) :
    (∫⁻ x in E, (ENNReal.ofReal ‖F x‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (C^(3/2:ℝ)*(2*Real.pi/r)) := by
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3:ℝ)) := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      convert norm_power_bound hC x y (hF x hx) using 1
      norm_num
    _ ≤ ∫⁻ x : ℂ in {x | r < ‖x-y‖}, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3:ℝ)) :=
      lintegral_mono_set hE
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_translated_far (by norm_num : (-3:ℝ) < -2) hr y,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
      congr 1
      norm_num [Real.rpow_neg_one]
      exact Or.inl (by ring)

end PlanePotential

open scoped RealInnerProductSpace
namespace PlanePotential

lemma green_diagonal (ψ : ℂ → ℝ) (x : ℂ) : green ψ x x = 0 := by
  simp [green]

lemma green_size_all {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) :
    ‖green ψ x y‖ ≤ (2*B*(R+X)^2)*‖x-y‖^(-1:ℝ) := by
  by_cases hxy : y = x
  · subst y
    simp [green_diagonal]
  · simpa only [Real.rpow_neg_one,div_eq_mul_inv,norm_sub_rev] using
      green_norm_bound hψm hψs hψB hM hB hx hxy

lemma green_near_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (ha : 0 < a) (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ ‖x-z‖ ≤ 2*a},
      (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 4*a) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have ht := norm_sub_le (x-z) (y-z)
    rw [sub_sub_sub_cancel_right] at ht
    linarith [hx.2]
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx.1

lemma green_far_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖},
      (ENNReal.ofReal ‖green ψ x y-green ψ x z‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a))) := by
  apply kernel_far_three_halves (by positivity) (by positivity : 0 < 2*a) z
  · exact fun _ hx => hx.2
  · intro x hx
    have hzx : z ≠ x := by
      intro h
      have hh := hx.2
      rw [← h,sub_self,norm_zero] at hh
      linarith
    have hn : ‖z-x‖ = ‖x-z‖ := norm_sub_rev z x
    have h := green_difference_bound (x := x) (y := y) (z := z) hψm hψs hψB hψL hM hB hL hx.1 hzx (by
      rw [hn]
      linarith [hx.2])
    rw [hn] at h
    calc
      _ ≤ (8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a/‖x-z‖^2 :=
        h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by positivity)) (sq_nonneg _))
      _ = _ := by
        rw [show ‖x-z‖^(-2:ℝ) = ‖x-z‖^(-2:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
        rfl

/-- The center is subtracted only off the near region, so this measurable
kernel retains integrability at the center and realizes zero-mass cancellation. -/
def cancelledGreen (ψ : ℂ → ℝ) (z : ℂ) (a : ℝ) (x y : ℂ) : ℂ :=
  if ‖x-z‖ ≤ 2*a then green ψ x y else green ψ x y-green ψ x z

lemma cancelledGreen_measurable {ψ : ℂ → ℝ} (hψ : Measurable ψ) (z : ℂ) (a : ℝ) :
    Measurable (fun p : ℂ × ℂ => cancelledGreen ψ z a p.1 p.2) := by
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact green_measurable ψ hψ
  · exact (green_measurable ψ hψ).sub
      ((green_measurable ψ hψ).comp (measurable_fst.prodMk measurable_const))

lemma green_piece_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
    ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a))) := by
  let E := {x : ℂ | ‖x‖ ≤ X}
  let N := {x : ℂ | ‖x-z‖ ≤ 2*a}
  have hN : MeasurableSet N := measurableSet_le (by fun_prop) measurable_const
  have hE : MeasurableSet E := measurableSet_le measurable_norm measurable_const
  have hsplit := lintegral_add_compl (μ := volume.restrict E)
    (fun x => (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ)) hN
  rw [← hsplit]
  have hn : (∫⁻ x in N, (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ) ∂volume.restrict E) =
      ∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ ‖x-z‖ ≤ 2*a}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ) := by
    rw [Measure.restrict_restrict hN,inter_comm]
    apply setLIntegral_congr_fun (hE.inter hN)
    intro x hx
    have hxN : ‖x-z‖ ≤ 2*a := hx.2
    simp only [cancelledGreen,ite_eq_left hxN]
  have hf : (∫⁻ x in Nᶜ, (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ) ∂volume.restrict E) =
      ∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖}, (ENNReal.ofReal ‖green ψ x y-green ψ x z‖)^(3/2:ℝ) := by
    rw [Measure.restrict_restrict hN.compl,inter_comm]
    have he : E ∩ Nᶜ = {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖} := by ext x; simp [E,N]
    rw [he]
    apply setLIntegral_congr_fun ((measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_lt measurable_const ((measurable_id.sub_const z).norm)))
    intro x hx
    have hxF : 2*a < ‖x-z‖ := hx.2
    simp only [cancelledGreen,ite_eq_right (not_le.mpr hxF)]
  rw [hn,hf]
  exact add_le_add (green_near_column hψm hψs hψB hM hB ha z y hy)
    (green_far_column hψm hψs hψB hψL hM hB hL ha z y hy)

end PlanePotential

namespace PlanePotential

theorem kernel_column_lp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α × β → ℝ≥0∞} (hK : Measurable K) {C : ℝ≥0∞}
    (hC : ∀ᵐ y ∂ν, (∫⁻ x, (K (x,y))^(3/2:ℝ) ∂μ) ≤ C) :
    (∫⁻ x, (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ∂μ) ≤ C*(ν univ)^(3/2:ℝ) := by
  have hpq : Real.HolderConjugate (3/2) 3 := by rw [Real.holderConjugate_iff]; norm_num
  have hpoint (x : α) : (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ≤
      (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun y => K (x,y)) (g := fun _ => 1)
      ((hK.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (aemeasurable_const (b := (1:ℝ≥0∞)))
    simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
    have h' := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 3/2)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),← ENNReal.rpow_mul,
      show (1/(3/2:ℝ))*(3/2)=1 by norm_num,
      show (1/(3:ℝ))*(3/2)=1/2 by norm_num,ENNReal.rpow_one,one_mul] using h'
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ y, ∫⁻ x, K (x,y)^(3/2:ℝ) ∂μ ∂ν)*(ν univ)^(1/2:ℝ) := by
      rw [lintegral_mul_const _ (hK.pow_const _).lintegral_prod_right,
        lintegral_lintegral_swap (hK.pow_const _).aemeasurable]
    _ ≤ (C*ν univ)*(ν univ)^(1/2:ℝ) :=
      mul_le_mul_left ((lintegral_mono_ae hC).trans_eq (lintegral_const _)) _
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (ν univ)^(1:ℝ)*(ν univ)^(1/2:ℝ) := by rw [ENNReal.rpow_one]
        _ = (ν univ)^((1:ℝ)+1/2) :=
          (ENNReal.rpow_add_of_nonneg 1 (1/2) (by norm_num) (by norm_num)).symm
        _ = _ := by norm_num

/-- No pointwise integrability assertion for the singular kernel is needed
in this domination: the Bochner integral is bounded by the nonnegative integral. -/
lemma potential_domination {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    ENNReal.ofReal |∫ y, ⟪L y,b y⟫| ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  calc
    _ = ‖∫ y, ⟪L y,b y⟫‖ₑ := by rw [← ofReal_norm,Real.norm_eq_abs]
    _ ≤ ∫⁻ y, ‖⟪L y,b y⟫‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only [Pi.mul_apply]
      rw [← ofReal_norm]
      change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

theorem cancelled_potential_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪cancelledGreen ψ z a x y,β y⟫|)^(3/2:ℝ)) ≤
    (ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
    ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a)))) * (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := cancelledGreen_measurable hψm z a
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
      ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ)*(2*Real.pi/(2*a))))
    (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_piece_column hψm hψs hψB hψL hM hB hL ha z y
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

lemma zero_mass_kernel_shift {L : ℂ → ℂ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (c : ℂ) :
    (∫ y, ⟪L y,β y⟫) = ∫ y, ⟪L y-c,β y⟫ := by
  have hc : Integrable (fun y => ⟪c,β y⟫) := hβ.const_inner c
  have hci : (∫ y, ⟪c,β y⟫) = 0 := by rw [integral_inner hβ,hzero,inner_zero_right]
  simp only [inner_sub_left]
  by_cases hi : Integrable (fun y => ⟪L y,β y⟫)
  · rw [integral_sub hi hc,hci,sub_zero]
  · rw [integral_undef hi,integral_undef]
    intro hs
    have hh := hs.add hc
    change Integrable (fun y => (⟪L y,β y⟫-⟪c,β y⟫)+⟪c,β y⟫) at hh
    simp only [sub_add_cancel] at hh
    exact hi hh

lemma cancelled_potential_eq {ψ : ℂ → ℝ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (z : ℂ) (a : ℝ) (x : ℂ) :
    (∫ y, ⟪green ψ x y,β y⟫) = ∫ y, ⟪cancelledGreen ψ z a x y,β y⟫ := by
  by_cases hx : ‖x-z‖ ≤ 2*a
  · simp only [cancelledGreen,ite_eq_left hx]
  · simp only [cancelledGreen,ite_eq_right hx]
    exact zero_mass_kernel_shift hβ hzero _

/-- Uniform scaling of the exact p-th power column constant: in dimension two
and at p=3/2 its radius dependence is precisely a^(1/2). -/
lemma column_scaling {K D a : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    K^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ)) +
      (D*a)^(3/2:ℝ)*(2*Real.pi/(2*a)) =
      (8*Real.pi*K^(3/2:ℝ)+Real.pi*D^(3/2:ℝ))*a^(1/2:ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) ha.le,Real.mul_rpow hD ha.le]
  have hfour : (4:ℝ)^(1/2:ℝ) = 2 := by norm_num [← Real.sqrt_eq_rpow]
  have hpow : a^(3/2:ℝ)/a = a^(1/2:ℝ) := by
    rw [← Real.rpow_sub_one ha.ne']
    norm_num
  rw [hfour]
  calc
    _ = 8*Real.pi*K^(3/2:ℝ)*a^(1/2:ℝ)+Real.pi*D^(3/2:ℝ)*(a^(3/2:ℝ)/a) := by ring
    _ = _ := by rw [hpow]; ring

theorem green_zero_piece_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hzero : ∫ y, β y = 0)
    (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((8*Real.pi*(2*B*(R+X)^2)^(3/2:ℝ)+
      Real.pi*(8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)^(3/2:ℝ))*a^(1/2:ℝ)) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  simp_rw [cancelled_potential_eq hβ hzero z a]
  have h := cancelled_potential_lp hψm hψs hψB hψL hM hB hL ha z hβ hβs
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    column_scaling (by positivity) ha] at h
  exact h

end PlanePotential

open scoped RealInnerProductSpace
noncomputable section

end
end

end OAI
