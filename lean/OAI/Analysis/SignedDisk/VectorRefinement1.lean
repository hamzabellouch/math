import OAI.Analysis.SignedDisk.PlanePotential1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace VectorRefinement

/-- Exact quadratic defect of a positive vector refinement, including zero parent mass. -/
theorem quadratic_defect {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w a : ι → ℝ) (θ : ι → E) (n : E) (A : ℝ)
    (hn : ‖n‖ = 1) (hθ : ∀ i, ‖θ i‖ = 1)
    (href : A • n = ∑ i, (w i*a i) • θ i) :
    (∑ i, w i*a i)-A = (1/2:ℝ)*∑ i, w i*a i*‖θ i-n‖^2 := by
  have hinner : A = ∑ i, w i*a i*⟪θ i,n⟫ := by
    have h := congrArg (fun v : E => ⟪v,n⟫) href
    simpa only [real_inner_smul_left,sum_inner,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] using h
  rw [hinner,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_sub_sq_real,hθ i,hn]
  ring

lemma sq_norm_triangle {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x-z‖^2 ≤ 2*(‖x-y‖^2+‖z-y‖^2) := by
  have h := norm_sub_le_norm_sub_add_norm_sub x y z
  rw [norm_sub_rev y z] at h
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
  nlinarith [sq_nonneg (‖x-y‖-‖z-y‖)]

/-- Two sufficiently represented children cannot have a large angular disagreement
without spending the actual parent's triangle defect. -/
theorem pair_defect_bound {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w a : ι → ℝ) (θ : ι → E) (n : E) (A : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    (hn : ‖n‖ = 1) (hθ : ∀ i, ‖θ i‖ = 1)
    (href : A • n = ∑ i, (w i*a i) • θ i)
    {q s : ι} (hwaq : 1/4 ≤ w q) (hwas : 9/64 ≤ w s) (has : a q ≤ a s) :
    a q*‖θ q-θ s‖^2 ≤ 48*((∑ i, w i*a i)-A) := by
  let D := (∑ i, w i*a i)-A
  have hD := quadratic_defect w a θ n A hn hθ href
  have hi (i : ι) : w i*a i*‖θ i-n‖^2 ≤ 2*D := by
    have hs : w i*a i*‖θ i-n‖^2 ≤ ∑ j, w j*a j*‖θ j-n‖^2 :=
      Finset.single_le_sum (fun j _ => mul_nonneg (mul_nonneg (hw j) (ha j)) (sq_nonneg ‖θ j-n‖)) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hD0 : 0 ≤ D := by
    have hs : 0 ≤ ∑ i, w i*a i*‖θ i-n‖^2 := Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hw i) (ha i)) (sq_nonneg _)
    dsimp [D]; linarith
  have hq : a q*‖θ q-n‖^2 ≤ 8*D := by
    have hm := mul_le_mul_of_nonneg_right hwaq (mul_nonneg (ha q) (sq_nonneg ‖θ q-n‖))
    nlinarith [hi q]
  have hs : a q*‖θ s-n‖^2 ≤ (128/9:ℝ)*D := by
    have hm := mul_le_mul_of_nonneg_right hwas (mul_nonneg (ha s) (sq_nonneg ‖θ s-n‖))
    have hmas := mul_le_mul_of_nonneg_right has (sq_nonneg ‖θ s-n‖)
    nlinarith [hi s]
  have ht := mul_le_mul_of_nonneg_left (sq_norm_triangle (θ q) n (θ s)) (ha q)
  change _ ≤ 48*D
  nlinarith

end VectorRefinement

open MeasureTheory Set
open scoped ENNReal NNReal Topology

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

end SignedDisk

end

end OAI
