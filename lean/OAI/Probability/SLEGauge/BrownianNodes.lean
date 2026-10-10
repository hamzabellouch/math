import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.InverseRegularity

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.BrownianCalculus
open scoped ContinuousMapZero
variable {W : Measure Driver} (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
include hW
lemma increment_indep_history (s h : ℝ≥0) : IndepFun (increment s h) (history s) W := by
  have hi := (hW.toIsPreBrownianReal.indepFun_shift s).comp
    (measurable_pi_apply h) measurable_id
  exact hi

lemma increment_indep_past_function (s h : ℝ≥0) {F : (Iic s → ℝ) → ℝ}
    (hF : Measurable F) : IndepFun (increment s h) (F ∘ history s) W := by
  exact (increment_indep_history hW s h).comp measurable_id hF

lemma predictable_increment_centered (s h : ℝ≥0) {F : (Iic s → ℝ) → ℝ}
    (hF : Measurable F) :
    (∫ b, F (history s b) * increment s h b ∂W) = 0 := by
  have hi := (increment_indep_past_function hW s h hF).symm
  have hh := hi.integral_mul_eq_mul_integral
    (hF.comp (measurable_history s)).aestronglyMeasurable
    (measurable_increment s h).aestronglyMeasurable
  change (∫ b, F (history s b) * increment s h b ∂W) =
    (∫ b, F (history s b) ∂W) * (∫ b, increment s h b ∂W) at hh
  rw [hh, increment_mean hW, mul_zero]

lemma increment_pow_integrable (s h : ℝ≥0) (n : ℕ) :
    Integrable (fun b => (increment s h b)^n) W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hm := (increment_law hW s h).hasGaussianLaw.memLp (p := (n : ℝ≥0∞)) (by simp)
  apply (integrable_norm_iff ((measurable_increment s h).pow_const n).aestronglyMeasurable).mp
  simpa only [norm_pow] using hm.integrable_norm_pow'

lemma predictable_innovation_centered (s h : ℝ≥0) {F : (Iic s → ℝ) → ℝ}
    (hF : Measurable F) {J : ℝ → ℝ} (hJ : Measurable J)
    (hmean : (∫ x, J x ∂gaussianReal 0 h) = 0) :
    (∫ b, F (history s b) * J (increment s h b) ∂W) = 0 := by
  have hi := (increment_indep_history hW s h).comp hJ hF
  have hh := hi.symm.integral_mul_eq_mul_integral
    (hF.comp (measurable_history s)).aestronglyMeasurable
    (hJ.comp (measurable_increment s h)).aestronglyMeasurable
  change (∫ b, F (history s b) * J (increment s h b) ∂W) =
    (∫ b, F (history s b) ∂W) * (∫ b, J (increment s h b) ∂W) at hh
  have hm : (∫ b, J (increment s h b) ∂W) = 0 := by
    exact ((increment_law hW s h).integral_comp hJ.aestronglyMeasurable).trans hmean
  rw [hh, hm, mul_zero]

lemma predictable_compensated_square_centered (s h : ℝ≥0)
    {F : (Iic s → ℝ) → ℝ} (hF : Measurable F) :
    (∫ b, F (history s b) * ((increment s h b)^2 - (h:ℝ)) ∂W) = 0 := by
  apply predictable_innovation_centered hW s h hF (J := fun x : ℝ => x^2-(h:ℝ)) (by fun_prop)
  have hi : Integrable (fun x : ℝ => x^2) (gaussianReal 0 h) := by
    simpa only [id_eq] using (memLp_id_gaussianReal (μ := 0) (v := h) 2).integrable_sq
  rw [integral_sub hi (integrable_const (h:ℝ)), integral_sq_gaussian]
  simp

lemma increment_abs_cube_integrable (s h : ℝ≥0) :
    Integrable (fun b => |increment s h b|^3) W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hm := (increment_law hW s h).hasGaussianLaw.memLp (p := (3 : ℝ≥0∞)) (by simp)
  simpa only [Real.norm_eq_abs] using hm.integrable_norm_pow' (p := 3)

omit hW in
lemma abs_cube_bound {h x : ℝ} (hh : 0 < h) :
    |x|^3 ≤ (h*x^2 + x^4) / (2*Real.sqrt h) := by
  have hr := Real.sqrt_pos.mpr hh
  have hs := Real.sq_sqrt hh.le
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt h)).mpr
  have hx4 : |x|^4 = x^4 := by
    calc |x|^4 = (|x|^2)^2 := by ring
         _ = (x^2)^2 := by rw [sq_abs]
         _ = x^4 := by ring
  have he : h*x^2 + x^4 - |x|^3*(2*Real.sqrt h) =
      (|x|^2 - Real.sqrt h*|x|)^2 := by
    calc
      _ = (Real.sqrt h)^2*|x|^2 + |x|^4 - |x|^3*(2*Real.sqrt h) := by
        rw [hs, sq_abs, hx4]
      _ = _ := by ring
  linarith [sq_nonneg (|x|^2-Real.sqrt h*|x|)]

lemma increment_abs_cube_le (s h : ℝ≥0) :
    (∫ b, |increment s h b|^3 ∂W) ≤ 2*(h:ℝ)*Real.sqrt h := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  by_cases hh : h = 0
  · subst h
    simp [increment]
  have hp : 0 < (h:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
  have hr := Real.sqrt_pos.mpr hp
  have hi2 := increment_pow_integrable hW s h 2
  have hi4 := increment_pow_integrable hW s h 4
  have hm := integral_mono (increment_abs_cube_integrable hW s h)
    (((hi2.const_mul (h:ℝ)).add hi4).div_const (2*Real.sqrt h))
    (fun b => abs_cube_bound (x := increment s h b) hp)
  have he : (∫ b, ((h:ℝ)*(increment s h b)^2+(increment s h b)^4) /
      (2*Real.sqrt h) ∂W) = 2*(h:ℝ)*Real.sqrt h := by
    rw [integral_div, integral_add (hi2.const_mul _) hi4, integral_const_mul,
      increment_sq hW, increment_fourth hW]
    apply (div_eq_iff (by positivity : 2*Real.sqrt (h:ℝ) ≠ 0)).mpr
    nlinarith [Real.sq_sqrt hp.le]
  exact hm.trans_eq he

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus

lemma taylor_second_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {C : ℝ} (hC : ∀ z, |iteratedDeriv 3 f z| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x*(y-x) - deriv (deriv f) x*(y-x)^2/2| ≤
      C/6 * |y-x|^3 := by
  by_cases heq : x = y
  · subst y
    simp
  have hc : ContDiffOn ℝ (2+1 : ℕ) f (uIcc x y) := hf.contDiffOn
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) heq hc
  have hi (k : ℕ) (hk : k ≤ 2) :
      iteratedDerivWithin k f (uIcc x y) x = iteratedDeriv k f x := by
    apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc heq)
    · exact (hf.of_le (by norm_cast; omega)).contDiffAt
    · exact left_mem_uIcc
  have ht : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x*(y-x) + deriv (deriv f) x*(y-x)^2/2 := by
    simp only [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, hi 0 (by omega), hi 1 (by omega), hi 2 (by omega)]
    norm_num [iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  have he' : f y - f x - deriv f x*(y-x) - deriv (deriv f) x*(y-x)^2/2 =
      iteratedDeriv 3 f z * (y-x)^3 / 6 := by
    rw [ht] at he
    norm_num at he
    linarith
  rw [he', abs_div, abs_mul, abs_pow]
  norm_num
  calc |iteratedDeriv 3 f z| * |y-x|^3 / 6 ≤ C * |y-x|^3 / 6 := by gcongr; exact hC z
       _ = _ := by ring

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus

 

lemma expected_taylor_step {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s h : ℝ≥0) (f : (Iic s → ℝ) → ℝ → ℝ)
    (hsm : ∀ p, ContDiff ℝ 3 (f p))
    (hm1 : Measurable (fun p => deriv (f p) (p ⟨s, by simp⟩)))
    (hm2 : Measurable (fun p => deriv (deriv (f p)) (p ⟨s, by simp⟩)))
    {C M₁ M₂ : ℝ} (hC : 0 ≤ C)
    (hb1 : ∀ p, |deriv (f p) (p ⟨s, by simp⟩)| ≤ M₁)
    (hb2 : ∀ p, |deriv (deriv (f p)) (p ⟨s, by simp⟩)| ≤ M₂)
    (hb3 : ∀ p x, |iteratedDeriv 3 (f p) x| ≤ C)
    (hi : Integrable (fun b => f (history s b) (b (s+h)) - f (history s b) (b s)) W) :
    |(∫ b, f (history s b) (b (s+h)) - f (history s b) (b s) ∂W) -
      (h:ℝ)/2 * (∫ b, deriv (deriv (f (history s b))) (b s) ∂W)| ≤
      C/3 * (h:ℝ) * Real.sqrt h := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let A₁ := fun p : Iic s → ℝ => deriv (f p) (p ⟨s, by simp⟩)
  let A₂ := fun p : Iic s → ℝ => deriv (deriv (f p)) (p ⟨s, by simp⟩)
  have ha₁ : AEStronglyMeasurable (fun b => A₁ (history s b)) W :=
    (hm1.comp (measurable_history s)).aestronglyMeasurable
  have ha₂ : AEStronglyMeasurable (fun b => A₂ (history s b)) W :=
    (hm2.comp (measurable_history s)).aestronglyMeasurable
  have i₁ : Integrable (fun b => A₁ (history s b)*increment s h b) W := by
    have hg : Integrable (increment s h) W := by
      simpa only [pow_one] using increment_pow_integrable hW s h 1
    exact hg.bdd_mul ha₁ (Filter.Eventually.of_forall fun b => by
      simpa only [Real.norm_eq_abs] using hb1 (history s b))
  have i₂ : Integrable (fun b => A₂ (history s b)*(increment s h b)^2) W :=
    (increment_pow_integrable hW s h 2).bdd_mul ha₂
      (Filter.Eventually.of_forall fun b => by
        simpa only [Real.norm_eq_abs] using hb2 (history s b))
  have ia₂ : Integrable (fun b => A₂ (history s b)) W :=
    (integrable_const M₂).mono' ha₂ (Filter.Eventually.of_forall fun b => by
      simpa only [Real.norm_eq_abs] using hb2 (history s b))
  have e₂ : (∫ b, A₂ (history s b)*(increment s h b)^2 ∂W) =
      (h:ℝ)*(∫ b, A₂ (history s b) ∂W) := by
    have hh := predictable_compensated_square_centered hW s h hm2
    change (∫ b, A₂ (history s b)*((increment s h b)^2-(h:ℝ)) ∂W) = 0 at hh
    simp_rw [mul_sub] at hh
    rw [integral_sub i₂ (ia₂.mul_const (h:ℝ)), integral_mul_const] at hh
    linarith
  let R := fun b => f (history s b) (b (s+h)) - f (history s b) (b s) -
    A₁ (history s b)*increment s h b - A₂ (history s b)*(increment s h b)^2/2
  have he : (∫ b, R b ∂W) =
      (∫ b, f (history s b) (b (s+h)) - f (history s b) (b s) ∂W) -
        (h:ℝ)/2*(∫ b, deriv (deriv (f (history s b))) (b s) ∂W) := by
    dsimp only [R]
    have hs1 := integral_sub hi i₁
    have hs2 := integral_sub (hi.sub i₁) (i₂.div_const 2)
    simp only [Pi.sub_apply] at hs1 hs2
    rw [hs2, hs1, predictable_increment_centered hW s h hm1, integral_div, e₂]
    dsimp only [A₂, history]
    ring
  rw [← he]
  have hb (b : Driver) : ‖R b‖ ≤ C/6 * |increment s h b|^3 := by
    simpa only [R, A₁, A₂, history, increment, Real.norm_eq_abs] using
      taylor_second_bound (hsm (history s b)) (hb3 (history s b)) (b s) (b (s+h))
  have hiR := (increment_abs_cube_integrable hW s h).const_mul (C/6)
  have hbR := norm_integral_le_of_norm_le hiR (Filter.Eventually.of_forall hb)
  rw [Real.norm_eq_abs, integral_const_mul] at hbR
  calc
    _ ≤ C/6 * (∫ b, |increment s h b|^3 ∂W) := hbR
    _ ≤ C/6 * (2*(h:ℝ)*Real.sqrt h) := by
      gcongr
      exact increment_abs_cube_le hW s h
    _ = _ := by ring

end SLEExactGauge.BrownianCalculus

 

noncomputable section
open Set
namespace SLEExactGauge.BrownianCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma state_taylor_bound {F : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hD : ∀ x, HasFDerivAt F (D x) x) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x y, ‖D x-D y‖ ≤ C*‖x-y‖) (x v : E) :
    |F (x+v)-F x-D x v| ≤ C*‖v‖^2 := by
  let f : ℝ → ℝ := fun t => F (x+t • v)-t*(D x v)
  have hd (t : ℝ) : HasDerivAt f ((D (x+t • v)-D x) v) t := by
    have hh := (hD (x+t • v)).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v).const_add x)
    have hk := hh.sub ((hasDerivAt_id t).mul_const (D x v))
    convert! hk using 1
    simp
  have hb (t : ℝ) (ht : t ∈ Icc 0 1) : ‖(D (x+t • v)-D x) v‖ ≤ C*‖v‖^2 := by
    calc _ ≤ ‖D (x+t • v)-D x‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C*‖(x+t • v)-x‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)
      _ = C*(t*‖v‖)*‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ = t*(C*‖v‖^2) := by ring
      _ ≤ 1*(C*‖v‖^2) := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hC (sq_nonneg _))
      _ = _ := one_mul _
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Icc (0:ℝ) 1) => (hd t).hasDerivWithinAt) hb
    (convex_Icc (0:ℝ) 1) (by simp : (0:ℝ) ∈ Icc 0 1) (by simp : (1:ℝ) ∈ Icc 0 1)
  simp only [f, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero,
    Real.norm_eq_abs, abs_one, mul_one] at hh
  convert! hh using 1
  congr 1
  ring

lemma state_euler_remainder {F : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hD : ∀ x, HasFDerivAt F (D x) x) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x y, ‖D x-D y‖ ≤ C*‖x-y‖) (x v : E) {M h : ℝ}
    (hh : 0 ≤ h) (hv : ‖v‖ ≤ M) :
    F (x+h • v)-F x ≤ h*(D x v) + C*M^2*h^2 := by
  have hb := (le_abs_self _).trans (state_taylor_bound hD hC hLip x (h • v))
  rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh] at hb
  have hM : 0 ≤ M := (norm_nonneg v).trans hv
  have hn : ‖v‖^2 ≤ M^2 := by nlinarith [norm_nonneg v]
  have hh' := mul_le_mul_of_nonneg_left hn (mul_nonneg hC (sq_nonneg h))
  nlinarith

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

theorem expected_euler_step {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s h : ℝ≥0) (F : E → ℝ → ℝ) (D : E → ℝ → E →L[ℝ] ℝ)
    (X V : (Iic s → ℝ) → E)
    (mF : Measurable (Function.uncurry F))
    (mB1 : Measurable (fun q : E × ℝ => deriv (F q.1) q.2))
    (mB2 : Measurable (fun q : E × ℝ => deriv (deriv (F q.1)) q.2))
    (mX : Measurable X) (mV : Measurable V)
    (hD : ∀ x b, HasFDerivAt (fun y => F y b) (D x b) x)
    (hsm : ∀ x, ContDiff ℝ 3 (F x))
    {C₀ C₁ C₂ C₃ Cx Ccross M : ℝ}
    (hC₃ : 0 ≤ C₃) (hCx : 0 ≤ Cx) (hCcross : 0 ≤ Ccross)
    (hF : ∀ x b, |F x b| ≤ C₀)
    (hB1 : ∀ x b, |deriv (F x) b| ≤ C₁)
    (hB2 : ∀ x b, |deriv (deriv (F x)) b| ≤ C₂)
    (hB3 : ∀ x b, |iteratedDeriv 3 (F x) b| ≤ C₃)
    (hLipD : ∀ x y b, ‖D x b-D y b‖ ≤ Cx*‖x-y‖)
    (hLipB2 : ∀ x y b, |deriv (deriv (F x)) b-deriv (deriv (F y)) b| ≤ Ccross*‖x-y‖)
    (hV : ∀ p, ‖V p‖ ≤ M)
    (hgen : ∀ p, D (X p) (p ⟨s,by simp⟩) (V p) +
      deriv (deriv (F (X p))) (p ⟨s,by simp⟩)/2 ≤ 0) :
    (∫ b, F (X (history s b)+(h:ℝ) • V (history s b)) (b (s+h)) -
      F (X (history s b)) (b s) ∂W) ≤
        (Cx*M^2+Ccross*M/2)*(h:ℝ)^2 + C₃/3*(h:ℝ)*Real.sqrt h := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let Y := fun p => X p+(h:ℝ) • V p
  have mY : Measurable Y := mX.add (mV.const_smul (h:ℝ))
  let f := fun p v => F (Y p) v
  let old := fun b : Driver => F (X (history s b)) (b s)
  let step := fun b : Driver => F (Y (history s b)) (b s)
  let next := fun b : Driver => F (Y (history s b)) (b (s+h))
  have mOld : Measurable old := mF.comp ((mX.comp (measurable_history s)).prodMk
    ((continuous_eval_const s).measurable))
  have mStep : Measurable step := mF.comp ((mY.comp (measurable_history s)).prodMk
    ((continuous_eval_const s).measurable))
  have mNext : Measurable next := mF.comp ((mY.comp (measurable_history s)).prodMk
    ((continuous_eval_const (s+h)).measurable))
  have iOld : Integrable old W := (integrable_const C₀).mono' mOld.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hF _ _)
  have iStep : Integrable step W := (integrable_const C₀).mono' mStep.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hF _ _)
  have iNext : Integrable next W := (integrable_const C₀).mono' mNext.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hF _ _)
  let Q := fun b : Driver => deriv (deriv (F (Y (history s b)))) (b s)
  have mQ : Measurable Q := mB2.comp ((mY.comp (measurable_history s)).prodMk
    ((continuous_eval_const s).measurable))
  have iQ : Integrable Q W := (integrable_const C₂).mono' mQ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hB2 _ _)
  have hm1 : Measurable (fun p => deriv (f p) (p ⟨s,by simp⟩)) :=
    mB1.comp (mY.prodMk (measurable_pi_apply _))
  have hm2 : Measurable (fun p => deriv (deriv (f p)) (p ⟨s,by simp⟩)) :=
    mB2.comp (mY.prodMk (measurable_pi_apply _))
  have ht := expected_taylor_step hW s h f (fun p => hsm (Y p)) hm1 hm2 hC₃
    (fun p => hB1 _ _) (fun p => hB2 _ _) (fun p v => hB3 _ _) (iNext.sub iStep)
  change |(∫ b, next b-step b ∂W)-(h:ℝ)/2*(∫ b, Q b ∂W)| ≤ _ at ht
  have hp (b : Driver) : step b-old b+(h:ℝ)/2*Q b ≤
      (Cx*M^2+Ccross*M/2)*(h:ℝ)^2 := by
    let p := history s b
    have hs : p ⟨s,by simp⟩ = b s := rfl
    have hy : ‖Y p-X p‖ ≤ (h:ℝ)*M := by
      simp only [Y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg h.coe_nonneg]
      exact mul_le_mul_of_nonneg_left (hV p) h.coe_nonneg
    have hd := state_euler_remainder (fun x => hD x (b s)) hCx
      (fun x y => hLipD x y (b s)) (X p) (V p) h.coe_nonneg (hV p)
    have hb := (le_abs_self _).trans (hLipB2 (Y p) (X p) (b s))
    have hcross := hb.trans (mul_le_mul_of_nonneg_left hy hCcross)
    have hg := hgen p
    rw [hs] at hg
    have hg' := mul_nonpos_of_nonneg_of_nonpos h.coe_nonneg hg
    have hc' := mul_le_mul_of_nonneg_left hcross (div_nonneg h.coe_nonneg (by norm_num : (0:ℝ) ≤ 2))
    dsimp only [step, old, Q]
    change F (Y p) (b s)-F (X p) (b s)+(h:ℝ)/2*deriv (deriv (F (Y p))) (b s) ≤ _
    dsimp only [Y] at hd ⊢
    nlinarith
  have hib : (∫ b, step b-old b+(h:ℝ)/2*Q b ∂W) ≤
      (Cx*M^2+Ccross*M/2)*(h:ℝ)^2 := by
    have hh := integral_mono_ae ((iStep.sub iOld).add (iQ.const_mul ((h:ℝ)/2)))
      (integrable_const ((Cx*M^2+Ccross*M/2)*(h:ℝ)^2)) (Filter.Eventually.of_forall hp)
    simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, Pi.add_apply, Pi.sub_apply] using hh
  change (∫ b, (step-old) b+((h:ℝ)/2*Q b) ∂W) ≤ _ at hib
  rw [integral_add (iStep.sub iOld) (iQ.const_mul ((h:ℝ)/2)), integral_const_mul] at hib
  change (∫ b, step b-old b ∂W)+(h:ℝ)/2*(∫ b, Q b ∂W) ≤ _ at hib
  rw [integral_sub iStep iOld] at hib
  rw [integral_sub iNext iStep] at ht
  change (∫ b, next b-old b ∂W) ≤ _
  rw [integral_sub iNext iOld]
  linarith [le_abs_self ((∫ b, next b ∂W)-(∫ b, step b ∂W)-(h:ℝ)/2*(∫ b, Q b ∂W))]

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

structure SmoothTest (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] where
  F : E → ℝ → ℝ
  D : E → ℝ → E →L[ℝ] ℝ
  C₀ : ℝ
  C₁ : ℝ
  C₂ : ℝ
  C₃ : ℝ
  Cx : ℝ
  Ccross : ℝ
  hC₃ : 0 ≤ C₃
  hCx : 0 ≤ Cx
  hCcross : 0 ≤ Ccross
  cF : Continuous (Function.uncurry F)
  mF : Measurable (Function.uncurry F)
  mB1 : Measurable (fun q : E × ℝ => deriv (F q.1) q.2)
  mB2 : Measurable (fun q : E × ℝ => deriv (deriv (F q.1)) q.2)
  hD : ∀ x b, HasFDerivAt (fun y => F y b) (D x b) x
  hsm : ∀ x, ContDiff ℝ 3 (F x)
  hF : ∀ x b, |F x b| ≤ C₀
  hB1 : ∀ x b, |deriv (F x) b| ≤ C₁
  hB2 : ∀ x b, |deriv (deriv (F x)) b| ≤ C₂
  hB3 : ∀ x b, |iteratedDeriv 3 (F x) b| ≤ C₃
  hLipD : ∀ x y b, ‖D x b-D y b‖ ≤ Cx*‖x-y‖
  hLipB2 : ∀ x y b, |deriv (deriv (F x)) b-deriv (deriv (F y)) b| ≤ Ccross*‖x-y‖

def extendHistory (s : ℝ≥0) (p : Iic s → ℝ) (t : ℝ≥0) : ℝ :=
  if ht : t ≤ s then p ⟨t,ht⟩ else 0

lemma measurable_extendHistory (s : ℝ≥0) : Measurable (extendHistory s) := by
  apply Measurable.of_eval
  intro t
  by_cases ht : t ≤ s
  · simpa only [extendHistory, dite_eq_left ht] using (measurable_pi_apply (⟨t,ht⟩ : Iic s))
  · simp only [extendHistory, dite_eq_right ht]
    exact measurable_const

 
def stochasticNodes (v : E → ℝ → E) (h : ℝ≥0) (x : E) : ℕ → (ℝ≥0 → ℝ) → E
  | 0, _ => x
  | k+1, b => stochasticNodes v h x k b + (h:ℝ) •
      v (stochasticNodes v h x k b) (b ((k:ℝ≥0)*h))

lemma measurable_stochasticNodes (v : E → ℝ → E)
    (hv : Measurable (Function.uncurry v)) (h : ℝ≥0) (x : E) (k : ℕ) :
    Measurable (stochasticNodes v h x k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact ih.add ((hv.comp (ih.prodMk (measurable_pi_apply _))).const_smul (h:ℝ))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma stochasticNodes_congr (v : E → ℝ → E) (h : ℝ≥0) (x : E) (k : ℕ)
    {b c : ℝ≥0 → ℝ} (he : ∀ t ≤ (k:ℝ≥0)*h, b t = c t) :
    stochasticNodes v h x k b = stochasticNodes v h x k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hle : (k:ℝ≥0)*h ≤ ((k+1:ℕ):ℝ≥0)*h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) h.coe_nonneg
    have hn := ih (fun t ht => he t (ht.trans hle))
    simp only [stochasticNodes, hn, he _ hle]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma stochasticNodes_history (v : E → ℝ → E) (h : ℝ≥0) (x : E) (k : ℕ)
    (b : Driver) :
    stochasticNodes v h x k (extendHistory ((k:ℝ≥0)*h) (history ((k:ℝ≥0)*h) b)) =
      stochasticNodes v h x k b := by
  apply stochasticNodes_congr
  intro t ht
  simp only [extendHistory, dite_eq_left ht, history]

end SLEExactGauge.BrownianCalculus
end
end
end
end
end
end

end OAI
