import Mathlib
import OAI.Probability.SphericalField.Heat.TerminalDerivative

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

@[simp] lemma shiftBCF_apply (f : ℝ →ᵇ ℝ) (a x : ℝ) : shiftBCF f a x = f (x+a) := rfl

lemma shiftBCF_norm_le (f : ℝ →ᵇ ℝ) (a : ℝ) : ‖shiftBCF f a‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm (x+a))

lemma shiftBCF_lipschitz (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) :
    LipschitzWith ‖f'‖₊ (shiftBCF f) := by
  have hl := lipschitzWith_of_nnnorm_deriv_le (C := ‖f'‖₊) (fun x => (hf x).differentiableAt) (fun x => by
    rw [(hf x).deriv]
    exact_mod_cast f'.norm_coe_le_norm x)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change |f (x+a)-f (x+b)| ≤ _
  simpa only [Real.dist_eq,add_sub_add_left_eq_sub,coe_nnnorm] using hl.dist_le_mul (x+a) (x+b)

lemma shiftBCF_Jet3_hasDerivAt (g : Jet3) (a : ℝ) :
    HasDerivAt (shiftBCF g.f) (shiftBCF g.d1 a) a := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < ε/(‖g.d2‖+1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show 0 < ε/(‖g.d2‖+1) by positivity)] with h hh
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
  filter_upwards [he] with h hh
  have hb : ‖shiftBCF g.f (a+h)-shiftBCF g.f a-h • shiftBCF g.d1 a‖ ≤ ‖g.d2‖*h^2/2 := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    have ht := first_order_taylor_bound (g.contDiff.of_le (by norm_num)) ‖g.d2‖
      (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y) (x+a) (x+(a+h))
    rw [g.deriv_eq] at ht
    convert! ht using 1 <;> simp [shiftBCF,add_comm,add_left_comm,mul_comm]
  calc
    _ ≤ ‖g.d2‖*h^2/2 := hb
    _ ≤ ε*‖h‖ := by
      have ht : |h| * (‖g.d2‖+1) < ε := (lt_div_iff₀ (by positivity)).mp hh
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs h,abs_nonneg h,norm_nonneg g.d2,
        mul_nonneg (abs_nonneg h) (sub_nonneg.mpr ht.le)]

lemma shiftBCF_gaussian_integrable (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) (a : ℝ) :
    Integrable (fun z => shiftBCF f (a*z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound ((shiftBCF_lipschitz f f' hf).continuous.comp
    (continuous_const.mul continuous_id)).aestronglyMeasurable ‖f‖
  exact ae_of_all _ (fun z => shiftBCF_norm_le f (a*z))

lemma gaussianAverage_scaling (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s f x = ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt s)^2, sq_nonneg _⟩ : ℝ≥0) = s := by
    ext; exact Real.sq_sqrt s.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt s)
  simp only [mul_zero,NNReal.mk] at hL
  rw [hv,mul_one] at hL
  exact (hL.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun z => f (x+z)) (gaussianReal 0 s))).symm

lemma gaussianAverageBCF_scaling (s : ℝ≥0) (g : Jet3) :
    gaussianAverageBCF s g.f = ∫ z, shiftBCF g.f (Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hi := shiftBCF_gaussian_integrable g.f g.d1 g.has1 (Real.sqrt s)
  ext x
  have he := (BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm hi
  change gaussianAverage s g.f x = _
  rw [gaussianAverage_scaling]
  exact he

lemma gaussianAverageBCF_time_hasDerivAt (g : Jet3) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => gaussianAverageBCF t.toNNReal g.f)
      ((1/2 : ℝ) • gaussianAverageBCF s.toNNReal g.d2) s := by
  let F : ℝ → ℝ → (ℝ →ᵇ ℝ) := fun t z => shiftBCF g.f (Real.sqrt t*z)
  let D : ℝ → ℝ → (ℝ →ᵇ ℝ) := fun t z =>
    (z / (2*Real.sqrt t)) • shiftBCF g.d1 (Real.sqrt t*z)
  have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
    simpa only [pow_one,id_eq] using gaussian_law_integrable_abs_pow
      (HasLaw.id (μ := gaussianReal 0 1)) 1
  have hm (t : ℝ) : AEStronglyMeasurable (F t) (gaussianReal 0 1) := by
    exact (shiftBCF_gaussian_integrable g.f g.d1 g.has1 (Real.sqrt t)).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (D s) (gaussianReal 0 1) := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_id.div_const _).smul ((shiftBCF_lipschitz g.d1 g.d2 g.has2).continuous.comp
      (continuous_const.mul continuous_id))
  have hb : ∀ᵐ z ∂gaussianReal 0 1, ∀ t ∈ Set.Ioo (s/2) (2*s),
      ‖D t z‖ ≤ |z| / (2*Real.sqrt (s/2)) * ‖g.d1‖ := by
    apply ae_of_all
    intro z t ht
    have ht0 : 0 < t := by linarith [ht.1]
    dsimp [D]
    rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt t)]
    apply mul_le_mul (div_le_div_of_nonneg_left (abs_nonneg z) (by positivity)
      (by gcongr; exact ht.1.le)) (shiftBCF_norm_le _ _) (norm_nonneg _) (by positivity)
  have hd : ∀ᵐ z ∂gaussianReal 0 1, ∀ t ∈ Set.Ioo (s/2) (2*s),
      HasDerivAt (fun t => F t z) (D t z) t := by
    apply ae_of_all
    intro z t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hh := (shiftBCF_Jet3_hasDerivAt g (Real.sqrt t*z)).scomp t
      ((Real.hasDerivAt_sqrt ht0).mul_const z)
    simpa only [F,D,Function.comp_def,div_eq_mul_inv,_root_.mul_inv_rev,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : s/2 < s) (by linarith : s < 2*s))
    (Filter.Eventually.of_forall hm)
    (shiftBCF_gaussian_integrable g.f g.d1 g.has1 (Real.sqrt s))
    hdm hb ((hz.div_const _).mul_const ‖g.d1‖) hd
  have he : (∫ z, D s z ∂gaussianReal 0 1) =
      (1/2 : ℝ) • gaussianAverageBCF s.toNNReal g.d2 := by
    ext x
    have hev := (BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm hh.1
    have hib := standardGaussian_integrationByParts
      (F := fun z => g.d1 (x+Real.sqrt s*z))
      (F' := fun z => Real.sqrt s*g.d2 (x+Real.sqrt s*z))
      (C := ‖g.d1‖) (D := Real.sqrt s*‖g.d2‖)
      (fun z => by
        have h := (g.has2 (x+Real.sqrt s*z)).comp z
          (((hasDerivAt_id z).const_mul (Real.sqrt s)).const_add x)
        simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using h)
      (by fun_prop)
      (fun z => by simpa only [Real.norm_eq_abs] using g.d1.norm_coe_le_norm (x+Real.sqrt s*z))
      (fun z => by
        rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_left (g.d2.norm_coe_le_norm (x+Real.sqrt s*z))
          (Real.sqrt_nonneg _))
    change (∫ z, (D s z) x ∂gaussianReal 0 1) = (∫ z,D s z ∂gaussianReal 0 1) x at hev
    rw [← hev]
    change (∫ z, z/(2*Real.sqrt s)*g.d1 (x+Real.sqrt s*z) ∂gaussianReal 0 1) =
      (1/2)*gaussianAverage s.toNNReal g.d2 x
    rw [gaussianAverage_scaling,Real.coe_toNNReal s hs.le]
    have hc : (∫ z, z/(2*Real.sqrt s)*g.d1 (x+Real.sqrt s*z) ∂gaussianReal 0 1) =
        (2*Real.sqrt s)⁻¹ * ∫ z, z*g.d1 (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
      rw [← integral_const_mul]; congr 1; ext z; ring
    rw [hc,hib,integral_const_mul]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hs)]
  rw [he] at hh
  apply hh.2.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  exact (gaussianAverageBCF_scaling t.toNNReal g).trans (by rw [Real.coe_toNNReal t ht.le])

lemma log_lipschitz_above {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b-Real.log a| ≤ c⁻¹*|b-a| := by
  apply (convex_Ici c).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (Real.hasDerivAt_log (ne_of_gt (hc.trans_le hx))).hasDerivWithinAt)
    (fun x hx => ?_) ha hb
  rw [Real.norm_eq_abs,abs_inv,abs_of_pos (hc.trans_le hx)]
  exact inv_anti₀ hc hx

lemma heatLogBCF_time_continuousAt (g : Jet3) (d : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    ContinuousAt (fun t : ℝ => heatLogBCF t.toNNReal d g.f) s := by
  by_cases hd : d = 0
  · subst d
    have he : (fun t : ℝ => heatLogBCF t.toNNReal 0 g.f) =
        (fun t => gaussianAverageBCF t.toNNReal g.f) := by ext t x; simp [heatLog]
    rw [he]
    exact (gaussianAverageBCF_time_hasDerivAt g s hs).continuousAt
  let A : ℝ → (ℝ →ᵇ ℝ) := fun t => gaussianAverageBCF t.toNNReal (expBCF d g.f)
  let c : ℝ := Real.exp (-(d : ℝ)*‖g.f‖)
  have hc : 0 < c := Real.exp_pos _
  have hb t : ∀ x, c ≤ A t x := fun x => (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg g.f x).1
  have ha : ContinuousAt A s := (gaussianAverageBCF_time_hasDerivAt (g.exp d) s hs).continuousAt
  have hbd t : ‖heatLogBCF t.toNNReal d g.f - heatLogBCF s.toNNReal d g.f‖ ≤
      (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change |heatLog t.toNNReal d g.f x-heatLog s.toNNReal d g.f x| ≤ _
    simp only [heatLog,hd,↓reduceIte,← mul_sub,abs_mul,abs_inv,abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ)⁻¹*(c⁻¹*|A t x-A s x|) :=
        mul_le_mul_of_nonneg_left (log_lipschitz_above hc (hb s x) (hb t x)) (by positivity)
      _ ≤ (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left ((A t-A s).norm_coe_le_norm x) (by positivity)
  have ht : Tendsto (fun t => (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖) (𝓝 s) (𝓝 0) := by
    simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
      (ha.sub (continuousAt_const (y := A s))).norm.const_mul ((d : ℝ)⁻¹*c⁻¹) |>.tendsto
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbd ht)

end SphericalPerceptron
end
end
end

end OAI
