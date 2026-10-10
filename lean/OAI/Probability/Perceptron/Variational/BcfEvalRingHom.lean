import Mathlib
import OAI.Probability.Perceptron.Variational.HeatTilt

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

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

private def bcfEvalRingHom (x : ℝ) : (ℝ →ᵇ ℝ) →+* ℝ where
  toFun := fun f => f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

lemma expBCF_eq_normedSpace_exp (d : ℝ) (f : ℝ →ᵇ ℝ) :
    expBCF d f = NormedSpace.exp (d • f) := by
  ext x
  have hh := NormedSpace.map_exp (bcfEvalRingHom x)
    (BoundedContinuousFunction.evalCLM ℝ x).continuous (d • f)
  change _ = (bcfEvalRingHom x) (NormedSpace.exp (d • f))
  rw [hh,← Real.exp_eq_exp_ℝ]
  rfl

lemma expBCF_hasFDerivAt (d : ℝ) (f : ℝ →ᵇ ℝ) :
    HasFDerivAt (expBCF d)
      ((expBCF d f • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))) ∘L
        (d • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ)))) f := by
  have hh := (hasFDerivAt_exp (𝕂 := ℝ) (x := d • f)).comp f
    ((d • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))).hasFDerivAt)
  simpa only [← expBCF_eq_normedSpace_exp,one_apply_eq_self,
    _root_.smul_apply,Function.comp_def] using hh

def heatGenerator (d : ℝ≥0) (g : Jet3) : ℝ →ᵇ ℝ :=
  (1/2 : ℝ) • (g.d2 + (d : ℝ) • g.d1^2)

lemma heatLogBCF_time_hasDerivAt (g : Jet3) (d : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => heatLogBCF t.toNNReal d g.f)
      (heatGenerator d (g.heatLog s.toNNReal d)) s := by
  by_cases hd : d = 0
  · subst d
    convert gaussianAverageBCF_time_hasDerivAt g s hs using 1
    · ext t x; simp [heatLog]
    · simp [heatGenerator,Jet3.heatLog,Jet3.gaussianAverage]
  have hdR : (d : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hd
  let U := heatLogBCF s.toNNReal d g.f
  let L : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
    ((d : ℝ)⁻¹ • expBCF (-(d : ℝ)) U) • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))
  have hlin : Function.LeftInverse L
      ((expBCF d U • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))) ∘L
        ((d : ℝ) • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ)))) := by
    intro h
    ext x
    change ((d : ℝ)⁻¹*Real.exp (-(d : ℝ)*U x))*(Real.exp ((d : ℝ)*U x)*((d : ℝ)*h x)) = h x
    calc
      _ = ((d : ℝ)⁻¹*d)*(Real.exp (-(d : ℝ)*U x)*Real.exp ((d : ℝ)*U x))*h x := by ring
      _ = h x := by rw [← Real.exp_add]; simp [hdR]
  have hcomp : expBCF d ∘ (fun t : ℝ => heatLogBCF t.toNNReal d g.f) =ᶠ[𝓝 s]
      (fun t : ℝ => gaussianAverageBCF t.toNNReal (g.exp d).f) := by
    apply Filter.Eventually.of_forall
    intro t
    ext x
    exact exp_heatLog t.toNNReal d hd g.f x
  have hh := HasFDerivAt.of_comp_of_leftInverse
    (heatLogBCF_time_continuousAt g d s hs) (expBCF_hasFDerivAt d U)
    (gaussianAverageBCF_time_hasDerivAt (g.exp d) s hs).hasFDerivAt hcomp hlin
  have he : L ((1/2 : ℝ) • gaussianAverageBCF s.toNNReal (g.exp d).d2) =
      heatGenerator d (g.heatLog s.toNNReal d) := by
    ext x
    have hex : Real.exp (-(d : ℝ)*U x) = (gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹ := by
      rw [neg_mul,Real.exp_neg,show Real.exp ((d : ℝ)*U x) = _ from exp_heatLog s.toNNReal d hd g.f x]
    change ((d : ℝ)⁻¹*Real.exp (-(d : ℝ)*U x)) *
      ((1/2)*gaussianAverage s.toNNReal (g.exp d).d2 x) = _
    rw [hex]
    simp only [Jet3.heatLog,hd,↓reduceDIte]
    change _ = (1/2)*((d : ℝ)⁻¹ *
      (gaussianAverage s.toNNReal (g.exp d).d2 x *
        (gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹ -
       (gaussianAverage s.toNNReal (g.exp d).d1 x)^2 *
        ((gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹)^2) +
      (d : ℝ)*((d : ℝ)⁻¹ * (gaussianAverage s.toNNReal (g.exp d).d1 x *
        (gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹))^2)
    field_simp [hdR,(gaussianAverage_exp_pos s.toNNReal d g.f x).ne']
    ring
  apply hh.hasDerivAt.congr_deriv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] using he

lemma gaussianAverageBCF_scaling_of_deriv (s : ℝ≥0) (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) :
    gaussianAverageBCF s f = ∫ z, shiftBCF f (Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hi := shiftBCF_gaussian_integrable f f' hf (Real.sqrt s)
  ext x
  have he := (BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm hi
  change gaussianAverage s f x = _
  rw [gaussianAverage_scaling]
  exact he

lemma gaussianAverageBCF_time_continuous_of_deriv (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) :
    Continuous (fun t : ℝ => gaussianAverageBCF t.toNNReal f) := by
  have he : (fun t : ℝ => gaussianAverageBCF t.toNNReal f) =
      (fun t : ℝ => ∫ z, shiftBCF f (Real.sqrt t.toNNReal*z) ∂gaussianReal 0 1) := by
    ext t x
    exact congrArg (fun h : ℝ →ᵇ ℝ => h x) (gaussianAverageBCF_scaling_of_deriv t.toNNReal f f' hf)
  rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t
    exact (shiftBCF_gaussian_integrable f f' hf (Real.sqrt t.toNNReal)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun z => shiftBCF_norm_le f (Real.sqrt t.toNNReal*z))
  · exact integrable_const _
  · apply ae_of_all
    intro z
    apply (shiftBCF_lipschitz f f' hf).continuous.comp
    exact (Real.continuous_sqrt.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)).mul_const z

lemma heatTiltBCF_time_continuous_of_deriv (f f' h h' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) (d : ℝ≥0) :
    Continuous (fun t : ℝ => heatTiltBCF t.toNNReal d f h) := by
  let A := expBCF d f
  let A' := (d : ℝ) • (A*f')
  have hA x : HasDerivAt (A:ℝ→ℝ) (A' x) x := by
    change HasDerivAt (fun y => Real.exp ((d : ℝ)*f y)) ((d : ℝ)*(A x*f' x)) x
    exact ((hf x).const_mul (d : ℝ)).exp.congr_deriv (by dsimp [A,expBCF]; ring)
  have hB x : HasDerivAt (A*h : ℝ →ᵇ ℝ) ((A'*h+A*h') x) x := by
    simpa only [BoundedContinuousFunction.coe_mul,Pi.mul_apply,
      BoundedContinuousFunction.coe_add,Pi.add_apply] using (hA x).mul (hh x)
  have hca := gaussianAverageBCF_time_continuous_of_deriv A A' hA
  have hcb := gaussianAverageBCF_time_continuous_of_deriv (A*h) (A'*h+A*h') hB
  let c := Real.exp (-(d : ℝ)*‖f‖)
  have hc : 0 < c := Real.exp_pos _
  let J (t : ℝ) := invBCF (gaussianAverageBCF t.toNNReal A) c hc
    (fun x => (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg f x).1)
  have hJ : Continuous J := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hb t : ‖J t-J s‖ ≤ c⁻¹^2 * ‖gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A‖ := by
      apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
      intro x
      change |(gaussianAverage t.toNNReal A x)⁻¹-(gaussianAverage s.toNNReal A x)⁻¹| ≤ _
      have h1 := (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg f x).1
      have h2 := (gaussianAverage_exp_bounds s.toNNReal d d.coe_nonneg f x).1
      have h1p : 0 < gaussianAverage t.toNNReal A x := hc.trans_le h1
      have h2p : 0 < gaussianAverage s.toNNReal A x := hc.trans_le h2
      rw [inv_sub_inv h1p.ne' h2p.ne',abs_div,abs_mul,
        abs_of_pos h1p,abs_of_pos h2p,abs_sub_comm]
      calc
        _ ≤ ‖gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A‖/(c*c) :=
          div_le_div₀ (by positivity) ((gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A).norm_coe_le_norm x)
            (by positivity) (mul_le_mul h1 h2 hc.le h1p.le)
        _ = _ := by ring
    have ht : Tendsto (fun t => c⁻¹^2*‖gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A‖)
        (𝓝 s) (𝓝 0) := by
      simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
        ((hca.continuousAt (x := s)).sub (continuousAt_const (y := gaussianAverageBCF s.toNNReal A))).norm.const_mul (c⁻¹^2) |>.tendsto
    exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hb ht)
  have he : (fun t : ℝ => heatTiltBCF t.toNNReal d f h) =
      (fun t => gaussianAverageBCF t.toNNReal (A*h)*J t) := by
    ext t x
    change gaussianAverage t.toNNReal (A*h) x / gaussianAverage t.toNNReal A x = _
    rfl
  rw [he]
  exact hcb.mul hJ

lemma heatGenerator_hasDerivAt (g : Jet3) (d : ℝ≥0) (x : ℝ) :
    HasDerivAt (heatGenerator d g : ℝ → ℝ)
      (((1/2 : ℝ) • (g.d3+(2*(d:ℝ)) • (g.d1*g.d2))) x) x := by
  have hh := ((g.has3 x).add ((g.has2 x).pow 2 |>.const_mul (d : ℝ))).const_mul (1/2 : ℝ)
  change HasDerivAt (fun y => (1/2 : ℝ)*(g.d2 y+(d:ℝ)*(g.d1 y)^2))
    ((1/2 : ℝ)*(g.d3 x+(2*(d:ℝ))*(g.d1 x*g.d2 x))) x
  exact hh.congr_deriv (by norm_num; ring)

lemma heatTilt_heatGenerator (g : Jet3) (s d : ℝ≥0) :
    heatTiltCLM s d g.f (heatGenerator d g) = heatGenerator d (g.heatLog s d) := by
  by_cases hd : d = 0
  · subst d
    ext x
    simp only [heatGenerator,NNReal.coe_zero,zero_smul,add_zero]
    change heatTilt s 0 g.f ((1/2 : ℝ) • g.d2) x = _
    rw [heatTilt_zero,gaussianAverage_smul]
    simp only [Jet3.heatLog,↓reduceDIte]
    rfl
  have hdR : (d : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hd
  ext x
  have hf : (g.exp d).d2 = (d : ℝ) • (expBCF d g.f*(g.d2+(d : ℝ) • g.d1^2)) := by
    ext z
    simp only [Jet3.exp,BoundedContinuousFunction.coe_smul,BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_mul,BoundedContinuousFunction.coe_pow,
      Pi.add_apply,Pi.mul_apply,Pi.pow_apply,smul_eq_mul]
    ring
  have hf1 : (g.exp d).d1 = (d : ℝ) • (expBCF d g.f*g.d1) := rfl
  change heatTilt s d g.f (heatGenerator d g) x = _
  simp only [heatGenerator,heatTilt_smul,heatTilt_add,Jet3.heatLog,hd,↓reduceDIte]
  change (1/2)*(heatTilt s d g.f g.d2 x + (d:ℝ)*heatTilt s d g.f (g.d1^2) x) =
    (1/2)*((d : ℝ)⁻¹ *
      (gaussianAverage s (g.exp d).d2 x * (gaussianAverage s (expBCF d g.f) x)⁻¹ -
       (gaussianAverage s (g.exp d).d1 x)^2 * ((gaussianAverage s (expBCF d g.f) x)⁻¹)^2) +
      (d : ℝ)*((d : ℝ)⁻¹ * (gaussianAverage s (g.exp d).d1 x *
        (gaussianAverage s (expBCF d g.f) x)⁻¹))^2)
  rw [hf,hf1,gaussianAverage_smul,gaussianAverage_smul]
  have hm : expBCF d g.f*(g.d2+(d : ℝ) • g.d1^2) =
      expBCF d g.f*g.d2+(d : ℝ) • (expBCF d g.f*g.d1^2) := by ext z; simp; ring
  rw [hm,gaussianAverage_add,gaussianAverage_smul]
  unfold heatTilt
  simp only [BoundedContinuousFunction.coe_mul]
  field_simp [hdR,(gaussianAverage_exp_pos s d g.f x).ne']
  ring

lemma heatLogBCF_moving_hasDerivAt (g : Jet3) (d : ℝ≥0)
    (σ : ℝ → ℝ) (G : ℝ → (ℝ →ᵇ ℝ)) (θ v : ℝ) (h h' : ℝ →ᵇ ℝ)
    (hσ : HasDerivAt σ v θ) (hs : 0 < σ θ)
    (hG : HasDerivAt G h θ) (hGθ : G θ = g.f)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) :
    HasDerivAt (fun t => heatLogBCF (σ t).toNNReal d (G t))
      (v • heatGenerator d (g.heatLog (σ θ).toNNReal d) +
        heatTiltCLM (σ θ).toNNReal d g.f h) θ := by
  let L (t : ℝ) := heatTiltCLM (σ t).toNNReal d g.f
  let A (t : ℝ) := heatLogBCF (σ t).toNNReal d g.f
  let K (t : ℝ) := G t-g.f
  have hK0 : Tendsto K (𝓝 θ) (𝓝 0) := by
    simpa only [hGθ,sub_self] using hG.continuousAt.tendsto.sub_const g.f
  have hKo : (fun t => ‖K t‖) =o[𝓝 θ] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr (by simpa only [norm_zero] using hK0.norm)
  have hKb : (fun t => ‖K t‖) =O[𝓝 θ] (fun t => t-θ) := by
    simpa only [hGθ] using hG.isBigO_sub.norm_left
  have hR : (fun t => heatLogBCF (σ t).toNNReal d (G t)-A t-L t (K t))
      =o[𝓝 θ] (fun t => t-θ) := by
    have hb : (fun t => heatLogBCF (σ t).toNNReal d (G t)-A t-L t (K t))
        =O[𝓝 θ] (fun t => ‖K t‖*‖K t‖) := by
      apply Asymptotics.IsBigO.of_bound (2*(d:ℝ))
      apply Filter.Eventually.of_forall
      intro t
      have he := heatLogBCF_terminal_quadratic_error (σ t).toNNReal d g.f (K t)
      simpa only [K,A,L,add_sub_cancel,norm_mul,Real.norm_of_nonneg (norm_nonneg _),pow_two] using he
    exact hb.trans_isLittleO (by simpa only [one_mul] using hKo.mul_isBigO hKb)
  have hE : (fun t => L t (G t-g.f-(t-θ) • h)) =o[𝓝 θ] (fun t => t-θ) := by
    have hb : (fun t => L t (G t-g.f-(t-θ) • h)) =O[𝓝 θ]
        (fun t => G t-g.f-(t-θ) • h) := by
      apply Asymptotics.IsBigO.of_bound'
      exact Filter.Eventually.of_forall (fun t => heatTiltBCF_norm_le (σ t).toNNReal d g.f _)
    apply hb.trans_isLittleO
    simpa only [hGθ] using hG.isLittleO
  have hLc : Tendsto (fun t => L t h-L θ h) (𝓝 θ) (𝓝 0) := by
    have hc := (heatTiltBCF_time_continuous_of_deriv g.f g.d1 h h' g.has1 hh d).continuousAt.comp
      hσ.continuousAt
    have he := hc.tendsto.sub_const (L θ h)
    change Tendsto (fun t => L t h-L θ h) (𝓝 θ) (𝓝 (L θ h-L θ h)) at he
    simpa only [sub_self] using he
  have hLo : (fun t => (t-θ) • (L t h-L θ h)) =o[𝓝 θ] (fun t => t-θ) := by
    have he := (Asymptotics.isBigO_refl (fun t : ℝ => t-θ) (𝓝 θ)).smul_isLittleO
      ((Asymptotics.isLittleO_one_iff ℝ).mpr hLc)
    simpa only [smul_eq_mul,mul_one] using he
  have hA : HasDerivAt A (v • heatGenerator d (g.heatLog (σ θ).toNNReal d)) θ :=
    (heatLogBCF_time_hasDerivAt g d (σ θ) hs).scomp θ hσ
  apply HasDerivAt.of_isLittleO
  apply ((hA.isLittleO.add hR).add hE |>.add hLo).congr_left
  intro t
  simp only [hGθ,K,A,L,map_sub,map_smul,smul_add,smul_sub]
  abel

lemma heatTiltBCF_hasDerivAt (s d : ℝ≥0) (f f' h h' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) (x : ℝ) :
    HasDerivAt (heatTiltBCF s d f h : ℝ→ℝ)
      ((heatTiltBCF s d f h' + (d:ℝ) •
        (heatTiltBCF s d f (f'*h)-heatTiltBCF s d f f'*heatTiltBCF s d f h)) x) x := by
  let A := expBCF d f
  let A' := (d : ℝ) • (A*f')
  have hA y : HasDerivAt (A:ℝ→ℝ) (A' y) y := by
    change HasDerivAt (fun z => Real.exp ((d:ℝ)*f z)) ((d:ℝ)*(A y*f' y)) y
    exact ((hf y).const_mul (d:ℝ)).exp.congr_deriv (by dsimp [A,expBCF]; ring)
  have hB y : HasDerivAt (A*h : ℝ→ᵇ ℝ) ((A'*h+A*h') y) y := by
    simpa only [BoundedContinuousFunction.coe_mul,Pi.mul_apply,
      BoundedContinuousFunction.coe_add,Pi.add_apply] using (hA y).mul (hh y)
  have he := (gaussianAverage_hasDerivAt s (A*h) (A'*h+A*h') hB x).div
    (gaussianAverage_hasDerivAt s A A' hA x) (gaussianAverage_exp_pos s d f x).ne'
  change HasDerivAt (fun y => gaussianAverage s (A*h) y / gaussianAverage s A y) _ x
  apply he.congr_deriv
  have hmul : A'*h = (d:ℝ) • (A*(f'*h)) := by ext y; dsimp [A']; ring
  rw [gaussianAverage_add,hmul,gaussianAverage_smul]
  symm
  change (gaussianAverage s (A*h') x/gaussianAverage s A x) +
    (d:ℝ)*((gaussianAverage s (A*(f'*h)) x/gaussianAverage s A x)-
      (gaussianAverage s (A*f') x/gaussianAverage s A x)*
        (gaussianAverage s (A*h) x/gaussianAverage s A x)) = _
  dsimp only [A']
  rw [gaussianAverage_smul]
  simp only [BoundedContinuousFunction.coe_mul]
  field_simp [show gaussianAverage s A x ≠ 0 from (gaussianAverage_exp_pos s d f x).ne']
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
