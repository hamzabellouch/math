import Mathlib
import OAI.Probability.SphericalField.Heat.Translations

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

end SphericalPerceptron
end
end
end

end OAI
