import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SmoothReciprocalNormCompBound

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric Filter
open scoped ContDiff RealInnerProductSpace Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def spherePlaneWaveND (Λ : ℝ) (e x : V) : ℂ :=
  Complex.exp (Complex.I*Λ*(inner ℝ x e : ℂ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma spherePlaneWaveND_contDiff (Λ : ℝ) (e : V) :
    ContDiff ℝ ∞ (spherePlaneWaveND Λ e) := by
  unfold spherePlaneWaveND
  have hi : ContDiff ℝ ∞ (fun x : V => (inner ℝ x e : ℂ)) :=
    by simpa [Function.comp_def,real_inner_comm] using
      Complex.ofRealCLM.contDiff.comp (innerSL ℝ e).contDiff
  exact (contDiff_const.mul hi).cexp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_planeWave (A : V →L[ℝ] V) (Λ : ℝ) (e x : V) :
    angularDerivativeND A (spherePlaneWaveND Λ e) x =
      spherePlaneWaveND Λ e x * (Complex.I*Λ*(inner ℝ (A x) e : ℂ)) := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (innerSL ℝ e)
  have hL : ∀ w, L w = (inner ℝ w e : ℂ) := by
    intro w
    simp [L,real_inner_comm]
  have h := ((L.hasFDerivAt (x := x)).const_mul (Complex.I*Λ)).cexp
  change HasFDerivAt _ _ x at h
  unfold angularDerivativeND spherePlaneWaveND
  have he : (fun y => Complex.exp (Complex.I*Λ*L y)) =
      (fun y => Complex.exp (Complex.I*Λ*(inner ℝ y e : ℂ))) := by ext y; rw [hL]
  rw [he] at h
  rw [h.fderiv]
  simp [hL,smul_eq_mul]

noncomputable def sphereAxisIntegralND (Λ : ℝ) (e : V) (b : V → ℂ) : ℂ :=
  ∫ w, Complex.exp (Complex.I*Λ*(inner ℝ w e : ℂ))*b w ∂canonicalSphereMeasureND V

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def smoothPhaseReciprocalND (T : V →L[ℝ] V) (e : V) (τ : ℝ) (x : V) : ℂ :=
  (τ⁻¹ : ℂ) * (smoothReciprocal (inner ℝ (T x) e / τ) : ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma smoothPhaseReciprocalND_contDiff (T : V →L[ℝ] V) (e : V) (τ : ℝ) :
    ContDiff ℝ ∞ (smoothPhaseReciprocalND T e τ) := by
  have hL : ContDiff ℝ ∞ (fun x => inner ℝ (T x) e / τ) := by
    simpa [real_inner_comm,div_eq_mul_inv] using
      (((innerSL ℝ e).comp T).contDiff.mul contDiff_const)
  exact contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (smoothReciprocal_contDiff.comp hL))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma smoothPhaseReciprocalND_cancel (T : V →L[ℝ] V) (e : V) {τ : ℝ} (hτ : 0 < τ)
    {x : V} (hx : τ ≤ inner ℝ (T x) e) :
    (inner ℝ (T x) e : ℂ) * smoothPhaseReciprocalND T e τ x = 1 := by
  have hd : inner ℝ (T x) e ≠ 0 := ne_of_gt (hτ.trans_le hx)
  rw [smoothPhaseReciprocalND, smoothReciprocal_eq_inv ((le_div_iff₀ hτ).2 (by simpa using hx))]
  push_cast
  field_simp [hd,hτ.ne']

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma smoothPhaseReciprocalND_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : V →L[ℝ] V) (e : V) (τ A : ℝ),
      ‖T‖ ≤ 2 → 0 < τ → 0 ≤ A → ‖e‖/τ ≤ A →
      ∀ j ≤ m, ∀ w,
        ‖iteratedFDeriv ℝ j (smoothPhaseReciprocalND T e τ) w‖ ≤ (C/τ)*A^j := by
  obtain ⟨C,hC,hCb⟩ := smoothReciprocal_norm_comp_bound (V := V) m
  refine ⟨C*2^m, by positivity, ?_⟩
  intro T e τ A hT hτ hA he j hj w
  let L : V →L[ℝ] ℝ := τ⁻¹ • ((innerSL ℝ e).comp T)
  have hL : ∀ x, L x = inner ℝ (T x) e / τ := by
    intro x
    simp [L,real_inner_comm,div_eq_mul_inv,mul_comm]
  have hLn : ‖L‖ ≤ 2*A := by
    calc
      ‖L‖ = τ⁻¹*‖(innerSL ℝ e).comp T‖ := by rw [show L = τ⁻¹ • ((innerSL ℝ e).comp T) from rfl,
        norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hτ]
      _ ≤ τ⁻¹*(‖innerSL ℝ e‖*‖T‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)
      _ ≤ τ⁻¹*(‖e‖*2) := by gcongr; simp
      _ = 2*(‖e‖/τ) := by ring
      _ ≤ 2*A := by gcongr
  have hEq : smoothPhaseReciprocalND T e τ =
      fun x => (τ⁻¹:ℂ) • ((smoothReciprocal (L x):ℂ)) := by
    funext x
    simp [smoothPhaseReciprocalND,hL,smul_eq_mul]
  have hcf : ContDiff ℝ ∞ (fun x : V => (smoothReciprocal (L x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (smoothReciprocal_contDiff.comp L.contDiff)
  rw [hEq,iteratedFDeriv_const_smul_apply'
    ((hcf.of_le (show (j:ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt),
    norm_smul]
  have hct : ‖(τ⁻¹:ℂ)‖ = τ⁻¹ := by simp [abs_of_pos hτ]
  rw [hct]
  calc
    _ ≤ τ⁻¹*(C*‖L‖^j) := mul_le_mul_of_nonneg_left (hCb L j hj w) (by positivity)
    _ ≤ τ⁻¹*(C*(2*A)^j) := by gcongr
    _ = (C/τ)*2^j*A^j := by rw [mul_pow]; ring
    _ ≤ (C/τ)*2^m*A^j := by gcongr; norm_num
    _ = (C*2^m/τ)*A^j := by ring

omit [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_zero_region [MeasurableSpace V] [BorelSpace V]
    (T : V →L[ℝ] V) (hT : star T = -T)
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) {d : V → ℝ} (hd : Continuous d) {τ : ℝ}
    (hz : ∀ w, ‖w‖=1 → d w < τ → f w=0) {w : V} (hw : ‖w‖=1) (hdw : d w < τ) :
    angularDerivativeND T f w = 0 := by
  have hcurve := skewFlowND_hasDerivAt T hT 0 w
  have hdf := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hc : ContinuousAt (fun t => d (skewFlowND T hT t w)) 0 :=
    hd.continuousAt.comp hcurve.continuousAt
  have he : (fun t => f (skewFlowND T hT t w)) =ᶠ[𝓝 (0:ℝ)] fun _ => (0:ℂ) := by
    have hnear := hc.preimage_mem_nhds (Iio_mem_nhds (show d (skewFlowND T hT 0 w) < τ by
      simpa [skewFlowND_zero] using hdw))
    filter_upwards [hnear] with t ht
    exact hz _ (by simpa using hw) ht
  have hz' := hdf.congr_of_eventuallyEq he.symm
  have heq := hz'.unique (hasDerivAt_const (0:ℝ) (0:ℂ))
  simpa [angularDerivativeND,skewFlowND_zero] using heq

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric Filter
open scoped ContDiff RealInnerProductSpace Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def angularAdjointND (T : V →L[ℝ] V) (e : V) (τ : ℝ) (b : V → ℂ) : V → ℂ :=
  fun w => -angularDerivativeND T (fun x => smoothPhaseReciprocalND T e τ x*b x) w

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularAdjointND_contDiff [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (T : V →L[ℝ] V) (e : V) (τ : ℝ) {b : V → ℂ}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (angularAdjointND T e τ b) :=
  (angularDerivativeND_contDiff T ((smoothPhaseReciprocalND_contDiff T e τ).mul hb)).neg

lemma angularAdjointND_support (T : V →L[ℝ] V) (hT : star T = -T) (e : V) (τ : ℝ)
    {b : V → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : ∀ w, ‖w‖=1 → inner ℝ (T w) e < τ → b w=0) :
    ∀ w, ‖w‖=1 → inner ℝ (T w) e < τ → angularAdjointND T e τ b w=0 := by
  intro w hw hdw
  dsimp [angularAdjointND]
  rw [angularDerivativeND_zero_region T hT
    ((smoothPhaseReciprocalND_contDiff T e τ).mul hb)
    (T.continuous.inner continuous_const) (fun x hx hd => by rw [hs x hx hd,mul_zero]) hw hdw,
    neg_zero]

omit [MeasurableSpace V] [BorelSpace V] in
lemma angularAdjointND_bound [MeasurableSpace V] [BorelSpace V] (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : V →L[ℝ] V) (e : V) (τ A B : ℝ) (b : V → ℂ),
      ‖T‖ ≤ 2 → 0 < τ → 1 ≤ A → 0 ≤ B → ‖e‖/τ ≤ A → ContDiff ℝ ∞ b →
      (∀ j ≤ m+1, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ B*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (angularAdjointND T e τ b) w‖ ≤ (D*B*A/τ)*A^j := by
  obtain ⟨C,hC,hCb⟩ := smoothPhaseReciprocalND_bound (V := V) (m+1)
  obtain ⟨D,hD,hDb⟩ := angularDerivative_uniform_bound (V := V) m
  refine ⟨D*2^(m+1)*C, by positivity, ?_⟩
  intro T e τ A B b hT hτ hA hB he hb hbb j hj w hw
  have hqb := hCb T e τ A hT hτ (by linarith) he
  have hprod := sphere_product_derivative_bound (m+1)
    (smoothPhaseReciprocalND_contDiff T e τ) hb (by linarith : 0 ≤ A)
    (div_nonneg hC hτ.le) hB (fun j hj w _ => hqb j hj w) hbb
  have hbd := hDb T _ A (2^(m+1)*(C/τ)*B) hT
    ((smoothPhaseReciprocalND_contDiff T e τ).mul hb) hA (by positivity) hprod j hj w hw
  change ‖iteratedFDeriv ℝ j (- (angularDerivativeND T
    (fun x => smoothPhaseReciprocalND T e τ x*b x))) w‖ ≤ _
  rw [iteratedFDeriv_neg_apply,norm_neg]
  apply hbd.trans_eq
  rw [pow_succ]
  ring

lemma sphereAxisIntegralND_norm_le {Λ B : ℝ} {e : V} {b : V → ℂ}
    (hb : ∀ w, ‖w‖=1 → ‖b w‖ ≤ B) :
    ‖sphereAxisIntegralND Λ e b‖ ≤ (canonicalSphereMeasureND V).real univ * B := by
  unfold sphereAxisIntegralND
  rw [mul_comm ((canonicalSphereMeasureND V).real univ) B]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
  simpa [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im] using hb w hw

lemma sphereAxisIntegralND_adjoint (T : V →L[ℝ] V) (hT : star T = -T) (e : V)
    (Λ : ℝ) {τ : ℝ} (hτ : 0 < τ) {b : V → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : ∀ w, ‖w‖=1 → inner ℝ (T w) e < τ → b w=0) :
    (Complex.I*Λ)*sphereAxisIntegralND Λ e b =
      sphereAxisIntegralND Λ e (angularAdjointND T e τ b) := by
  have hibp := sphere_angular_integration_by_parts T hT
    (spherePlaneWaveND_contDiff Λ e) ((smoothPhaseReciprocalND_contDiff T e τ).mul hb)
  have hl : (∫ w, angularDerivativeND T (spherePlaneWaveND Λ e) w *
      (smoothPhaseReciprocalND T e τ w*b w) ∂canonicalSphereMeasureND V) =
      (Complex.I*Λ)*sphereAxisIntegralND Λ e b := by
    rw [sphereAxisIntegralND, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    rw [angularDerivativeND_planeWave]
    by_cases hd : inner ℝ (T w) e < τ
    · rw [hs w hw hd]; simp
    · have hc := smoothPhaseReciprocalND_cancel T e hτ (le_of_not_gt hd)
      change spherePlaneWaveND Λ e w * (Complex.I*Λ*(inner ℝ (T w) e:ℂ)) *
        (smoothPhaseReciprocalND T e τ w*b w) =
        (Complex.I*Λ)*(spherePlaneWaveND Λ e w*b w)
      calc
        _ = (Complex.I*Λ)*(spherePlaneWaveND Λ e w*b w)*
          ((inner ℝ (T w) e:ℂ)*smoothPhaseReciprocalND T e τ w) := by ring
        _ = _ := by rw [hc,mul_one]
  rw [hl] at hibp
  rw [hibp, sphereAxisIntegralND, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [angularAdjointND,spherePlaneWaveND,mul_neg]

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace

theorem sphere_nonstationary_aux
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : V →L[ℝ] V) (e : V) (Λ τ A B : ℝ) (b : V → ℂ),
      star T = -T → ‖T‖ ≤ 2 → 0 < Λ → 0 < τ → 1 ≤ A → 0 ≤ B → ‖e‖/τ ≤ A →
      ContDiff ℝ ∞ b →
      (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ B*A^j) →
      (∀ w, ‖w‖=1 → inner ℝ (T w) e < τ → b w=0) →
      ‖sphereAxisIntegralND Λ e b‖ ≤ C*B*(A/(Λ*τ))^m := by
  induction m with
  | zero =>
    refine ⟨(canonicalSphereMeasureND V).real univ, ENNReal.toReal_nonneg, ?_⟩
    intro T e Λ τ A B b _ _ _ _ _ _ _ _ hb _
    simpa only [pow_zero,mul_one] using
      sphereAxisIntegralND_norm_le (Λ := Λ) (e := e) (fun w hw => by
        simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb 0 le_rfl w hw)
  | succ m ih =>
    obtain ⟨C,hC,hCb⟩ := ih
    obtain ⟨D,hD,hDb⟩ := angularAdjointND_bound (V := V) m
    refine ⟨C*D, mul_nonneg hC hD, ?_⟩
    intro T e Λ τ A B b hT hTn hΛ hτ hA hB he hb hbb hs
    have hadj := hCb T e Λ τ A (D*B*A/τ) (angularAdjointND T e τ b) hT hTn hΛ hτ
      hA (by positivity) he (angularAdjointND_contDiff T e τ hb)
      (hDb T e τ A B b hTn hτ hA hB he hb hbb) (angularAdjointND_support T hT e τ hb hs)
    have hid : Λ*‖sphereAxisIntegralND Λ e b‖ =
        ‖sphereAxisIntegralND Λ e (angularAdjointND T e τ b)‖ := by
      have hh := congrArg norm (sphereAxisIntegralND_adjoint T hT e Λ hτ hb hs)
      simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hΛ] using hh
    calc
      ‖sphereAxisIntegralND Λ e b‖ =
          ‖sphereAxisIntegralND Λ e (angularAdjointND T e τ b)‖/Λ := by
        apply (eq_div_iff hΛ.ne').2
        simpa only [mul_comm] using hid
      _ ≤ C*(D*B*A/τ)*(A/(Λ*τ))^m/Λ :=
        div_le_div_of_nonneg_right hadj hΛ.le
      _ = (C*D)*B*(A/(Λ*τ))^(m+1) := by rw [pow_succ]; ring

theorem sphere_nonstationary_uniform
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : V →L[ℝ] V) (e : V) (Λ τ A B : ℝ) (b : V → ℂ),
      star T = -T → ‖T‖ ≤ 2 → 0 < Λ → 0 < τ → 1 ≤ A → 0 ≤ B →
      ContDiff ℝ ∞ b →
      (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ B*A^j) →
      (∀ w, ‖w‖=1 → inner ℝ (T w) e < τ → b w=0) →
      ‖sphereAxisIntegralND Λ e b‖ ≤ C*B*((A+1+‖e‖/τ)/(Λ*τ))^m := by
  obtain ⟨C,hC,hCb⟩ := sphere_nonstationary_aux V m
  refine ⟨C,hC,?_⟩
  intro T e Λ τ A B b hT hTn hΛ hτ hA hB hb hbb hs
  have he0 : 0 ≤ ‖e‖/τ := div_nonneg (norm_nonneg _) hτ.le
  refine hCb T e Λ τ (A+1+‖e‖/τ) B b hT hTn hΛ hτ (by linarith) hB
    (by linarith) hb ?_ hs
  intro j hj w hw
  exact (hbb j hj w hw).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0 ≤ A) (by linarith) j) hB)

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

noncomputable def capRotationND (w t : V) : V →L[ℝ] V :=
  InnerProductSpace.rankOne ℝ t w - InnerProductSpace.rankOne ℝ w t

omit [FiniteDimensional ℝ V] in
lemma capRotationND_apply [FiniteDimensional ℝ V] (w t x : V) :
    capRotationND w t x = inner ℝ w x • t - inner ℝ t x • w := by
  simp [capRotationND,InnerProductSpace.rankOne_apply]

lemma capRotationND_skew (w t : V) : star (capRotationND w t) = -capRotationND w t := by
  simp [capRotationND,ContinuousLinearMap.star_eq_adjoint,neg_sub]

omit [FiniteDimensional ℝ V] in
lemma capRotationND_norm_le [FiniteDimensional ℝ V] (w t : V) (hw : ‖w‖=1) (ht : ‖t‖=1) :
    ‖capRotationND w t‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by norm_num [InnerProductSpace.norm_rankOne,hw,ht])

lemma capRotationND_center (w t : V) (hw : ‖w‖=1) (ht : inner ℝ t w=0) :
    capRotationND w t w = t := by
  simp [capRotationND_apply,hw,ht]

theorem capRotationND_phase_lower (w₀ d : V) (hw : ‖w₀‖=1)
    (hp : 0 < ‖d-inner ℝ d w₀ • w₀‖) :
    ∃ T : V →L[ℝ] V, star T = -T ∧ ‖T‖ ≤ 2 ∧
      ∀ w e : V, inner ℝ (T w) e ≥
        ‖d-inner ℝ d w₀ • w₀‖ - 2*‖w-w₀‖*‖e‖ - ‖e-d‖ := by
  let z := d-inner ℝ d w₀ • w₀
  have hz : 0 < ‖z‖ := hp
  let t := ‖z‖⁻¹ • z
  have ht : ‖t‖=1 := by
    simp only [t,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hz]
    exact inv_mul_cancel₀ hz.ne'
  have hzw : inner ℝ z w₀=0 := by
    simp [z,inner_sub_left,inner_smul_left,hw]
  have htw : inner ℝ t w₀=0 := by simp [t,inner_smul_left,hzw]
  have hzd : inner ℝ z d=‖z‖^2 := by
    have he : d=z+inner ℝ d w₀ • w₀ := by dsimp [z]; abel
    conv_lhs => rw [he]
    simp [inner_add_right,inner_smul_right,hzw]
  have htd : inner ℝ t d=‖z‖ := by
    simp only [t,real_inner_smul_left,hzd]
    field_simp [hz.ne']
  let T := capRotationND w₀ t
  have hT : ‖T‖ ≤ 2 := capRotationND_norm_le w₀ t hw ht
  have hTc : T w₀=t := capRotationND_center w₀ t hw htw
  refine ⟨T,capRotationND_skew w₀ t,hT,?_⟩
  intro w e
  have h1 : |inner ℝ (T (w-w₀)) e| ≤ 2*‖w-w₀‖*‖e‖ := by
    apply (abs_real_inner_le_norm _ _).trans
    gcongr
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have h2 : |inner ℝ t (e-d)| ≤ ‖e-d‖ := by
    simpa only [ht,one_mul] using abs_real_inner_le_norm t (e-d)
  have heq : inner ℝ (T w) e =
      inner ℝ (T (w-w₀)) e + inner ℝ t (e-d) + ‖z‖ := by
    rw [map_sub,hTc,inner_sub_left,inner_sub_right,htd]
    ring
  change ‖z‖-2*‖w-w₀‖*‖e‖-‖e-d‖ ≤ _
  rw [heq]
  linarith [(abs_le.mp h1).1,(abs_le.mp h2).1]

theorem sphere_cap_nonstationary_uniform
    [MeasurableSpace V] [BorelSpace V] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w₀ d e : V) (Λ τ δ D η A B : ℝ) (b : V → ℂ),
      ‖w₀‖=1 → 0 < Λ → 0 < τ → 0 ≤ δ → 0 ≤ D → 0 ≤ η → 1 ≤ A → 0 ≤ B →
      ‖e‖ ≤ D → ‖e-d‖ ≤ η → 2*δ*D+η ≤ τ/2 →
      τ < ‖d-inner ℝ d w₀ • w₀‖ → ContDiff ℝ ∞ b →
      (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ B*A^j) →
      (∀ w, ‖w‖=1 → b w ≠ 0 → ‖w-w₀‖ ≤ δ) →
      ‖sphereAxisIntegralND Λ e b‖ ≤ C*B*((A+1+D/τ)/(Λ*τ))^m := by
  obtain ⟨C,hC,hCb⟩ := sphere_nonstationary_uniform V m
  refine ⟨C*4^m,by positivity,?_⟩
  intro w₀ d e Λ τ δ D η A B b hw hΛ hτ hδ hD hη hA hB he hed herr hfail hb hbb hs
  obtain ⟨T,hT,hTn,hTp⟩ := capRotationND_phase_lower w₀ d hw (hτ.trans hfail)
  have hs' : ∀ w, ‖w‖=1 → inner ℝ (T w) e < τ/2 → b w=0 := by
    intro w hwn hl
    by_contra hn
    have hh := hTp w e
    have he' : 2*‖w-w₀‖*‖e‖ ≤ 2*δ*D := by gcongr; exact hs w hwn hn
    linarith
  have hh := hCb T e Λ (τ/2) A B b hT hTn hΛ (by positivity) hA hB hb hbb hs'
  have hnum : (A+1+‖e‖/(τ/2))/(Λ*(τ/2)) ≤ 4*((A+1+D/τ)/(Λ*τ)) := by
    apply (div_le_iff₀ (by positivity : 0 < Λ*(τ/2))).2
    have hed' : ‖e‖/τ ≤ D/τ := div_le_div_of_nonneg_right he hτ.le
    have hAA : 0 ≤ A+1 := by linarith
    have hrew : 4*((A+1+D/τ)/(Λ*τ))*(Λ*(τ/2)) = 2*(A+1+D/τ) := by field_simp; ring
    rw [hrew,div_div_eq_mul_div]
    rw [show ‖e‖*2/τ=2*(‖e‖/τ) by ring]
    linarith
  calc
    _ ≤ C*B*((A+1+‖e‖/(τ/2))/(Λ*(τ/2)))^m := hh
    _ ≤ C*B*(4*((A+1+D/τ)/(Λ*τ)))^m := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end Attempt4FullFar
end
end

end OAI
