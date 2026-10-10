import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadialStopping

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
namespace ExactSLEGreen
lemma physicalTheta_second_noise (v : State) (hv : 0<Y v) :
    fderiv ℝ (fun w => fderiv ℝ physicalTheta w noise) v noise = 2*X v*Y v/(Q v)^2 := by
  have he : (fun w => fderiv ℝ physicalTheta w noise) =ᶠ[𝓝 v] physicalV := by
    filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hv)] with w hw
    rw [(hasFDerivAt_physicalTheta w hw).fderiv,thetaDeriv_noise]
  rw [he.fderiv_eq]
  have hd : HasFDerivAt physicalV (velocityDeriv v) v := by
    have hQinv := (hasDerivAt_inv (Q_pos hv).ne').comp_hasFDerivAt v (hasFDerivAt_Q v)
    convert Y.hasFDerivAt.mul hQinv using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro w
    simp only [velocityDeriv,add_apply,smul_apply,
      sub_apply,smul_eq_mul,Function.comp_apply]
    have hq := (Q_pos hv).ne'
    field_simp
    ring
  rw [hd.fderiv]
  simp [velocityDeriv,noise,X,Y]
  ring

lemma regX_drift (a : ℝ) (v : State) : X (physicalDrift a v) = a*X v/Q v := by
  simp [physicalDrift,X_apply,Complex.div_re,Q_eq]
lemma regY_drift (a : ℝ) (v : State) : Y (physicalDrift a v) = -a*Y v/Q v := by
  simp [physicalDrift,Y_apply,Complex.div_im,Q_eq]; ring
lemma regJ_drift (a : ℝ) (v : State) :
    J (physicalDrift a v) = -a*((X v)^2-(Y v)^2)/(Q v)^2 := by
  simp only [physicalDrift,J_apply,Complex.div_re,Complex.neg_re,Complex.ofReal_re,
    Complex.neg_im,Complex.ofReal_im,neg_zero,zero_mul,map_pow,← Q_eq]
  simp only [pow_two,Complex.mul_re,X_apply,Y_apply,zero_div,add_zero]

lemma theta_generator (a : ℝ) (v : State) (hv : 0<Y v) :
    (1/2:ℝ)*fderiv ℝ (fun w => fderiv ℝ physicalTheta w noise) v noise +
      fderiv ℝ physicalTheta v (physicalDrift a v) =
        (1-2*a)*Real.cot (physicalTheta v)*(physicalV v)^2 := by
  have hy := hv.ne'
  have hq := (Q_pos hv).ne'
  rw [physicalTheta_second_noise v hv,(hasFDerivAt_physicalTheta v hv).fderiv]
  simp only [thetaDeriv,add_apply,smul_apply,
    smul_eq_mul,regX_drift,regY_drift,physicalTheta_cot,physicalV]
  field_simp
  ring

noncomputable def physicalClock (a cap : ℝ) (v : State) : ℝ :=
  (Real.log (cap/2)+J v-Real.log (Y v))/(2*a)
noncomputable def clockDeriv (a : ℝ) (v : State) : State →L[ℝ] ℝ :=
  (1/(2*a)) • (J-(1/Y v) • Y)
lemma hasFDerivAt_physicalClock (a cap : ℝ) (v : State) (hv : 0<Y v) :
    HasFDerivAt (physicalClock a cap) (clockDeriv a v) v := by
  convert ((J.hasFDerivAt.const_add (Real.log (cap/2))).sub (Y.hasFDerivAt.log hv.ne')).const_mul (1/(2*a)) using 1 <;> try rfl
  · ext w
    simp only [physicalClock,Pi.sub_apply]
    ring
  · simp only [clockDeriv,one_div]
lemma clockDeriv_noise (a : ℝ) (v : State) : clockDeriv a v noise = 0 := by
  simp [clockDeriv,noise,J,Y]
lemma physicalClock_drift (a cap : ℝ) (ha : a≠0) (v : State) (hv : 0<Y v) :
    fderiv ℝ (physicalClock a cap) v (physicalDrift a v) = (physicalV v)^2 := by
  have hy := hv.ne'
  have hq := (Q_pos hv).ne'
  rw [(hasFDerivAt_physicalClock a cap v hv).fderiv]
  simp only [clockDeriv,sub_apply,smul_apply,smul_eq_mul,
    regY_drift,regJ_drift,physicalV]
  field_simp
  dsimp only [Q]
  ring
lemma physicalClock_second_noise (a cap : ℝ) (v : State) (hv : 0<Y v) :
    fderiv ℝ (fun w => fderiv ℝ (physicalClock a cap) w noise) v noise = 0 := by
  have he : (fun w => fderiv ℝ (physicalClock a cap) w noise) =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
    filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hv)] with w hw
    rw [(hasFDerivAt_physicalClock a cap w hw).fderiv,clockDeriv_noise]
  rw [he.fderiv_eq,(hasFDerivAt_const (0:ℝ) v).fderiv]
  rfl
lemma physicalTheta_smooth (v : State) (hv : 0<Y v) : ContDiffAt ℝ 2 physicalTheta v := by
  exact contDiffAt_const.sub ((X.contDiff.contDiffAt.div Y.contDiff.contDiffAt hv.ne').arctan)
lemma physicalClock_smooth (a cap : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ 2 (physicalClock a cap) v := by
  exact ((contDiffAt_const.add J.contDiff.contDiffAt).sub
    (Y.contDiff.contDiffAt.log hv.ne')).div_const (2*a)
end ExactSLEGreen

open Filter Set
open scoped Topology
namespace ExactSLECalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def N (f : E → ℝ) (e : E) (x : E) : ℝ := fderiv ℝ f x e
noncomputable def L (f : E → ℝ) (A e : E) (x : E) : ℝ :=
  (1/2:ℝ) * N (N f e) e x + fderiv ℝ f x A
lemma N_differentiableAt {f : E → ℝ} {x e : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (N f e) x :=
  ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt_one
lemma N_mul {f g : E → ℝ} {x e : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    N (fun y => f y*g y) e x = f x*N g e x+g x*N f e x := by
  change (fderiv ℝ (f*g) x) e = _
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,N]
lemma L_mul {f g : E → ℝ} {x A e : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    L (fun y => f y*g y) A e x = f x*L g A e x+g x*L f A e x+N f e x*N g e x := by
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have heq : N (fun y => f y*g y) e =ᶠ[𝓝 x] (fun y => f y*N g e y+g y*N f e y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hfy hgy
    exact N_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))
  have hd := (hfd.hasFDerivAt.mul (N_differentiableAt (e := e) hg).hasFDerivAt).add
    (hgd.hasFDerivAt.mul (N_differentiableAt (e := e) hf).hasFDerivAt)
  have hd' := hd.fderiv
  have hp := (hfd.hasFDerivAt.mul hgd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y*N g e y+g y*N f e y) x = _ at hd'
  change fderiv ℝ (fun y => f y*g y) x = _ at hp
  unfold L
  rw [N,heq.fderiv_eq,hd',hp]
  simp only [add_apply,smul_apply,smul_eq_mul,N]
  ring
lemma N_comp {f : E → ℝ} {h : ℝ → ℝ} {x e : E}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h (f x)) :
    N (h ∘ f) e x = deriv h (f x)*N f e x := by
  rw [N,(hh.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp only [smul_apply,smul_eq_mul,N]
lemma L_comp {f : E → ℝ} {h : ℝ → ℝ} {x A e : E}
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h (f x)) :
    L (h ∘ f) A e x = deriv h (f x)*L f A e x+
      (1/2:ℝ)*deriv (deriv h) (f x)*(N f e x)^2 := by
  have hfd := hf.differentiableAt (by norm_num)
  have hhd := hh.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv h) (f x) := by
    convert N_differentiableAt (e := (1:ℝ)) hh using 1
    rfl
  have heq : N (h ∘ f) e =ᶠ[𝓝 x] (fun y => deriv h (f y)*N f e y) := by
    filter_upwards [hf.eventually (by norm_num),
      hfd.continuousAt.preimage_mem_nhds (hh.eventually (by norm_num))] with y hfy hhy
    change ContDiffAt ℝ 2 h (f y) at hhy
    exact N_comp (hfy.differentiableAt (by norm_num)) (hhy.differentiableAt (by norm_num))
  have hd := (hdd.hasDerivAt.comp_hasFDerivAt x hfd.hasFDerivAt).mul
    (N_differentiableAt (e := e) hf).hasFDerivAt
  have hd' := hd.fderiv
  change fderiv ℝ (fun y => deriv h (f y)*N f e y) x = _ at hd'
  unfold L
  rw [N,heq.fderiv_eq,hd',(hhd.hasDerivAt.comp_hasFDerivAt x hfd.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,N,Function.comp_apply]
  ring
end ExactSLECalculus

namespace ExactSLECalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[simp] lemma N_const (c : ℝ) (e x : E) : N (fun _ => c) e x = 0 := by
  rw [N,(hasFDerivAt_const c x).fderiv]; rfl
@[simp] lemma L_const (c : ℝ) (A e x : E) : L (fun _ => c) A e x = 0 := by
  have heq : N (fun _ : E => c) e = (fun _ => (0:ℝ)) := funext (N_const c e)
  simp only [L,heq,N,(hasFDerivAt_const c x).fderiv,(hasFDerivAt_const (0:ℝ) x).fderiv,
    zero_apply,mul_zero,add_zero]
lemma N_add {f g : E → ℝ} {x e : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    N (fun y => f y+g y) e x = N f e x+N g e x := by
  have h := (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y+g y) x = _ at h
  simp only [N,h,add_apply]
lemma L_add {f g : E → ℝ} {x A e : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    L (fun y => f y+g y) A e x = L f A e x+L g A e x := by
  have heq : N (fun y => f y+g y) e =ᶠ[𝓝 x] (fun y => N f e y+N g e y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hfy hgy
    exact N_add (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))
  have h := ((hf.differentiableAt (by norm_num)).hasFDerivAt.add
    (hg.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hd := ((N_differentiableAt (e := e) hf).hasFDerivAt.add
    (N_differentiableAt (e := e) hg).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y+g y) x = _ at h
  change fderiv ℝ (fun y => N f e y+N g e y) x = _ at hd
  unfold L
  rw [N,heq.fderiv_eq,hd,h]
  simp only [add_apply,N]
  ring
lemma N_const_mul {f : E → ℝ} {x e : E} (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    N (fun y => c*f y) e x = c*N f e x := by
  simpa only [N_const,zero_mul,mul_zero,add_zero] using N_mul (differentiableAt_const c) hf (e := e)
lemma L_const_mul {f : E → ℝ} {x A e : E} (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    L (fun y => c*f y) A e x = c*L f A e x := by
  simpa only [N_const,L_const,mul_zero,zero_mul,add_zero] using
    L_mul (contDiffAt_const (c := c)) hf (A := A) (e := e)
end ExactSLECalculus

 

namespace ExactSLEFiniteTilt
noncomputable def sinePower (r : ℝ) (θ : ℝ) : ℝ := Real.sin θ ^ r
noncomputable def angleGenerator (β : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * deriv (deriv f) θ + β * Real.cot θ * deriv f θ

open Filter
open scoped Topology

theorem sinePower_hasDerivAt (r θ : ℝ) (hθ : 0 < Real.sin θ) :
    HasDerivAt (sinePower r) (Real.cos θ * r * Real.sin θ ^ (r - 1)) θ := by
  exact (Real.hasDerivAt_sin θ).rpow_const (Or.inl hθ.ne')

theorem sinePower_secondDeriv (r θ : ℝ) (hθ : 0 < Real.sin θ) :
    deriv (deriv (sinePower r)) θ =
      -Real.sin θ * r * Real.sin θ ^ (r - 1) +
      (Real.cos θ * r) * (Real.cos θ * (r - 1) * Real.sin θ ^ (r - 2)) := by
  have he : deriv (sinePower r) =ᶠ[𝓝 θ]
      (fun x => Real.cos x * r * Real.sin x ^ (r - 1)) := by
    have hp : ∀ᶠ x in 𝓝 θ, 0 < Real.sin x :=
      (isOpen_lt continuous_const Real.continuous_sin).mem_nhds hθ
    filter_upwards [hp] with x hx
    exact (sinePower_hasDerivAt r x hx).deriv
  rw [he.deriv_eq]
  have hd := ((Real.hasDerivAt_cos θ).mul_const r).mul
    ((Real.hasDerivAt_sin θ).rpow_const (p := r - 1) (Or.inl hθ.ne'))
  convert hd.deriv using 1
  congr 2
  ring_nf

theorem angleGenerator_sinePower (β r θ : ℝ) (hθ : 0 < Real.sin θ) :
    angleGenerator β (sinePower r) θ = sinePower r θ *
      (-r / 2 + r * (r - 1 + 2 * β) / 2 * Real.cot θ ^ 2) := by
  unfold angleGenerator
  rw [sinePower_secondDeriv r θ hθ, (sinePower_hasDerivAt r θ hθ).deriv]
  dsimp [sinePower]
  rw [Real.rpow_sub hθ, Real.rpow_sub hθ, Real.rpow_one, Real.rpow_two,
    Real.cot_eq_cos_div_sin]
  have htrig := Real.sin_sq_add_cos_sq θ
  field_simp
  nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]

theorem sine_generator (a r θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    angleGenerator (1 - 2 * a) (sinePower r) θ / sinePower r θ =
      -r / 2 + r * (r - (4 * a - 1)) / 2 * Real.cot θ ^ 2 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [angleGenerator_sinePower _ _ _ hs]
  have hp : sinePower r θ ≠ 0 := (Real.rpow_pos_of_pos hs r).ne'
  field_simp
  ring

theorem green_angle_eigenfunction (a θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    angleGenerator (1 - 2 * a) (sinePower (4 * a - 1)) θ =
      -(4 * a - 1) / 2 * sinePower (4 * a - 1) θ := by
  rw [angleGenerator_sinePower _ _ _ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)]
  ring

theorem tilted_lyapunov (a q θ : ℝ) (_ha : 1 / 4 < a)
    (hq : 0 < q) (hqp : q < 4 * a - 1) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    angleGenerator (2 * a) (sinePower (-q)) θ =
      sinePower (-q) θ * (q / 2 - q * (4 * a - 1 - q) / 2 * Real.cot θ ^ 2) ∧
    angleGenerator (2 * a) (sinePower (-q)) θ ≤ q / 2 * sinePower (-q) θ := by
  have he : angleGenerator (2 * a) (sinePower (-q)) θ =
      sinePower (-q) θ * (q / 2 - q * (4 * a - 1 - q) / 2 * Real.cot θ ^ 2) := by
    rw [angleGenerator_sinePower _ _ _ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)]
    ring
  refine ⟨he, ?_⟩
  rw [he]
  have hf : 0 < sinePower (-q) θ :=
    Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) _
  have hc : 0 ≤ q * (4 * a - 1 - q) / 2 * Real.cot θ ^ 2 := by positivity
  nlinarith

end ExactSLEFiniteTilt

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt
noncomputable def clockExp (a cap lam : ℝ) (v : State) : ℝ :=
  Real.exp (lam*physicalClock a cap v)
noncomputable def angleLift (g : ℝ → ℝ) (v : State) : ℝ := g (physicalTheta v)
lemma clock_N_zero (a cap : ℝ) (v : State) (hv : 0<Y v) :
    N (physicalClock a cap) noise v = 0 := by
  rw [N,(hasFDerivAt_physicalClock a cap v hv).fderiv,clockDeriv_noise]
lemma clock_L (a cap : ℝ) (ha : a≠0) (v : State) (hv : 0<Y v) :
    L (physicalClock a cap) (physicalDrift a v) noise v = (physicalV v)^2 := by
  change (1/2:ℝ)*fderiv ℝ (fun w => fderiv ℝ (physicalClock a cap) w noise) v noise +
    fderiv ℝ (physicalClock a cap) v (physicalDrift a v) = _
  rw [physicalClock_second_noise a cap v hv,physicalClock_drift a cap ha v hv]
  ring
lemma theta_N (v : State) (hv : 0<Y v) : N physicalTheta noise v = physicalV v := by
  rw [N,(hasFDerivAt_physicalTheta v hv).fderiv,thetaDeriv_noise]
lemma theta_L (a : ℝ) (v : State) (hv : 0<Y v) :
    L physicalTheta (physicalDrift a v) noise v =
      (1-2*a)*Real.cot (physicalTheta v)*(physicalV v)^2 := theta_generator a v hv
lemma clockExp_smooth (a cap lam : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ 2 (clockExp a cap lam) v :=
  (contDiffAt_const.mul (physicalClock_smooth a cap v hv)).exp
lemma clockExp_N (a cap lam : ℝ) (v : State) (hv : 0<Y v) :
    N (clockExp a cap lam) noise v = 0 := by
  have he : clockExp a cap lam = Real.exp ∘ (fun w => lam*physicalClock a cap w) := rfl
  rw [he,N_comp ((contDiffAt_const.mul (physicalClock_smooth a cap v hv)).differentiableAt (by norm_num))
    Real.differentiable_exp.differentiableAt]
  rw [N_const_mul ((physicalClock_smooth a cap v hv).differentiableAt (by norm_num)),clock_N_zero a cap v hv]
  ring
lemma clockExp_L (a cap lam : ℝ) (ha : a≠0) (v : State) (hv : 0<Y v) :
    L (clockExp a cap lam) (physicalDrift a v) noise v =
      clockExp a cap lam v*lam*(physicalV v)^2 := by
  have he : clockExp a cap lam = Real.exp ∘ (fun w => lam*physicalClock a cap w) := rfl
  rw [he,L_comp (contDiffAt_const.mul (physicalClock_smooth a cap v hv)) Real.contDiff_exp.contDiffAt,
    L_const_mul (physicalClock_smooth a cap v hv),clock_L a cap ha v hv,
    N_const_mul ((physicalClock_smooth a cap v hv).differentiableAt (by norm_num)),clock_N_zero a cap v hv]
  simp only [Real.deriv_exp]
  change _ = Real.exp (lam*physicalClock a cap v)*lam*(physicalV v)^2
  ring
lemma angleLift_smooth (g : ℝ → ℝ) (v : State) (hv : 0<Y v)
    (hg : ContDiffAt ℝ 2 g (physicalTheta v)) : ContDiffAt ℝ 2 (angleLift g) v :=
  hg.comp v (physicalTheta_smooth v hv)
lemma angleLift_N (g : ℝ → ℝ) (v : State) (hv : 0<Y v)
    (hg : DifferentiableAt ℝ g (physicalTheta v)) :
    N (angleLift g) noise v = deriv g (physicalTheta v)*physicalV v := by
  change N (g ∘ physicalTheta) noise v = _
  rw [N_comp ((physicalTheta_smooth v hv).differentiableAt (by norm_num)) hg,theta_N v hv]
lemma angleLift_L (g : ℝ → ℝ) (a : ℝ) (v : State) (hv : 0<Y v)
    (hg : ContDiffAt ℝ 2 g (physicalTheta v)) :
    L (angleLift g) (physicalDrift a v) noise v =
      angleGenerator (1-2*a) g (physicalTheta v)*(physicalV v)^2 := by
  change L (g ∘ physicalTheta) (physicalDrift a v) noise v = _
  rw [L_comp (physicalTheta_smooth v hv) hg,theta_L a v hv,theta_N v hv]
  dsimp [angleGenerator]
  ring
lemma exponential_angle_generator (g : ℝ → ℝ) (a cap lam : ℝ) (ha : a≠0)
    (v : State) (hv : 0<Y v) (hg : ContDiffAt ℝ 2 g (physicalTheta v)) :
    L (fun w => clockExp a cap lam w*angleLift g w) (physicalDrift a v) noise v =
      clockExp a cap lam v*(lam*g (physicalTheta v)+angleGenerator (1-2*a) g (physicalTheta v))*(physicalV v)^2 := by
  rw [L_mul (clockExp_smooth a cap lam v hv) (angleLift_smooth g v hv hg),
    clockExp_L a cap lam ha v hv,clockExp_N a cap lam v hv,angleLift_L g a v hv hg]
  dsimp only [angleLift]
  ring
lemma sinePower_smooth (r θ : ℝ) (hθ : 0<Real.sin θ) : ContDiffAt ℝ 2 (sinePower r) θ :=
  Real.contDiff_sin.contDiffAt.rpow_const_of_ne hθ.ne'
end ExactSLEGreen

namespace ExactSLEFiniteTilt
noncomputable def regP (a : ℝ) : ℝ := 4*a-1
noncomputable def regQ (a : ℝ) : ℝ := min 1 (regP a)/2
noncomputable def regEta (a : ℝ) : ℝ := (1-regQ a)/(2-regQ a)
noncomputable def regM (a : ℝ) : ℝ := (1+regEta a)/(1-2*regEta a)
noncomputable def regBeta (a : ℝ) : ℝ := min 1 (a/(4*regM a))
noncomputable def regK (a : ℝ) : ℝ := regQ a*(regP a-regQ a)/2
noncomputable def regA (a : ℝ) : ℝ := regP a/2+(regP a-regQ a)*(1+regQ a)/2+2
noncomputable def regH (a : ℝ) : ℝ := (regK a/(2*regA a))^(1/(2-regQ a))
noncomputable def regC (a : ℝ) : ℝ := regA a * regH a ^ (-regP a)
noncomputable def regFactor (a δ θ : ℝ) : ℝ :=
  sinePower (regP a) θ + δ*(1+sinePower (regQ a) θ)
noncomputable def regD (a δ θ : ℝ) : ℝ := δ/regFactor a δ θ * Real.sin θ^(regQ a-2)
noncomputable def regNormalizedDrift (a δ σ θ : ℝ) : ℝ :=
  (angleGenerator (1-2*a) (regFactor a δ) θ + regP a/2 * regFactor a δ θ +
    σ*δ*(1+sinePower (regQ a) θ))/regFactor a δ θ
end ExactSLEFiniteTilt

namespace ExactSLEFiniteTilt

lemma regP_pos {a : ℝ} (ha : 1/4 < a) : 0 < regP a := by dsimp [regP]; linarith
lemma regQ_pos {a : ℝ} (ha : 1/4 < a) : 0 < regQ a := by
  dsimp [regQ]; exact div_pos (lt_min (by norm_num) (regP_pos ha)) (by norm_num)
lemma regQ_lt_one {a : ℝ} (_ha : 1/4 < a) : regQ a < 1 := by
  have hh := min_le_left (1 : ℝ) (regP a)
  dsimp [regQ]; linarith
lemma regQ_lt_p {a : ℝ} (ha : 1/4 < a) : regQ a < regP a := by
  have hh := min_le_right (1 : ℝ) (regP a)
  have hp := regP_pos ha
  dsimp [regQ]; linarith
lemma regEta_pos {a : ℝ} (ha : 1/4 < a) : 0 < regEta a := by
  have hq := regQ_lt_one ha
  exact div_pos (by linarith) (by linarith)
lemma regEta_lt_half {a : ℝ} (ha : 1/4 < a) : regEta a < 1/2 := by
  have hq := regQ_pos ha
  have hq1 := regQ_lt_one ha
  dsimp [regEta]
  apply (div_lt_iff₀ (by linarith)).mpr
  linarith
lemma regEta_identity {a : ℝ} (ha : 1/4 < a) : regEta a*(regQ a-2) = regQ a-1 := by
  have hq := regQ_lt_one ha
  dsimp [regEta]
  field_simp [show 2-regQ a ≠ 0 by linarith]
  ring
lemma regM_pos {a : ℝ} (ha : 1/4 < a) : 0 < regM a := by
  have hη := regEta_pos ha
  have hη1 := regEta_lt_half ha
  exact div_pos (by linarith) (by linarith)
lemma regM_eq {a : ℝ} (ha : 1/4 < a) : regM a = 3/regQ a-2 := by
  have hq := regQ_pos ha
  have hq1 := regQ_lt_one ha
  have hη1 := regEta_lt_half ha
  dsimp only [regM]
  apply (div_eq_iff (show 1-2*regEta a ≠ 0 by linarith)).mpr
  dsimp only [regEta]
  field_simp [show 2-regQ a ≠ 0 by linarith, hq.ne']
  ring
lemma regBeta_pos {a : ℝ} (ha : 1/4 < a) : 0 < regBeta a := by
  exact lt_min (by norm_num) (div_pos (by linarith) (by have := regM_pos ha; positivity))
lemma regBeta_le_one (a : ℝ) : regBeta a ≤ 1 := min_le_left _ _
lemma regBeta_discount {a : ℝ} (ha : 1/4 < a) : 2*regM a*regBeta a < a := by
  have hM := regM_pos ha
  have hb := min_le_right (1 : ℝ) (a/(4*regM a))
  change regBeta a ≤ a/(4*regM a) at hb
  have hm := (le_div_iff₀ (by positivity : 0 < 4*regM a)).mp hb
  nlinarith
lemma regK_pos {a : ℝ} (ha : 1/4 < a) : 0 < regK a := by
  exact div_pos (mul_pos (regQ_pos ha) (sub_pos.mpr (regQ_lt_p ha))) (by norm_num)
lemma regA_pos {a : ℝ} (ha : 1/4 < a) : 0 < regA a := by
  have hp := regP_pos ha
  have hq := regQ_pos ha
  have hpq := sub_pos.mpr (regQ_lt_p ha)
  dsimp [regA]; positivity
lemma reg_base_lt_one {a : ℝ} (ha : 1/4 < a) : regK a/(2*regA a) < 1 := by
  have hp := regP_pos ha
  have hq := regQ_pos ha
  have hpq := sub_pos.mpr (regQ_lt_p ha)
  have hA := regA_pos ha
  apply (div_lt_one (by positivity)).mpr
  have hprod := mul_pos hpq (show 0 < 1+regQ a/2 by linarith)
  dsimp [regK,regA]
  nlinarith
lemma regH_pos {a : ℝ} (ha : 1/4 < a) : 0 < regH a := by
  exact Real.rpow_pos_of_pos (div_pos (regK_pos ha) (by have := regA_pos ha; positivity)) _
lemma regH_lt_one {a : ℝ} (ha : 1/4 < a) : regH a < 1 := by
  have hq1 := regQ_lt_one ha
  exact Real.rpow_lt_one (by have := regK_pos ha; have := regA_pos ha; positivity)
    (reg_base_lt_one ha) (div_pos zero_lt_one (by linarith))
lemma regH_power {a : ℝ} (ha : 1/4 < a) : regH a ^ (regQ a-2) = 2*regA a/regK a := by
  have hq1 := regQ_lt_one ha
  have hk := regK_pos ha
  have hA := regA_pos ha
  dsimp [regH]
  rw [←Real.rpow_mul (by positivity : 0 ≤ regK a/(2*regA a))]
  have he : 1/(2-regQ a)*(regQ a-2) = -1 := by field_simp [show 2-regQ a ≠ 0 by linarith]; ring
  rw [he,Real.rpow_neg_one,inv_div]
lemma regC_pos {a : ℝ} (ha : 1/4 < a) : 0 < regC a :=
  mul_pos (regA_pos ha) (Real.rpow_pos_of_pos (regH_pos ha) _)

end ExactSLEFiniteTilt

namespace ExactSLEFiniteTilt
open Filter
end ExactSLEFiniteTilt
end

end OAI
