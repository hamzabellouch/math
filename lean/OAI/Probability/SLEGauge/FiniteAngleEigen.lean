import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.GlobalAngleBudget
import OAI.Probability.SLEGauge.JacobiKernel

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator ExactSLEMain

def angleEigenCutoff (g : ℝ → ℝ) (a cap lam ε : ℝ) (N : ℝ≥0) (v : State) : ℝ :=
  greenCutoff a ε N v * (clockExp a cap lam v * angleLift g v)

lemma angleEigenCutoff_smooth (g : ℝ → ℝ)
    (hg : ∀ θ ∈ Ioo 0 Real.pi, ContDiffAt ℝ (↑(⊤ : ℕ∞)) g θ)
    (a cap lam ε : ℝ) (hε : 0<ε) (N : ℝ≥0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (angleEigenCutoff g a cap lam ε N) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : 0<Y v
  · exact (greenCutoff_smooth a ε hε N).contDiffAt.mul
      ((clockExp_smooth_all a cap lam v hv).mul
        ((hg _ (physicalTheta_mem v)).comp v (physicalTheta_smooth_all v hv)))
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    have hv' : Y v < ε/4 := lt_of_le_of_lt (le_of_not_gt hv) (by positivity)
    filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Iio_mem_nhds hv')] with w hw
    simp only [angleEigenCutoff,greenCutoff,heightTurn_zero hε (le_of_lt hw),
      mul_zero,zero_mul]

lemma angleEigenCutoff_compact (g : ℝ → ℝ) (a cap lam ε : ℝ) (N : ℝ≥0) :
    HasCompactSupport (angleEigenCutoff g a cap lam ε N) :=
  (greenCutoff_compact a ε N).mul_right

lemma angleEigenCutoff_eq_near (g : ℝ → ℝ) (a cap lam ε : ℝ) (hε : 0<ε)
    (N : ℝ≥0) (v : State) (hv : ‖v‖≤N) (hy : ε≤Y v) :
    angleEigenCutoff g a cap lam ε N =ᶠ[𝓝 v]
      fun w => physicalGreen a w * (clockExp a cap lam w * angleLift g w) :=
  (greenCutoff_eq_near a ε hε N v hv hy).mul (EventuallyEq.refl _ _)

lemma angleEigenCutoff_generator (g : ℝ → ℝ)
    (hg : ∀ θ ∈ Ioo 0 Real.pi, ContDiffAt ℝ 2 g θ)
    (a cap lam ε : ℝ) (ha : a≠0)
    (heigen : ∀ θ ∈ Ioo 0 Real.pi, angleGenerator (2*a) g θ = -lam*g θ)
    (hε : 0<ε) (N : ℝ≥0) (v : State) (hv : ‖v‖≤N) (hy : ε≤Y v) :
    generator (angleEigenCutoff g a cap lam ε N) (cutoffDrift a ε) noise v = 0 := by
  have he := angleEigenCutoff_eq_near g a cap lam ε hε N v hv hy
  have hd : (fun w => fderiv ℝ (angleEigenCutoff g a cap lam ε N) w noise) =ᶠ[𝓝 v]
      (fun w => fderiv ℝ (fun u => physicalGreen a u *
        (clockExp a cap lam u * angleLift g u)) w noise) :=
    he.fderiv.mono (fun w hw => congrArg (fun f : State →L[ℝ] ℝ => f noise) hw)
  change (1/2:ℝ) * fderiv ℝ (fun w => fderiv ℝ
    (angleEigenCutoff g a cap lam ε N) w noise) v noise +
    fderiv ℝ (angleEigenCutoff g a cap lam ε N) v (cutoffDrift a ε v) = 0
  rw [hd.fderiv_eq,he.fderiv_eq,cutoffDrift_eq_physical a ε v hy]
  change L (fun w => physicalGreen a w * (clockExp a cap lam w * angleLift g w))
    (physicalDrift a v) noise v = 0
  rw [green_exponential_angle_generator g a cap lam ha v (hε.trans_le hy)
    (hg _ (physicalTheta_mem v)),heigen _ (physicalTheta_mem v)]
  ring

 
theorem local_angle_eigen (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (g : ℝ → ℝ) (hg : ∀ θ ∈ Ioo 0 Real.pi, ContDiffAt ℝ (↑(⊤ : ℕ∞)) g θ)
    (a cap lam ε : ℝ) (ha : a≠0)
    (heigen : ∀ θ ∈ Ioo 0 Real.pi, angleGenerator (2*a) g θ = -lam*g θ)
    (hε : 0<ε) (z : ℂ) (N B : ℝ≥0) (T : ExactSLEGenerator.Driver → ℝ≥0)
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hTB : ∀ b, T b≤B)
    (hsafe : ∀ b t, t≤T b → ε≤Y (localState a ε hε z t b) ∧
      ‖localState a ε hε z t b‖≤N) :
    Integrable (fun b => physicalGreen a (localState a ε hε z (T b) b) *
      (clockExp a cap lam (localState a ε hε z (T b) b) *
        angleLift g (localState a ε hε z (T b) b))) W ∧
    (∫ b, physicalGreen a (localState a ε hε z (T b) b) *
      (clockExp a cap lam (localState a ε hε z (T b) b) *
        angleLift g (localState a ε hε z (T b) b)) ∂W) =
      physicalGreen a (z,0) * (clockExp a cap lam (z,0) * angleLift g (z,0)) := by
  let V := localState a ε hε z
  let f := angleEigenCutoff g a cap lam ε N
  let D := generator f (cutoffDrift a ε) noise
  have hf := angleEigenCutoff_smooth g hg a cap lam ε hε N
  have hfc := angleEigenCutoff_compact g a cap lam ε N
  have he (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (ht : t≤T b) :
      f (V t b) = physicalGreen a (V t b) * (clockExp a cap lam (V t b)*angleLift g (V t b)) :=
    (angleEigenCutoff_eq_near g a cap lam ε hε N _ (hsafe b t ht).2
      (hsafe b t ht).1).eq_of_nhds
  have hgen (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (ht : t≤T b) : D (V t b)=0 :=
    angleEigenCutoff_generator g (fun θ hθ => (hg θ hθ).of_le (by norm_cast))
      a cap lam ε ha heigen hε N _ (hsafe b t ht).2 (hsafe b t ht).1
  have hDy := compact_test_stopped_dynkin W hW V
    (localState_continuous a ε hε z) (localState_adapted a ε hε z)
    (cutoffDrift a ε) (cutoffDrift_lipschitz a ε hε).continuous
    (max (|a|/ε) (|a|/ε^2)) (by positivity) (cutoffDrift_bound a ε hε) noise
    (by simp [noise,Prod.norm_def]) (localState_eq a ε hε z) f hf hfc T B hT hTB
  have hzero (b : ExactSLEGenerator.Driver) : (∫ u in (0:ℝ)..(T b : ℝ), generator f (cutoffDrift a ε) noise (V u.toNNReal b)) = 0 := by
    rw [intervalIntegral.integral_of_le (T b).coe_nonneg]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    exact hgen b u.toNNReal (by simpa using Real.toNNReal_le_toNNReal hu.2)
  have hinit (b : ExactSLEGenerator.Driver) : f (V 0 b) =
      physicalGreen a (z,0)*(clockExp a cap lam (z,0)*angleLift g (z,0)) := by
    rw [he b 0 bot_le]
    simp only [V,localState_zero]
  refine ⟨by simpa only [he _ _ le_rfl] using hDy.1, ?_⟩
  have hd := hDy.2.2
  simp_rw [hinit,he _ _ le_rfl,hzero] at hd
  simpa only [integral_const,probReal_univ,one_smul,integral_zero,add_zero] using hd

 

theorem finite_level_angle_eigen (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (g : ℝ → ℝ) (hg : ∀ θ ∈ Ioo 0 Real.pi, ContDiffAt ℝ (↑(⊤ : ℕ∞)) g θ)
    (C : ℝ) (hC : 0≤C) (hbound : ∀ θ ∈ Ioo 0 Real.pi, ‖g θ‖≤C)
    (a lam : ℝ) (ha : 1/4<a) (hlam : 0≤lam)
    (heigen : ∀ θ ∈ Ioo 0 Real.pi, angleGenerator (2*a) g θ = -lam*g θ)
    (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : 0≤ s) :
    Integrable (fun b : ExactSLEGenerator.Driver => radialTestWeight a (angleLift g) b.1 z
      (levelRadius a (2*z.im) s)) W ∧
    (∫ b, radialTestWeight a (angleLift g) b.1 z
      (levelRadius a (2*z.im) s) ∂W) =
      physicalGreen a (z,0) * Real.exp (-lam*s) * g (physicalTheta (z,0)) := by
  have ha0 : 0<a := by linarith
  let cap := 2*z.im
  have hcap : 0<cap := by dsimp [cap]; positivity
  let ρ := levelRadius a cap s
  have hρ : 0<ρ := levelRadius_pos a cap s hcap
  have hr : ρ≤z.im := by
    simpa only [cap,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using
      (levelRadius_le ha0 hcap hs)
  let L (n : ℕ) := radialLocalization a ha0 z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T (n : ℕ) := radialStop a ha0 z hz ρ hρ hr n
  let V (n : ℕ) (b : ExactSLEGenerator.Driver) := localState a (L n).ε (L n).hε z (T n b) b
  let f (n : ℕ) (b : ExactSLEGenerator.Driver) := physicalGreen a (V n b)*
    (clockExp a cap lam (V n b)*angleLift g (V n b))
  let F (b : ExactSLEGenerator.Driver) := Real.exp (lam*s)*radialTestWeight a (angleLift g) b.1 z ρ
  have hsafe (n : ℕ) (b : ExactSLEGenerator.Driver) (u : ℝ≥0) (hu : u≤T n b) :
      (L n).ε≤Y (localState a (L n).ε (L n).hε z u b) ∧
        ‖localState a (L n).ε (L n).hε z u b‖≤(L n).N := by
    have h := regionStop_safe a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
      (L n).B (L n).initial b u hu
    exact ⟨h.1,h.2.1⟩
  have hact (n : ℕ) (b : ExactSLEGenerator.Driver) : alive a b.1 (T n b) z ∧
      actualState a b.1 (T n b) z = V n b :=
    regionStop_actualState a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
      (L n).B (L n).initial b _ le_rfl
  have hc (n : ℕ) (b : ExactSLEGenerator.Driver) : physicalClock a cap (V n b)≤ s := by
    rw [←(hact n b).2]
    have h := actual_physicalClock_le a ha0 z hz cap ρ hcap hρ hr b (T n b)
      (hact n b).1 (radialStop_le_radialTime a ha0 z hz ρ hρ hr n b)
    simpa only [ρ,levelRadius_clock ha0.ne' hcap] using h
  have hfi (n : ℕ) : Integrable (f n) W ∧
      (∫ b, f n b ∂W)=physicalGreen a (z,0)*angleLift g (z,0) := by
    have h := local_angle_eigen W hW g hg a cap lam (L n).ε ha0.ne' heigen (L n).hε
      z (L n).N (L n).B (T n) (radialStop_stopping a ha0 z hz ρ hρ hr n)
      (regionStop_le a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B)
      (hsafe n)
    refine ⟨h.1, ?_⟩
    have hi : clockExp a cap lam (z,0) = 1 := by
      simp only [cap,clockExp,physicalClock_initial,mul_zero,Real.exp_zero]
    simpa only [hi,one_mul] using h.2
  have hfactor (n : ℕ) (b : ExactSLEGenerator.Driver) :
      ‖clockExp a cap lam (V n b)*angleLift g (V n b)‖ ≤ Real.exp (lam*s)*C := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (show 0 < clockExp a cap lam (V n b) from Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hc n b) hlam))
      (hbound _ (physicalTheta_mem _)) (norm_nonneg _) (Real.exp_pos _).le
  have hb (n : ℕ) (b : ExactSLEGenerator.Driver) :
      ‖f n b‖ ≤ radialApproximation a ha0 z hz ρ hρ hr n b*(Real.exp (lam*s)*C) := by
    change ‖physicalGreen a (V n b)*(clockExp a cap lam (V n b)*angleLift g (V n b))‖≤_
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (show 0 < physicalGreen a (V n b) from Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hfactor n b) (Real.exp_pos _).le
  have hlim (b : ExactSLEGenerator.Driver) : Tendsto (fun n => f n b) atTop (𝓝 (F b)) := by
    by_cases ht : radialTime a b.1 z ρ=∞
    · have hF : F b=0 := by simp only [F,radialTestWeight,ite_eq_left ht,mul_zero]
      rw [hF]
      have hG := radialApproximation_tendsto a ha ha0 z hz ρ hρ hr b
      have hG0 : radialWeight a b.1 z ρ=0 := by simp only [radialWeight,ite_eq_left ht]
      rw [hG0] at hG
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero (fun n => norm_nonneg _) (fun n => hb n b)
      simpa only [zero_mul] using hG.mul_const (Real.exp (lam*s)*C)
    · apply tendsto_const_nhds.congr'
      filter_upwards [radialStop_eventually_eq a ha0 z hz ρ hρ hr b ht] with n hn
      have he : T n b=(radialTime a b.1 z ρ).toNNReal := by
        have hh := congrArg ENNReal.toNNReal hn
        simpa only [ENNReal.toNNReal_coe] using hh
      have hv : V n b=actualState a b.1 (radialTime a b.1 z ρ).toNNReal z := by
        rw [←(hact n b).2,he]
      have hclock : physicalClock a cap (V n b)=s := by
        rw [hv,actual_physicalClock_at a ha0 z hz cap ρ hcap hρ hr b ht]
        exact levelRadius_clock ha0.ne' hcap
      dsimp only [f,F]
      rw [clockExp,hclock,radialTestWeight,ite_eq_right ht,hv]
      ring
  let bound := Real.exp (-alpha a*Real.log ρ)*(Real.exp (lam*s)*C)
  have hbnd (n : ℕ) : ∀ᵐ b ∂W, ‖f n b‖≤bound := Eventually.of_forall fun b =>
    (hb n b).trans (mul_le_mul_of_nonneg_right
      (radialApproximation_bound a ha ha0 z hz ρ hρ hr n b).2
      (mul_nonneg (Real.exp_pos _).le hC))
  have hFm : AEStronglyMeasurable F W := aestronglyMeasurable_of_tendsto_ae
    atTop (fun n => (hfi n).1.aestronglyMeasurable)
    (Eventually.of_forall hlim)
  have hFi : Integrable F W := Integrable.of_bound hFm bound (by
    filter_upwards [] with b
    exact le_of_tendsto (hlim b).norm (Eventually.of_forall fun n =>
      (hb n b).trans (mul_le_mul_of_nonneg_right
        (radialApproximation_bound a ha ha0 z hz ρ hρ hr n b).2
        (mul_nonneg (Real.exp_pos _).le hC))))
  have hexp : Real.exp (-lam*s)*Real.exp (lam*s)=1 := by
    rw [←Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  have hconst : (fun b : ExactSLEGenerator.Driver => radialTestWeight a (angleLift g) b.1 z ρ) =
      fun b => Real.exp (-lam*s)*F b := by
    funext b
    dsimp only [F]
    rw [←mul_assoc,hexp,one_mul]
  have hint : (∫ b, F b ∂W)=physicalGreen a (z,0)*angleLift g (z,0) := by
    have hconv := tendsto_integral_of_dominated_convergence (fun _ : ExactSLEGenerator.Driver => bound)
      (fun n => (hfi n).1.aestronglyMeasurable) (integrable_const bound) hbnd
      (Eventually.of_forall hlim)
    apply tendsto_nhds_unique hconv
    simpa only [(hfi _).2] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => physicalGreen a (z,0)*angleLift g (z,0))
        atTop (𝓝 (physicalGreen a (z,0)*angleLift g (z,0))))
  change Integrable (fun b : ExactSLEGenerator.Driver => radialTestWeight a (angleLift g) b.1 z ρ) W ∧ _
  rw [hconst]
  refine ⟨hFi.const_mul _, ?_⟩
  rw [integral_const_mul,hint]
  dsimp only [angleLift]
  ring

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.Jacobi
open ExactSLEGreen ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator ExactSLEMain

def anglePoly (nu : ℝ) (n : ℕ) (θ : ℝ) : ℝ := (poly nu n).eval (Real.cos θ)

lemma eval_cos_deriv (p : ℝ[X]) (θ : ℝ) :
    deriv (fun θ => p.eval (Real.cos θ)) θ = p.derivative.eval (Real.cos θ)*(-Real.sin θ) :=
  ((p.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).deriv

lemma eval_cos_second (p : ℝ[X]) (θ : ℝ) :
    deriv (deriv (fun θ => p.eval (Real.cos θ))) θ =
      p.derivative.derivative.eval (Real.cos θ)*Real.sin θ^2
      -p.derivative.eval (Real.cos θ)*Real.cos θ := by
  have he : deriv (fun θ => p.eval (Real.cos θ)) =
      fun θ => p.derivative.eval (Real.cos θ)*(-Real.sin θ) := funext (eval_cos_deriv p)
  rw [he]
  have hd := (((p.derivative.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).mul
    (Real.hasDerivAt_sin θ).neg).deriv
  change deriv (fun θ => p.derivative.eval (Real.cos θ)*(-Real.sin θ)) θ = _ at hd
  rw [hd]
  dsimp only [Function.comp_apply, Pi.neg_apply]
  ring

lemma angleGenerator_poly (p : ℝ[X]) (nu : ℝ) (θ : ℝ) (hθ : 0<Real.sin θ) :
    angleGenerator (nu/2) (fun θ => p.eval (Real.cos θ)) θ =
      (operator nu p).eval (Real.cos θ)/2 := by
  rw [angleGenerator,eval_cos_second,eval_cos_deriv]
  simp only [operator,eval_sub,eval_mul,eval_pow,eval_one,eval_X,eval_C,Real.cot_eq_cos_div_sin]
  have hid := Real.sin_sq_add_cos_sq θ
  field_simp
  linear_combination p.derivative.derivative.eval (Real.cos θ) * hid

lemma anglePoly_smooth (nu : ℝ) (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (anglePoly nu n) := by
  change ContDiff ℝ _ ((fun x : ℝ => (poly nu n).eval x) ∘ Real.cos)
  have hp (p : ℝ[X]) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => p.eval x) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [eval_add] using hp.add hq
    | monomial n c =>
      simp only [eval_monomial]
      exact (contDiff_const (c:=c)).mul (contDiff_id.pow n)
  exact (hp _).comp Real.contDiff_cos

lemma anglePoly_bound (nu : ℝ) (hnu : 0<nu) (n : ℕ) (θ : ℝ) :
    ‖anglePoly nu n θ‖≤(2:ℝ)^n :=
  poly_eval_bound nu hnu n (Real.cos θ) (Real.abs_cos_le_one θ)

lemma anglePoly_eigen (a : ℝ) (n : ℕ) (θ : ℝ) (hθ : θ∈Ioo 0 Real.pi) :
    angleGenerator (2*a) (anglePoly (4*a) n) θ = -eigenvalue (4*a) n*anglePoly (4*a) n θ := by
  rw [show 2*a=(4*a)/2 by ring]
  unfold anglePoly
  rw [angleGenerator_poly _ _ _ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2),poly_eigen]
  simp only [eval_mul,eval_neg,eval_C,eigenvalue]
  ring

theorem finite_angle_poly (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    Integrable (fun b : ExactSLEGenerator.Driver =>
      radialTestWeight a (angleLift (anglePoly (4*a) n)) b.1 z (levelRadius a (2*z.im) s)) W ∧
    (∫ b, radialTestWeight a (angleLift (anglePoly (4*a) n)) b.1 z (levelRadius a (2*z.im) s) ∂W)=
      physicalGreen a (z,0)*Real.exp (-s*eigenvalue (4*a) n)*
        (poly (4*a) n).eval (Real.cos (physicalTheta (z,0))) := by
  simpa only [mul_comm (eigenvalue (4*a) n) s,neg_mul,anglePoly] using
    finite_level_angle_eigen W hW (anglePoly (4*a) n)
      (fun θ _ => (anglePoly_smooth (4*a) n).contDiffAt) (2^n) (by positivity)
      (fun θ _ => anglePoly_bound (4*a) (by linarith) n θ) a (eigenvalue (4*a) n) ha
      (eigenvalue_nonneg (4*a) (by linarith) n) (anglePoly_eigen a n) z hz s hs

end SLEExactGauge.Jacobi
end
end
 

 
section
 

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.Jacobi
open ExactSLEGreen ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator ExactSLEMain

lemma radialState_measurable (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) :
    Measurable (fun b : ExactSLEGenerator.Driver => radialState a b.1 z ρ) := by
  have he : z.im*(ρ/z.im)=ρ := mul_div_cancel₀ _ hz.ne'
  simpa only [Function.comp_def, id_eq, he] using (joint_radialState_measurable a ha (ρ/z.im) (div_pos hρ hz)
    ((div_le_one hz).mpr hr)).comp
      (measurable_id.prodMk (measurable_const (a:= (⟨z,hz⟩ : UpperPlane))))

lemma radialWeight_measurable (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) :
    Measurable (fun b : ExactSLEGenerator.Driver => radialWeight a b.1 z ρ) := by
  have he : z.im*(ρ/z.im)=ρ := mul_div_cancel₀ _ hz.ne'
  simpa only [Function.comp_def, id_eq, he] using (joint_radialWeight_measurable a ha (ρ/z.im) (div_pos hρ hz)
    ((div_le_one hz).mpr hr)).comp
      (measurable_id.prodMk (measurable_const (a:= (⟨z,hz⟩ : UpperPlane))))

def cosState (v : State) : Interval :=
  ⟨Real.cos (physicalTheta v),Real.neg_one_le_cos _,Real.cos_le_one _⟩

lemma cosState_measurable : Measurable cosState := by
  unfold cosState physicalTheta
  fun_prop

def finiteCos (a : ℝ) (z : ℂ) (ρ : ℝ) (b : ExactSLEGenerator.Driver) : Interval :=
  cosState (radialState a b.1 z ρ)

lemma finiteCos_measurable (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) : Measurable (finiteCos a z ρ) :=
  cosState_measurable.comp (radialState_measurable a ha z hz ρ hρ hr)

 
def finiteCosLaw (W : Measure ExactSLEGenerator.Driver) (a : ℝ) (z : ℂ) (s : ℝ) : Measure Interval :=
  (radialLaw W a z (levelRadius a (2*z.im) s)).map (finiteCos a z (levelRadius a (2*z.im) s))

lemma levelRadius_initial_le (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (s : ℝ) (hs : 0 ≤ s) : levelRadius a (2*z.im) s≤z.im := by
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using
    levelRadius_le ha (by positivity : 0<2*z.im) hs

lemma finiteCosLaw_probability (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : 0 ≤ s) :
    IsProbabilityMeasure (finiteCosLaw W a z s) := by
  have hρ := levelRadius_pos a (2*z.im) s (by positivity)
  have hr := levelRadius_initial_le a (by linarith) z hz s hs
  have := radialLaw_probability W hW a ha z hz _ hρ hr
  exact (Measure.isProbabilityMeasure_map_iff
    (finiteCos_measurable a (by linarith) z hz _ hρ hr).aemeasurable).mpr inferInstance

lemma finiteCosLaw_poly_integral (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    (∫ w : Interval,(poly (4*a) n).eval (w:ℝ) ∂finiteCosLaw W a z s)=
      Real.exp (-s*eigenvalue (4*a) n)*(poly (4*a) n).eval (cosState (z,0):ℝ) := by
  have hρ := levelRadius_pos a (2*z.im) s (by positivity)
  have hr := levelRadius_initial_le a (by linarith) z hz s hs
  let ρ := levelRadius a (2*z.im) s
  have hG : 0<physicalGreen a (z,0) := Real.exp_pos _
  have hf : AEStronglyMeasurable (fun w : Interval => (poly (4*a) n).eval (w:ℝ)) (finiteCosLaw W a z s) :=
    ((poly (4*a) n).continuous.comp continuous_subtype_val).aestronglyMeasurable
  rw [finiteCosLaw,integral_map (finiteCos_measurable a (by linarith) z hz ρ hρ hr).aemeasurable hf]
  rw [radialLaw,integral_withDensity_eq_integral_toReal_smul
    ((radialWeight_measurable a ha z hz ρ hρ hr).div_const _).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hn (b : ExactSLEGenerator.Driver) : 0≤radialWeight a b.1 z ρ/physicalGreen a (z,0) :=
    div_nonneg (radialWeight_bound a ha z hz ρ hρ hr b).1 hG.le
  simp_rw [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
  have he (b : ExactSLEGenerator.Driver) :
      (radialWeight a b.1 z ρ/physicalGreen a (z,0))*(poly (4*a) n).eval (finiteCos a z ρ b:ℝ)=
        radialTestWeight a (angleLift (anglePoly (4*a) n)) b.1 z ρ/physicalGreen a (z,0) := by
    rw [radialTestWeight_eq_mul]
    dsimp only [finiteCos,cosState,angleLift,anglePoly]
    ring
  simp_rw [he]
  rw [integral_div,(finite_angle_poly W hW a ha z hz s hs n).2]
  dsimp only [cosState]
  field_simp

 

theorem finiteCosLaw_eq_transition (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : mixingTime (4*a) ≤ s) :
    finiteCosLaw W a z s=transition (4*a) s (cosState (z,0)) := by
  have hs0 : 0 ≤ s := le_trans (by unfold mixingTime majorantBase; positivity) hs
  have := finiteCosLaw_probability W hW a ha z hz s hs0
  exact transition_identified (4*a) (by linarith) s hs _ _
    (finiteCosLaw_poly_integral W hW a ha z hz s hs0)

 
theorem finiteCosLaw_integral_bounds (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : mixingTime (4*a) ≤ s)
    (f : Interval→ℝ≥0∞) (hf : Measurable f) :
    (1/2:ℝ≥0∞)*(∫⁻w,f w∂pi (4*a))≤∫⁻w,f w∂finiteCosLaw W a z s ∧
      (∫⁻w,f w∂finiteCosLaw W a z s)≤2*(∫⁻w,f w∂pi (4*a)) := by
  rw [finiteCosLaw_eq_transition W hW a ha z hz s hs]
  exact transition_lintegral_bounds (4*a) (by linarith) s hs _ f hf

end SLEExactGauge.Jacobi
end
end
 

 
section
 

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.Jacobi
open CenteredMoments ExactSLEGreen ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator ExactSLEMain

def arccosAngle (x : Interval) : Angle :=
  if h : Real.arccos (x:ℝ) ∈ Ioo 0 Real.pi then ⟨Real.arccos (x:ℝ),h⟩
  else ⟨Real.pi/2,by constructor <;> linarith [Real.pi_pos]⟩

lemma arccosAngle_measurable : Measurable arccosAngle := by
  suffices Measurable (fun x : Interval => (arccosAngle x : ℝ)) from this.subtype_mk
  simp only [arccosAngle,apply_dite,dite_eq_ite]
  exact (Real.continuous_arccos.measurable.comp measurable_subtype_coe).ite
    ((Real.continuous_arccos.measurable.comp measurable_subtype_coe) measurableSet_Ioo)
    measurable_const

@[simp] lemma arccosAngle_angleCos (θ : Angle) : arccosAngle (angleCos θ)=θ := by
  have hc : Real.arccos (Real.cos (θ:ℝ))=(θ:ℝ) := Real.arccos_cos θ.2.1.le θ.2.2.le
  have hh : Real.arccos (angleCos θ : ℝ)∈Ioo 0 Real.pi := by
    change Real.arccos (Real.cos (θ:ℝ))∈Ioo 0 Real.pi
    rw [hc]
    exact θ.2
  apply Subtype.ext
  simp only [arccosAngle,dite_eq_left hh]
  exact hc

def angleState (v : State) : Angle := ⟨physicalTheta v,physicalTheta_mem v⟩

lemma angleState_measurable : Measurable angleState := by
  unfold angleState physicalTheta
  fun_prop

lemma arccosAngle_cosState (v : State) : arccosAngle (cosState v)=angleState v :=
  arccosAngle_angleCos (angleState v)

def finiteAngle (a : ℝ) (z : ℂ) (ρ : ℝ) (b : ExactSLEGenerator.Driver) : Angle :=
  angleState (radialState a b.1 z ρ)

lemma finiteAngle_measurable (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) : Measurable (finiteAngle a z ρ) :=
  angleState_measurable.comp (radialState_measurable a ha z hz ρ hρ hr)

def finiteAngleLaw (W : Measure ExactSLEGenerator.Driver) (a : ℝ) (z : ℂ) (s : ℝ) : Measure Angle :=
  (radialLaw W a z (levelRadius a (2*z.im) s)).map (finiteAngle a z (levelRadius a (2*z.im) s))

lemma finiteCosLaw_map_arccos (W : Measure ExactSLEGenerator.Driver)
    (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : 0≤ s) :
    (finiteCosLaw W a z s).map arccosAngle=finiteAngleLaw W a z s := by
  have hρ := levelRadius_pos a (2*z.im) s (by positivity : 0<2*z.im)
  have hr := levelRadius_initial_le a ha z hz s hs
  rw [finiteCosLaw,Measure.map_map arccosAngle_measurable
    (finiteCos_measurable a ha z hz _ hρ hr)]
  congr 1
  funext b
  exact arccosAngle_cosState _

lemma pi_map_arccos (a : ℝ) (ha : 1<4*a) : (pi (4*a)).map arccosAngle=angleLaw a := by
  rw [←map_angleLaw_eq_pi a ha,Measure.map_map arccosAngle_measurable angleCos_measurable]
  simp only [Function.comp_def,arccosAngle_angleCos,Measure.map_id']

 

theorem finiteAngleLaw_integral_bounds (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : mixingTime (4*a)≤ s)
    (f : Angle→ℝ≥0∞) (hf : Measurable f) :
    (1/2:ℝ≥0∞)*(∫⁻θ,f θ∂angleLaw a)≤∫⁻θ,f θ∂finiteAngleLaw W a z s ∧
      (∫⁻θ,f θ∂finiteAngleLaw W a z s)≤2*(∫⁻θ,f θ∂angleLaw a) := by
  have hs0 : 0≤ s := le_trans (by unfold mixingTime majorantBase; positivity) hs
  rw [←pi_map_arccos a (by linarith),←finiteCosLaw_map_arccos W a (by linarith) z hz s hs0]
  simp only [lintegral_map hf arccosAngle_measurable]
  exact finiteCosLaw_integral_bounds W hW a ha z hz s hs (f ∘ arccosAngle)
    (hf.comp arccosAngle_measurable)

 

theorem finiteAngleLaw_inverse_power_finite (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : mixingTime (4*a)≤ s) :
    (∫⁻θ : Angle,ENNReal.ofReal ((Real.sin θ)^(-p a))∂finiteAngleLaw W a z s)<∞ := by
  apply lt_of_le_of_lt (finiteAngleLaw_integral_bounds W hW a ha z hz s hs _ (by fun_prop)).2
  exact ENNReal.mul_lt_top (by norm_num) (angle_inverse_power_finite a)

end SLEExactGauge.Jacobi
end
end

end OAI
