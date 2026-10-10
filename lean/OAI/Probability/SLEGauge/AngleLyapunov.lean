import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RawBrownianRestart

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExactSLEFiniteTilt

 
lemma exists_tilted_coercivity {a q : ℝ} (ha : 1/4<a) (hq : 0<q)
    (hqp : q<4*a-1) :
    ∃ C : ℝ, 0<C ∧ ∀ θ∈Ioo 0 Real.pi,
      angleGenerator (2*a) (sinePower (-q)) θ + sinePower (-q) θ ≤ C := by
  let A := q/2+1
  let K := q*(4*a-1-q)/2
  have hA : 0<A := by dsimp [A]; linarith
  have hK : 0<K := by dsimp [K]; exact div_pos (mul_pos hq (by linarith)) (by norm_num)
  let δ := Real.sqrt (K/(A+K))
  have hδ : 0<δ := Real.sqrt_pos.mpr (div_pos hK (add_pos hA hK))
  have hδ2 : δ^2=K/(A+K) := Real.sq_sqrt (by positivity)
  have hδK : (A+K)*δ^2=K := by rw [hδ2]; field_simp
  refine ⟨A*δ^(-q), mul_pos hA (Real.rpow_pos_of_pos hδ _), ?_⟩
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hF : 0 < sinePower (-q) θ := Real.rpow_pos_of_pos hs _
  rw [(tilted_lyapunov a q θ ha hq hqp hθ).1]
  change sinePower (-q) θ * (q/2-K*Real.cot θ^2)+sinePower (-q) θ≤_
  by_cases hx : δ≤Real.sin θ
  · have hle : sinePower (-q) θ ≤ δ^(-q) :=
      Real.rpow_le_rpow_of_nonpos hδ hx (by linarith)
    have hn : 0 ≤ sinePower (-q) θ * (K*Real.cot θ^2) :=
      mul_nonneg hF.le (mul_nonneg hK.le (sq_nonneg _))
    have hh := mul_le_mul_of_nonneg_left hle hA.le
    dsimp only [A] at hh ⊢
    nlinarith only [hh,hn]
  · have hx' : Real.sin θ ≤ δ := (lt_of_not_ge hx).le
    have hx2 : Real.sin θ^2≤δ^2 := pow_le_pow_left₀ hs.le hx' 2
    have hsq := Real.sin_sq_add_cos_sq θ
    have hk : A*(Real.sin θ)^2 ≤ K*(Real.cos θ)^2 := by
      have hh := mul_le_mul_of_nonneg_left hx2 (add_pos hA hK).le
      rw [hδK] at hh
      nlinarith only [hh, congrArg (fun x => K*x) hsq]
    have hcot : A ≤ K*Real.cot θ^2 := by
      rw [Real.cot_eq_cos_div_sin, div_pow, ← mul_div_assoc]
      exact (le_div_iff₀ (sq_pos_of_pos hs)).mpr hk
    have hh := mul_le_mul_of_nonneg_left hcot hF.le
    have hc : 0≤A*δ^(-q) := by positivity
    dsimp only [A] at hh
    nlinarith only [hh,hc]

end ExactSLEFiniteTilt

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt

lemma physicalTheta_smooth_all (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) physicalTheta v :=
  contDiffAt_const.sub ((X.contDiff.contDiffAt.div Y.contDiff.contDiffAt hv.ne').arctan)

lemma physicalClock_smooth_all (a cap : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (physicalClock a cap) v :=
  ((contDiffAt_const.add J.contDiff.contDiffAt).sub
    (Y.contDiff.contDiffAt.log hv.ne')).div_const (2*a)

lemma clockExp_smooth_all (a cap lam : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (clockExp a cap lam) v :=
  (contDiffAt_const.mul (physicalClock_smooth_all a cap v hv)).exp

lemma angleLift_sinePower_smooth_all (q : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (angleLift (sinePower q)) v := by
  have hp := physicalTheta_mem v
  exact ((physicalTheta_smooth_all v hv).sin).rpow_const_of_ne
    (Real.sin_pos_of_pos_of_lt_pi hp.1 hp.2).ne'

lemma green_exponential_angle_generator (g : ℝ → ℝ) (a cap lam : ℝ) (ha : a≠0)
    (v : State) (hv : 0<Y v) (hg : ContDiffAt ℝ 2 g (physicalTheta v)) :
    L (fun w => physicalGreen a w * (clockExp a cap lam w*angleLift g w))
      (physicalDrift a v) noise v =
      physicalGreen a v * clockExp a cap lam v *
        (lam*g (physicalTheta v)+angleGenerator (2*a) g (physicalTheta v))*(physicalV v)^2 := by
  rw [green_product_generator a ha _ v hv ((clockExp_smooth a cap lam v hv).mul
    (angleLift_smooth g v hv hg))]
  rw [centeredGenerator,exponential_angle_generator g a cap lam ha v hv hg,
    N_mul ((clockExp_smooth a cap lam v hv).differentiableAt (by norm_num))
      ((angleLift_smooth g v hv hg).differentiableAt (by norm_num)),
    clockExp_N a cap lam v hv, angleLift_N g v hv (hg.differentiableAt (by norm_num))]
  simp only [angleGenerator,physicalTheta_cot,physicalV,noiseLog,p]
  field_simp [(Q_pos hv).ne']
  ring

 

def angleBudgetFactor (a q cap s C : ℝ) (v : State) : ℝ :=
  clockExp a cap 1 v * (angleLift (sinePower (-q)) v - C) + C*Real.exp s

lemma angleBudgetFactor_smooth (a q cap s C : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (angleBudgetFactor a q cap s C) v :=
  ((clockExp_smooth_all a cap 1 v hv).mul
    ((angleLift_sinePower_smooth_all (-q) v hv).sub contDiffAt_const)).add contDiffAt_const

lemma angleBudgetFactor_nonneg (a q cap s C : ℝ) (hC : 0≤C)
    (v : State) (hc : physicalClock a cap v ≤ s) :
    0≤angleBudgetFactor a q cap s C v := by
  have hp := physicalTheta_mem v
  have hF : 0<angleLift (sinePower (-q)) v :=
    Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hp.1 hp.2) _
  have hE : 0<clockExp a cap 1 v := Real.exp_pos _
  have hEs : clockExp a cap 1 v≤Real.exp s := by
    exact Real.exp_le_exp.mpr (by simpa only [one_mul] using hc)
  have hh := mul_nonneg hC (sub_nonneg.mpr hEs)
  have hh' := mul_pos hE hF
  dsimp only [angleBudgetFactor]
  nlinarith only [hh,hh']

lemma angleBudgetFactor_terminal (a q cap s C : ℝ) (v : State)
    (hc : physicalClock a cap v=s) :
    angleBudgetFactor a q cap s C v = Real.exp s * angleLift (sinePower (-q)) v := by
  unfold angleBudgetFactor clockExp
  rw [hc,one_mul]
  ring

lemma green_angleBudget_generator (a q cap s C : ℝ) (ha : a≠0)
    (v : State) (hv : 0<Y v) :
    L (fun w => physicalGreen a w * angleBudgetFactor a q cap s C w)
      (physicalDrift a v) noise v =
      physicalGreen a v * clockExp a cap 1 v *
        (sinePower (-q) (physicalTheta v) +
          angleGenerator (2*a) (sinePower (-q)) (physicalTheta v) - C)*(physicalV v)^2 := by
  have hp := physicalTheta_mem v
  have hs := sinePower_smooth (-q) (physicalTheta v)
    (Real.sin_pos_of_pos_of_lt_pi hp.1 hp.2)
  have hG : ContDiffAt ℝ 2 (physicalGreen a) v :=
    (contDiffAt_physicalGreen a v hv).of_le (by norm_cast)
  have he : (fun w => physicalGreen a w * angleBudgetFactor a q cap s C w) =
      (fun w => physicalGreen a w * (clockExp a cap 1 w * angleLift (sinePower (-q)) w) +
        (-C)*(physicalGreen a w * (clockExp a cap 1 w * angleLift (fun _ => (1:ℝ)) w)) +
        (C*Real.exp s)*physicalGreen a w) := by
    funext w
    dsimp only [angleBudgetFactor,angleLift]
    ring
  have hz : L (physicalGreen a) (physicalDrift a v) noise v = 0 :=
    green_generator_zero a ha v hv
  rw [he,L_add ((hG.mul ((clockExp_smooth a cap 1 v hv).mul (angleLift_smooth _ v hv hs))).add
      (contDiffAt_const.mul (hG.mul ((clockExp_smooth a cap 1 v hv).mul
        (angleLift_smooth _ v hv contDiffAt_const))))) (contDiffAt_const.mul hG),
    L_add (hG.mul ((clockExp_smooth a cap 1 v hv).mul (angleLift_smooth _ v hv hs)))
      (contDiffAt_const.mul (hG.mul ((clockExp_smooth a cap 1 v hv).mul
        (angleLift_smooth _ v hv contDiffAt_const)))),
    L_const_mul (hG.mul ((clockExp_smooth a cap 1 v hv).mul
      (angleLift_smooth _ v hv contDiffAt_const))),L_const_mul hG,
    green_exponential_angle_generator _ a cap 1 ha v hv hs,
    green_exponential_angle_generator _ a cap 1 ha v hv contDiffAt_const,
    hz]
  have h1 : deriv (fun _ : ℝ => (1:ℝ)) = fun _ => 0 := funext fun _ => deriv_const _ _
  simp only [angleGenerator,h1,deriv_const]
  ring

lemma green_angleBudget_generator_nonpos (a q cap s C : ℝ) (ha : a≠0)
    (hC : ∀ θ∈Ioo 0 Real.pi,
      angleGenerator (2*a) (sinePower (-q)) θ+sinePower (-q) θ≤C)
    (v : State) (hv : 0<Y v) :
    L (fun w => physicalGreen a w * angleBudgetFactor a q cap s C w)
      (physicalDrift a v) noise v ≤0 := by
  rw [green_angleBudget_generator a q cap s C ha v hv]
  have hh := hC (physicalTheta v) (physicalTheta_mem v)
  apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (by linarith)

end ExactSLEGreen
end
end
 

 
section
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

theorem compact_test_stopped_dynkin
    (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration t] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (T : Driver → ℝ≥0) (B : ℝ≥0)
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hTB : ∀ b, T b ≤ B) :
    Integrable (fun b => f (X (T b) b)) W ∧
    Integrable (fun b => ∫ u in (0 : ℝ)..(T b : ℝ), generator f A e (X u.toNNReal b)) W ∧
    (∫ b, f (X (T b) b) ∂W) = (∫ b, f (X 0 b) ∂W) +
      ∫ b, (∫ u in (0 : ℝ)..(T b : ℝ), generator f A e (X u.toNNReal b)) ∂W := by
  let M : ℝ≥0 → Driver → ℝ := fun t b => f (X t b) -
    ∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)
  have hM : Martingale M rawFiltration W :=
    compact_smooth_brownian_martingale W hW X hXc hXm A hAc K hK hAb e he hXeq f hf hfc
  have hgc (b : Driver) : Continuous (fun u : ℝ => generator f A e (X u.toNNReal b)) :=
    (generator_continuous f hf A hAc e).comp ((hXc b).comp continuous_real_toNNReal)
  have hmc (b : Driver) : Continuous (fun t => M t b) :=
    (hf.continuous.comp (hXc b)).sub
      ((intervalIntegral.continuous_primitive (fun s t => (hgc b).intervalIntegrable s t) 0).comp NNReal.continuous_coe)
  obtain ⟨C,D,hC,hD,hfb,hgb⟩ := compact_generator_bounds f hf hfc A K hK hAb e
  have hmb (t : ℝ≥0) (ht : t ≤ B+1) (b : Driver) : ‖M t b‖ ≤ C+D*(B+1) := by
    calc
      _ ≤ ‖f (X t b)‖ + ‖∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)‖ := norm_sub_le _ _
      _ ≤ C+D*(t : ℝ) := add_le_add (hfb _) (by
        simpa only [sub_zero,abs_of_nonneg t.coe_nonneg] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ))
            (fun u _ => hgb (X u.toNNReal b)))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hD)
  have hFa : StronglyAdapted rawFiltration (fun t b => f (X t b)) := fun t =>
    (hf.continuous.measurable.comp (hXm t)).stronglyMeasurable
  have hFm : Measurable (fun b => f (X (T b) b)) :=
    (measurable_stoppedValue (hFa.isStronglyProgressive_of_continuous
      (fun b => hf.continuous.comp (hXc b))) hT).mono hT.measurableSpace_le le_rfl
  have hFi : Integrable (fun b => f (X (T b) b)) W :=
    Integrable.of_bound hFm.aestronglyMeasurable C (Eventually.of_forall fun b => hfb _)
  have hMi : Integrable (fun b => M (T b) b) W :=
    Integrable.of_bound (ExactSLEOptional.stopped_measurable rawFiltration hM hmc T hT).aestronglyMeasurable
      (C+D*(B+1)) (Eventually.of_forall fun b => hmb _ ((hTB b).trans (le_add_of_nonneg_right zero_le_one)) b)
  have hi : Integrable (fun b => ∫ u in (0 : ℝ)..(T b : ℝ), generator f A e (X u.toNNReal b)) W := by
    convert hFi.sub hMi using 1
    funext b
    dsimp [M]
    ring
  have heq := ExactSLEOptional.setIntegral_optional_sampling rawFiltration hM hmc B
    (C+D*(B+1)) hmb (fun _ => 0) T (isStoppingTime_const _ _) hT (fun _ => bot_le) hTB univ MeasurableSet.univ
  simp only [setIntegral_univ, M, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero] at heq
  rw [integral_sub hFi hi] at heq
  exact ⟨hFi, hi, by linarith⟩

end ExactSLEGenerator

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEGenerator

noncomputable def lifetimeCutoff (a ε : ℝ) (N : ℝ≥0) (v : State) : ℝ :=
  greenCutoff a ε N v * lifetimeTest (lifetimeExponent a) v

lemma lifetimeCutoff_smooth (a ε : ℝ) (hε : 0 < ε) (N : ℝ≥0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (lifetimeCutoff a ε N) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : 0 < Y v
  · exact (greenCutoff_smooth a ε hε N).contDiffAt.mul (lifetimeTest_smooth _ v hv)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hv' : Y v < ε/4 := lt_of_le_of_lt (le_of_not_gt hv) (by positivity)
    filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Iio_mem_nhds hv')] with w hw
    simp only [lifetimeCutoff, greenCutoff, heightTurn_zero hε (le_of_lt hw),
      mul_zero, zero_mul]

lemma lifetimeCutoff_compact (a ε : ℝ) (N : ℝ≥0) :
    HasCompactSupport (lifetimeCutoff a ε N) := (greenCutoff_compact a ε N).mul_right

lemma lifetimeCutoff_eq_near (a ε : ℝ) (hε : 0 < ε) (N : ℝ≥0)
    (v : State) (hv : ‖v‖ ≤ N) (hy : ε ≤ Y v) :
    lifetimeCutoff a ε N =ᶠ[𝓝 v]
      fun w => physicalGreen a w * lifetimeTest (lifetimeExponent a) w :=
  (greenCutoff_eq_near a ε hε N v hv hy).mul (EventuallyEq.refl _ _)

noncomputable def lifetimeCost (a : ℝ) (v : State) : ℝ :=
  lifetimeDrift a * physicalGreen a v * Q v ^ (lifetimeExponent a / 2 - 1)

lemma lifetimeCost_pos {a : ℝ} (ha : 1/4 < a) {v : State} (hv : 0 < Y v) :
    0 < lifetimeCost a v :=
  mul_pos (mul_pos (lifetimeDrift_pos ha) (Real.exp_pos _)) (Real.rpow_pos_of_pos (Q_pos hv) _)

lemma lifetimeCost_continuousAt (a : ℝ) (v : State) (hv : 0 < Y v) :
    ContinuousAt (lifetimeCost a) v := by
  have hQ : ContDiffAt ℝ 1 Q v :=
    ((X.contDiff.pow 2).add (Y.contDiff.pow 2)).contDiffAt
  exact (continuousAt_const.mul (contDiffAt_physicalGreen a v hv).continuousAt).mul
    ((hQ.rpow_const_of_ne (Q_pos hv).ne').continuousAt)

lemma lifetimeCutoff_generator_le (a ε : ℝ) (ha : 1/4 < a) (hε : 0 < ε) (N : ℝ≥0)
    (v : State) (hv : ‖v‖ ≤ N) (hy : ε ≤ Y v) :
    generator (lifetimeCutoff a ε N) (cutoffDrift a ε) noise v ≤ -lifetimeCost a v := by
  have he := lifetimeCutoff_eq_near a ε hε N v hv hy
  have hd : (fun w => fderiv ℝ (lifetimeCutoff a ε N) w noise) =ᶠ[𝓝 v]
      (fun w => fderiv ℝ (fun u => physicalGreen a u * lifetimeTest (lifetimeExponent a) u) w noise) :=
    he.fderiv.mono (fun w hw => congrArg (fun f : State →L[ℝ] ℝ => f noise) hw)
  change (1/2:ℝ) * fderiv ℝ (fun w => fderiv ℝ (lifetimeCutoff a ε N) w noise) v noise +
    fderiv ℝ (lifetimeCutoff a ε N) v (cutoffDrift a ε v) ≤ _
  rw [hd.fderiv_eq, he.fderiv_eq, cutoffDrift_eq_physical a ε v hy]
  convert green_lifetime_generator_le a ha v (hε.trans_le hy) using 1 <;> first | rfl | (dsimp [lifetimeCost]; ring)

 

theorem local_lifetime_budget (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (a ε : ℝ) (ha : 1/4 < a) (hε : 0 < ε) (z : ℂ) (N B : ℝ≥0)
    (T : Driver → ℝ≥0)
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hTB : ∀ b, T b ≤ B)
    (hsafe : ∀ b t, t ≤ T b → ε ≤ Y (localState a ε hε z t b) ∧
      ‖localState a ε hε z t b‖ ≤ N) :
    Integrable (fun b => physicalGreen a (localState a ε hε z (T b) b) *
      lifetimeTest (lifetimeExponent a) (localState a ε hε z (T b) b)) W ∧
    (∫ b, physicalGreen a (localState a ε hε z (T b) b) *
      lifetimeTest (lifetimeExponent a) (localState a ε hε z (T b) b) ∂W) ≤
      physicalGreen a (z,0) * lifetimeTest (lifetimeExponent a) (z,0) ∧
    (∫⁻ b, ∫⁻ u in Ioc (0 : ℝ) (T b : ℝ),
      ENNReal.ofReal (lifetimeCost a (localState a ε hε z u.toNNReal b)) ∂volume ∂W) ≤
      ENNReal.ofReal (physicalGreen a (z,0) * lifetimeTest (lifetimeExponent a) (z,0)) := by
  let V := localState a ε hε z
  let f := lifetimeCutoff a ε N
  let g := generator f (cutoffDrift a ε) noise
  have hf := lifetimeCutoff_smooth a ε hε N
  have hfc := lifetimeCutoff_compact a ε N
  have hgc : Continuous g := generator_continuous f hf _ (cutoffDrift_lipschitz a ε hε).continuous noise
  have hVc (b : Driver) : Continuous (fun u : ℝ => V u.toNNReal b) :=
    (localState_continuous a ε hε z b).comp continuous_real_toNNReal
  have he (b : Driver) (t : ℝ≥0) (ht : t ≤ T b) :
      f (V t b) = physicalGreen a (V t b) * lifetimeTest (lifetimeExponent a) (V t b) :=
    (lifetimeCutoff_eq_near a ε hε N _ (hsafe b t ht).2 (hsafe b t ht).1).eq_of_nhds
  have hfpos (b : Driver) (t : ℝ≥0) (ht : t ≤ T b) : 0 ≤ f (V t b) := by
    rw [he b t ht]
    exact mul_nonneg (Real.exp_pos _).le (lifetimeTest_nonneg _ _ (hε.le.trans (hsafe b t ht).1))
  have hgen (b : Driver) (t : ℝ≥0) (ht : t ≤ T b) :
      g (V t b) ≤ -lifetimeCost a (V t b) :=
    lifetimeCutoff_generator_le a ε ha hε N _ (hsafe b t ht).2 (hsafe b t ht).1
  have hpos (b : Driver) (t : ℝ≥0) (ht : t ≤ T b) : 0 < lifetimeCost a (V t b) :=
    lifetimeCost_pos ha (hε.trans_le (hsafe b t ht).1)
  have hDy := compact_test_stopped_dynkin W hW V
    (localState_continuous a ε hε z) (localState_adapted a ε hε z)
    (cutoffDrift a ε) (cutoffDrift_lipschitz a ε hε).continuous
    (max (|a|/ε) (|a|/ε^2)) (by positivity) (cutoffDrift_bound a ε hε) noise
    (by simp [noise, Prod.norm_def]) (localState_eq a ε hε z) f hf hfc T B hT hTB
  let H : Driver → ℝ := fun b => -(∫ u in (0 : ℝ)..(T b : ℝ), g (V u.toNNReal b))
  have hHi : Integrable H W := hDy.2.1.neg
  have hHnonneg (b : Driver) : 0 ≤ H b := by
    dsimp [H]
    apply neg_nonneg.mpr
    rw [intervalIntegral.integral_of_le (T b).coe_nonneg]
    apply setIntegral_nonpos measurableSet_Ioc
    intro u hu
    have ht : u.toNNReal ≤ T b := by simpa using Real.toNNReal_le_toNNReal hu.2
    exact (hgen b u.toNNReal ht).trans (neg_nonpos.mpr (hpos b u.toNNReal ht).le)
  have hHbound : (∫ b, H b ∂W) ≤ physicalGreen a (z,0) * lifetimeTest (lifetimeExponent a) (z,0) := by
    have hinit (b : Driver) : f (V 0 b) = physicalGreen a (z,0) * lifetimeTest (lifetimeExponent a) (z,0) := by
      rw [he b 0 (bot_le)]
      simp only [V,localState_zero]
    have hd := hDy.2.2
    simp_rw [hinit] at hd
    simp only [integral_const, probReal_univ, one_smul] at hd
    have hn : 0 ≤ ∫ b, f (V (T b) b) ∂W := integral_nonneg (fun b => hfpos b (T b) le_rfl)
    change (∫ b, -(∫ u in (0 : ℝ)..(T b : ℝ), g (V u.toNNReal b)) ∂W) ≤ _
    rw [integral_neg]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · simpa only [he _ _ le_rfl] using hDy.1
  · have hn : (∫ b, H b ∂W) ≥ 0 := integral_nonneg hHnonneg
    have hd := hDy.2.2
    have hinit (b : Driver) : f (V 0 b) = physicalGreen a (z,0) * lifetimeTest (lifetimeExponent a) (z,0) := by
      rw [he b 0 (bot_le)]
      simp only [V,localState_zero]
    simp_rw [hinit, he _ _ le_rfl] at hd
    simp only [integral_const, probReal_univ, one_smul] at hd
    dsimp only [H] at hn
    rw [integral_neg] at hn
    change (∫ b, physicalGreen a (V (T b) b) * lifetimeTest (lifetimeExponent a) (V (T b) b) ∂W) ≤ _
    linarith
  · suffices hp : ∀ b, (∫⁻ u in Ioc (0 : ℝ) (T b : ℝ), ENNReal.ofReal (lifetimeCost a (V u.toNNReal b))) ≤ ENNReal.ofReal (H b) by
      calc
        _ ≤ ∫⁻ b, ENNReal.ofReal (H b) ∂W := lintegral_mono hp
        _ = ENNReal.ofReal (∫ b, H b ∂W) := (ofReal_integral_eq_lintegral_ofReal hHi (Eventually.of_forall hHnonneg)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hHbound
    intro b
    have ht (u : ℝ) (hu : u ∈ Icc 0 (T b : ℝ)) : u.toNNReal ≤ T b := by
      simpa using Real.toNNReal_le_toNNReal hu.2
    have hcostc : ContinuousOn (fun u : ℝ => lifetimeCost a (V u.toNNReal b)) (Icc 0 (T b : ℝ)) := by
      intro u hu
      exact ((lifetimeCost_continuousAt a _ (hε.trans_le (hsafe b u.toNNReal (ht u hu)).1)).comp (f := fun u : ℝ => V u.toNNReal b) (hVc b).continuousAt).continuousWithinAt
    have hci : IntervalIntegrable (fun u : ℝ => lifetimeCost a (V u.toNNReal b)) volume 0 (T b) :=
      hcostc.intervalIntegrable_of_Icc (T b).coe_nonneg
    have hgi : IntervalIntegrable (fun u : ℝ => g (V u.toNNReal b)) volume 0 (T b) := (hgc.comp (hVc b)).intervalIntegrable 0 (T b)
    have hcb : (∫ u in (0 : ℝ)..(T b : ℝ), lifetimeCost a (V u.toNNReal b)) ≤ H b := by
      dsimp only [H]
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_mono_on (T b).coe_nonneg hci hgi.neg
      intro u hu
      dsimp only [Pi.neg_apply]
      linarith only [hgen b u.toNNReal (ht u hu)]
    rw [intervalIntegral.integral_of_le (T b).coe_nonneg] at hcb
    have hn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) (T b : ℝ))] (fun u => lifetimeCost a (V u.toNNReal b)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact (hpos b u.toNNReal (ht u ⟨hu.1.le,hu.2⟩)).le
    rw [← ofReal_integral_eq_lintegral_ofReal hci.1 hn]
    exact ENNReal.ofReal_le_ofReal hcb

end ExactSLEGreen
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator

def angleBudgetCutoff (a q cap s C ε : ℝ) (N : ℝ≥0) (v : State) : ℝ :=
  greenCutoff a ε N v * angleBudgetFactor a q cap s C v

lemma angleBudgetCutoff_smooth (a q cap s C ε : ℝ) (hε : 0<ε) (N : ℝ≥0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (angleBudgetCutoff a q cap s C ε N) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : 0<Y v
  · exact (greenCutoff_smooth a ε hε N).contDiffAt.mul
      (angleBudgetFactor_smooth a q cap s C v hv)
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    have hv' : Y v < ε/4 := lt_of_le_of_lt (le_of_not_gt hv) (by positivity)
    filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Iio_mem_nhds hv')] with w hw
    simp only [angleBudgetCutoff, greenCutoff, heightTurn_zero hε (le_of_lt hw),
      mul_zero, zero_mul]

lemma angleBudgetCutoff_compact (a q cap s C ε : ℝ) (N : ℝ≥0) :
    HasCompactSupport (angleBudgetCutoff a q cap s C ε N) :=
  (greenCutoff_compact a ε N).mul_right

lemma angleBudgetCutoff_eq_near (a q cap s C ε : ℝ) (hε : 0<ε) (N : ℝ≥0)
    (v : State) (hv : ‖v‖≤N) (hy : ε≤Y v) :
    angleBudgetCutoff a q cap s C ε N =ᶠ[𝓝 v]
      fun w => physicalGreen a w * angleBudgetFactor a q cap s C w :=
  (greenCutoff_eq_near a ε hε N v hv hy).mul (EventuallyEq.refl _ _)

lemma angleBudgetCutoff_generator_nonpos (a q cap s C ε : ℝ) (ha : a≠0)
    (hC : ∀ θ∈Ioo 0 Real.pi,
      angleGenerator (2*a) (sinePower (-q)) θ + sinePower (-q) θ ≤ C)
    (hε : 0<ε) (N : ℝ≥0) (v : State) (hv : ‖v‖≤N) (hy : ε≤Y v) :
    generator (angleBudgetCutoff a q cap s C ε N) (cutoffDrift a ε) noise v ≤ 0 := by
  have he := angleBudgetCutoff_eq_near a q cap s C ε hε N v hv hy
  have hd : (fun w => fderiv ℝ (angleBudgetCutoff a q cap s C ε N) w noise) =ᶠ[𝓝 v]
      (fun w => fderiv ℝ (fun u => physicalGreen a u * angleBudgetFactor a q cap s C u) w noise) :=
    he.fderiv.mono (fun w hw => congrArg (fun f : State →L[ℝ] ℝ => f noise) hw)
  change (1/2:ℝ) * fderiv ℝ (fun w => fderiv ℝ (angleBudgetCutoff a q cap s C ε N) w noise) v noise +
    fderiv ℝ (angleBudgetCutoff a q cap s C ε N) v (cutoffDrift a ε v) ≤ 0
  rw [hd.fderiv_eq, he.fderiv_eq, cutoffDrift_eq_physical a ε v hy]
  exact green_angleBudget_generator_nonpos a q cap s C ha hC v (hε.trans_le hy)

 

theorem local_angle_budget (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (a q cap s C ε : ℝ) (ha : a≠0)
    (hC : ∀ θ∈Ioo 0 Real.pi,
      angleGenerator (2*a) (sinePower (-q)) θ + sinePower (-q) θ ≤ C)
    (hε : 0<ε) (z : ℂ) (N B : ℝ≥0) (T : Driver → ℝ≥0)
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hTB : ∀ b, T b≤B)
    (hsafe : ∀ b t, t≤T b → ε≤Y (localState a ε hε z t b) ∧
      ‖localState a ε hε z t b‖≤N) :
    Integrable (fun b => physicalGreen a (localState a ε hε z (T b) b) *
      angleBudgetFactor a q cap s C (localState a ε hε z (T b) b)) W ∧
    (∫ b, physicalGreen a (localState a ε hε z (T b) b) *
      angleBudgetFactor a q cap s C (localState a ε hε z (T b) b) ∂W) ≤
      physicalGreen a (z,0) * angleBudgetFactor a q cap s C (z,0) := by
  let V := localState a ε hε z
  let f := angleBudgetCutoff a q cap s C ε N
  let g := generator f (cutoffDrift a ε) noise
  have hf := angleBudgetCutoff_smooth a q cap s C ε hε N
  have hfc := angleBudgetCutoff_compact a q cap s C ε N
  have he (b : Driver) (t : ℝ≥0) (ht : t≤T b) :
      f (V t b) = physicalGreen a (V t b) * angleBudgetFactor a q cap s C (V t b) :=
    (angleBudgetCutoff_eq_near a q cap s C ε hε N _ (hsafe b t ht).2
      (hsafe b t ht).1).eq_of_nhds
  have hgen (b : Driver) (t : ℝ≥0) (ht : t≤T b) : g (V t b)≤0 :=
    angleBudgetCutoff_generator_nonpos a q cap s C ε ha hC hε N _
      (hsafe b t ht).2 (hsafe b t ht).1
  have hDy := compact_test_stopped_dynkin W hW V
    (localState_continuous a ε hε z) (localState_adapted a ε hε z)
    (cutoffDrift a ε) (cutoffDrift_lipschitz a ε hε).continuous
    (max (|a|/ε) (|a|/ε^2)) (by positivity) (cutoffDrift_bound a ε hε) noise
    (by simp [noise, Prod.norm_def]) (localState_eq a ε hε z) f hf hfc T B hT hTB
  have hneg : (∫ b, (∫ u in (0:ℝ)..(T b : ℝ), g (V u.toNNReal b)) ∂W) ≤ 0 := by
    apply integral_nonpos
    intro b
    change (∫ u in (0:ℝ)..(T b : ℝ), g (V u.toNNReal b)) ≤ 0
    rw [intervalIntegral.integral_of_le (T b).coe_nonneg]
    apply setIntegral_nonpos measurableSet_Ioc
    intro u hu
    exact hgen b u.toNNReal (by simpa using Real.toNNReal_le_toNNReal hu.2)
  have hinit (b : Driver) : f (V 0 b) = physicalGreen a (z,0) * angleBudgetFactor a q cap s C (z,0) := by
    rw [he b 0 bot_le]
    simp only [V,localState_zero]
  refine ⟨by simpa only [he _ _ le_rfl] using hDy.1, ?_⟩
  have hd := hDy.2.2
  simp_rw [hinit,he _ _ le_rfl] at hd
  simp only [integral_const,probReal_univ,one_smul] at hd
  change (∫ b, physicalGreen a (V (T b) b)*angleBudgetFactor a q cap s C (V (T b) b) ∂W)≤_
  linarith

end ExactSLEGreen
end
end

end OAI
