import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.AngleLyapunov

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt

def radialTestWeight (a : ℝ) (F : State→ℝ) (b : ℝ≥0→ℝ) (z : ℂ) (ρ : ℝ) : ℝ :=
  if radialTime a b z ρ=∞ then 0 else
    let v := actualState a b (radialTime a b z ρ).toNNReal z
    physicalGreen a v * F v

lemma radialTestWeight_nonneg (a : ℝ) (F : State→ℝ) (hF : ∀v, 0≤F v)
    (b : ℝ≥0→ℝ) (z : ℂ) (ρ : ℝ) : 0≤radialTestWeight a F b z ρ := by
  unfold radialTestWeight
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Real.exp_pos _).le (hF _)

lemma sinePower_angleLift_pos (q : ℝ) (v : State) : 0<angleLift (sinePower q) v :=
  Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (physicalTheta_mem v).1 (physicalTheta_mem v).2) _

lemma physicalClock_initial (a : ℝ) (z : ℂ) : physicalClock a (2*z.im) (z,0)=0 := by
  simp only [physicalClock,J_apply,Y_apply]
  rw [show 2*z.im/2=z.im by ring]
  simp

lemma angleBudgetFactor_initial_bound (a q s C : ℝ) (hs : 0≤ s) (hC : 0≤C)
    (z : ℂ) :
    Real.exp (-s) * angleBudgetFactor a q (2*z.im) s C (z,0) ≤
      angleLift (sinePower (-q)) (z,0)+C := by
  have hE := (Real.exp_pos (-s)).le
  have hE1 : Real.exp (-s)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hF := (sinePower_angleLift_pos (-q) (z,0)).le
  have he : Real.exp (-s)*Real.exp s=1 := by rw [←Real.exp_add]; simp
  have hprod := mul_le_mul_of_nonneg_right hE1 hF
  have hCprod := mul_nonneg hE hC
  unfold angleBudgetFactor clockExp
  rw [physicalClock_initial a z, mul_zero,Real.exp_zero,one_mul]
  nlinarith only [he,hprod,hCprod,hC]

 

theorem finite_level_angle_budget (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a q C : ℝ) (ha : 0<a) (hC0 : 0≤C)
    (hC : ∀ θ∈Ioo 0 Real.pi,
      angleGenerator (2*a) (sinePower (-q)) θ+sinePower (-q) θ≤C)
    (z : ℂ) (hz : 0<z.im) (s : ℝ) (hs : 0≤ s) :
    (∫⁻ b, ENNReal.ofReal (radialTestWeight a (angleLift (sinePower (-q))) b.1 z
      (levelRadius a (2*z.im) s)) ∂W) ≤
      ENNReal.ofReal (physicalGreen a (z,0)*(angleLift (sinePower (-q)) (z,0)+C)) := by
  let cap := 2*z.im
  have hcap : 0<cap := by dsimp [cap]; positivity
  let ρ := levelRadius a cap s
  have hρ : 0<ρ := levelRadius_pos a cap s hcap
  have hr : ρ≤z.im := by
    simpa only [cap,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using
      (levelRadius_le ha hcap hs)
  let L (n : ℕ) := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T (n : ℕ) := radialStop a ha z hz ρ hρ hr n
  let V (n : ℕ) (b : ExactSLEGenerator.Driver) := localState a (L n).ε (L n).hε z (T n b) b
  let f (n : ℕ) (b : ExactSLEGenerator.Driver) := Real.exp (-s) *
    (physicalGreen a (V n b)*angleBudgetFactor a q cap s C (V n b))
  let A := physicalGreen a (z,0)*(angleLift (sinePower (-q)) (z,0)+C)
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
  have hc (n : ℕ) (b : ExactSLEGenerator.Driver) : physicalClock a cap (V n b) ≤ s := by
    rw [←(hact n b).2]
    have h := actual_physicalClock_le a ha z hz cap ρ hcap hρ hr b (T n b)
      (hact n b).1 (radialStop_le_radialTime a ha z hz ρ hρ hr n b)
    simpa only [ρ,levelRadius_clock ha.ne' hcap] using h
  have hp (n : ℕ) (b : ExactSLEGenerator.Driver) : 0≤f n b :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le
      (angleBudgetFactor_nonneg a q cap s C hC0 _ (hc n b)))
  have hb (n : ℕ) : Integrable (f n) W ∧ (∫ b, f n b ∂W)≤A := by
    have hh := local_angle_budget W hW a q cap s C (L n).ε ha.ne' hC (L n).hε
      z (L n).N (L n).B (T n) (radialStop_stopping a ha z hz ρ hρ hr n)
      (regionStop_le a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B)
      (hsafe n)
    refine ⟨hh.1.const_mul _, ?_⟩
    change (∫ b, Real.exp (-s)*(physicalGreen a (V n b)*angleBudgetFactor a q cap s C (V n b)) ∂W)≤A
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (-s)*(physicalGreen a (z,0)*angleBudgetFactor a q cap s C (z,0)) :=
        mul_le_mul_of_nonneg_left hh.2 (Real.exp_pos _).le
      _ = physicalGreen a (z,0)*(Real.exp (-s)*angleBudgetFactor a q cap s C (z,0)) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left
        (angleBudgetFactor_initial_bound a q s C hs hC0 z) (Real.exp_pos _).le
  have hbf (n : ℕ) : (∫⁻ b, ENNReal.ofReal (f n b) ∂W)≤ENNReal.ofReal A := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hb n).1 (Eventually.of_forall (hp n))]
    exact ENNReal.ofReal_le_ofReal (hb n).2
  have hlim (b : ExactSLEGenerator.Driver) :
      ENNReal.ofReal (radialTestWeight a (angleLift (sinePower (-q))) b.1 z ρ) ≤
        liminf (fun n => ENNReal.ofReal (f n b)) atTop := by
    by_cases ht : radialTime a b.1 z ρ=∞
    · simp only [radialTestWeight,ite_eq_left ht,ENNReal.ofReal_zero]
      exact bot_le
    · apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [radialStop_eventually_eq a ha z hz ρ hρ hr b ht] with n hn
      have he : T n b=(radialTime a b.1 z ρ).toNNReal := by
        have hh := congrArg ENNReal.toNNReal hn
        simpa only [ENNReal.toNNReal_coe] using hh
      have hv : V n b=actualState a b.1 (radialTime a b.1 z ρ).toNNReal z := by
        rw [←(hact n b).2,he]
      have htC : physicalClock a cap (V n b)=s := by
        rw [hv, actual_physicalClock_at a ha z hz cap ρ hcap hρ hr b ht]
        exact levelRadius_clock ha.ne' hcap
      have hexp : Real.exp (-s)*Real.exp s=1 := by rw [←Real.exp_add]; simp
      apply le_of_eq
      congr 1
      simp only [radialTestWeight,ite_eq_right ht,f,angleBudgetFactor_terminal a q cap s C _ htC]
      rw [hv]
      nlinarith only [congrArg (fun x => x*(physicalGreen a
        (actualState a b.1 (radialTime a b.1 z ρ).toNNReal z)*
          angleLift (sinePower (-q)) (actualState a b.1 (radialTime a b.1 z ρ).toNNReal z))) hexp]
  exact (lintegral_mono hlim).trans ((lintegral_liminf_le' (fun n =>
    (hb n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)).trans
      (liminf_le_of_frequently_le (Eventually.of_forall hbf).frequently))

 

theorem exists_finite_level_angle_bound (a q : ℝ) (ha : 1/4<a) (hq : 0<q)
    (hqp : q<4*a-1) : ∃ C : ℝ, 0<C ∧
    ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
      ∀ (z : ℂ), 0<z.im → ∀ s : ℝ, 0≤ s →
        (∫⁻ b, ENNReal.ofReal (radialTestWeight a (angleLift (sinePower (-q))) b.1 z
          (levelRadius a (2*z.im) s)) ∂W) ≤
          ENNReal.ofReal (physicalGreen a (z,0)*(angleLift (sinePower (-q)) (z,0)+C)) := by
  obtain ⟨C,hC0,hC⟩ := exists_tilted_coercivity ha hq hqp
  refine ⟨C,hC0,?_⟩
  intro W hprob hW z hz s hs
  exact finite_level_angle_budget W hW a q C (by linarith) hC0.le hC z hz s hs

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt

lemma localizationStop_eventually_eq (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) (b : ExactSLEGenerator.Driver)
    (L : ∀n, RadialLocalization a z ρ (angleThreshold z n))
    (hfin : radialTime a b.1 z ρ≠∞) :
    ∀ᶠ n in atTop,
      (regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b : ℝ≥0∞)=
        radialTime a b.1 z ρ := by
  let t := (radialTime a b.1 z ρ).toNNReal
  have ht := radialTime_attained a ha z hz ρ hρ hr b hfin
  obtain ⟨η,hη,hηs⟩ := actual_sine_lower a b.1 b.1.continuous z t ht.1
  filter_upwards [(angleThreshold_tendsto z).eventually (gt_mem_nhds hη)] with n hn
  let T := regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b
  let V := localState a (L n).ε (L n).hε z T b
  have hTt : T≤t := regionStop_le_hit a (L n).ε (L n).hε z (L n).N ρ
    (angleThreshold z n) (L n).B (L n).initial b t ht.2
  have he := regionStop_actualState a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
    (L n).B (L n).initial b T le_rfl
  rcases regionStop_true_exit a (L n).ε ha (L n).hε z (L n).N ρ (angleThreshold z n) hρ
    (angleThreshold_pos z hz n) (L n).B (L n).initial (L n).small (L n).large (L n).time b with hR|hS
  · exact (regionStop_eq_radialTime a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
      (L n).B (L n).initial b hR).symm
  · have hs := regionStop_safe a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
      (L n).B (L n).initial b T le_rfl
    have hnp : 0<‖V.1‖ := ((L n).hε.trans_le hs.1).trans_le (Complex.im_le_norm _)
    have hd : Y V/‖V.1‖=angleThreshold z n := (div_eq_iff hnp.ne').mpr hS
    have hη' := hηs T hTt
    rw [he.2,hd] at hη'
    exact False.elim (not_le.mpr hn hη')

 
def radialState (a : ℝ) (b : ℝ≥0→ℝ) (z : ℂ) (ρ : ℝ) : State :=
  if radialTime a b z ρ=∞ then 0 else
    actualState a b (radialTime a b z ρ).toNNReal z

lemma localizedState_eventually_eq (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) (b : ExactSLEGenerator.Driver)
    (L : ∀n, RadialLocalization a z ρ (angleThreshold z n)) :
    ∀ᶠ n in atTop,
      (let V := localState a (L n).ε (L n).hε z
        (regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b) b
       if physicalRadius V=ρ then V else 0)=radialState a b.1 z ρ := by
  let T (n : ℕ) := regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b
  let V (n : ℕ) := localState a (L n).ε (L n).hε z (T n) b
  have he (n : ℕ) : actualState a b.1 (T n) z=V n :=
    (regionStop_actualState a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
      (L n).B (L n).initial b _ le_rfl).2
  by_cases hf : radialTime a b.1 z ρ=∞
  · apply Eventually.of_forall
    intro n
    have hn : physicalRadius (V n)≠ρ := by
      intro hn
      have hh := regionStop_eq_radialTime a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
        (L n).B (L n).initial b hn
      exact ENNReal.coe_ne_top ((hf.symm.trans hh).symm)
    exact (ite_eq_right hn).trans (by simp [radialState,hf])
  · filter_upwards [localizationStop_eventually_eq a ha z hz ρ hρ hr b L hf] with n hn
    have ht : T n=(radialTime a b.1 z ρ).toNNReal := by
      have hh := congrArg ENNReal.toNNReal hn
      simpa only [ENNReal.toNNReal_coe] using hh
    have hv : V n=actualState a b.1 (radialTime a b.1 z ρ).toNNReal z := by rw [←he n,ht]
    have hh : physicalRadius (V n)=ρ := by
      rw [hv]; exact (radialTime_attained a ha z hz ρ hρ hr b hf).2
    exact (ite_eq_left hh).trans (by simpa only [radialState,ite_eq_right hf] using hv)

 

theorem joint_radialState_measurable (a : ℝ) (ha : 0<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) :
    Measurable (fun p : ExactSLEGenerator.Driver×UpperPlane =>
      radialState a p.1.1 p.2.1 (p.2.1.im*q)) := by
  let Ω := ExactSLEGenerator.Driver×UpperPlane
  let z : Ω→ℂ := fun p => p.2.1
  let b : Ω→ExactSLEGenerator.Driver := Prod.fst
  have hz (ω : Ω) : 0<(z ω).im := ω.2.2
  have hzM : Measurable z := measurable_subtype_coe.comp measurable_snd
  have hbM : Measurable b := measurable_fst
  let ρ : Ω→ℝ := fun ω => (z ω).im*q
  have hρ (ω : Ω) : 0<ρ ω := mul_pos (hz ω) hq
  have hr (ω : Ω) : ρ ω≤(z ω).im := mul_le_of_le_one_right (hz ω).le hq1
  let δ : ℕ→Ω→ℝ := fun n ω => angleThreshold (z ω) n
  let L (n : ℕ) (ω : Ω) := explicitRadialLocalization a ha (z ω) (hz ω) (ρ ω) (δ n ω)
    (hρ ω) (hr ω) (angleThreshold_pos (z ω) (hz ω) n) (angleThreshold_initial (z ω) (hz ω) n)
  have hρM : Measurable ρ := hzM.im.mul_const q
  have hδM (n : ℕ) : Measurable (δ n) := by
    dsimp [δ,angleThreshold]
    exact (hzM.im.div hzM.norm).div_const _
  have hεM (n : ℕ) : Measurable (fun ω => (L n ω).ε) := by
    change Measurable (fun ω => heightFloor (z ω).im (ρ ω) (δ n ω)/2)
    unfold heightFloor
    fun_prop
  have hNM (n : ℕ) : Measurable (fun ω => (L n ω).N) := by
    change Measurable (fun ω => (⟨(z ω).im/δ n ω+logCeiling (z ω).im (ρ ω) (δ n ω)+1,_⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    unfold logCeiling heightFloor
    fun_prop
  have hBM (n : ℕ) : Measurable (fun ω => (L n ω).B) := by
    change Measurable (fun ω => (⟨(z ω).im^2/(2*a*(δ n ω)^2)+1,_⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    fun_prop
  let T (n : ℕ) (ω : Ω) := regionStop a (L n ω).ε (L n ω).hε (z ω)
    (L n ω).N (ρ ω) (δ n ω) (L n ω).B (b ω)
  have hTM (n : ℕ) : Measurable (T n) :=
    regionStop_parameter_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε) z b _ ρ (δ n) _
      (hεM n) hzM hbM (measurable_subtype_coe.comp (hNM n)) hρM (hδM n) (hBM n)
  let V (n : ℕ) (ω : Ω) := localState a (L n ω).ε (L n ω).hε (z ω) (T n ω) (b ω)
  have hVM (n : ℕ) : Measurable (V n) :=
    (localState_parameter_joint_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε)
      z b (hεM n) hzM hbM).comp ((hTM n).prodMk measurable_id)
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => if physicalRadius (V n ω)=ρ ω then V n ω else (0:State))
  · intro n
    exact Measurable.ite (measurableSet_eq_fun
      (physicalRadius_continuous.measurable.comp (hVM n)) hρM) (hVM n) measurable_const
  · apply tendsto_pi_nhds.mpr
    intro ω
    apply tendsto_const_nhds.congr'
    exact (localizedState_eventually_eq a ha (z ω) (hz ω) (ρ ω) (hρ ω) (hr ω) (b ω)
      (fun n => L n ω)).mono (fun n hn => hn.symm)

lemma radialTestWeight_eq_mul (a : ℝ) (F : State→ℝ) (b : ℝ≥0→ℝ) (z : ℂ) (ρ : ℝ) :
    radialTestWeight a F b z ρ=radialWeight a b z ρ*F (radialState a b z ρ) := by
  unfold radialTestWeight radialWeight radialState
  split_ifs <;> simp

lemma joint_radialTestWeight_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (F : State→ℝ) (hF : Measurable F) :
    Measurable (fun p : ExactSLEGenerator.Driver×UpperPlane =>
      radialTestWeight a F p.1.1 p.2.1 (p.2.1.im*q)) := by
  simp_rw [radialTestWeight_eq_mul]
  exact (joint_radialWeight_measurable a ha q hq hq1).mul
    (hF.comp (joint_radialState_measurable a (by linarith) q hq hq1))

lemma angleLift_sinePower_measurable (q : ℝ) : Measurable (angleLift (sinePower q)) := by
  unfold angleLift sinePower physicalTheta
  fun_prop

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerScaling
open ExactSLEMain ExactSLEGreen

def scaleState (c : ℝ≥0) (v : State) : State := (((c:ℝ):ℂ)⁻¹*v.1,v.2)

lemma scaleState_Y (c : ℝ≥0) (v : State) :
    Y (scaleState c v)=(c:ℝ)⁻¹*Y v := by
  simp [scaleState,←Complex.ofReal_inv,Complex.mul_im]

lemma scaleState_X (c : ℝ≥0) (v : State) :
    X (scaleState c v)=(c:ℝ)⁻¹*X v := by
  simp [scaleState,←Complex.ofReal_inv,Complex.mul_re]

lemma scaleState_Q (c : ℝ≥0) (v : State) :
    Q (scaleState c v)=((c:ℝ)⁻¹)^2*Q v := by
  simp only [Q,scaleState_X,scaleState_Y]
  ring

lemma scaleState_J (c : ℝ≥0) (v : State) : J (scaleState c v)=J v := rfl

lemma scaleState_radius (c : ℝ≥0) (v : State) :
    physicalRadius (scaleState c v)=(c:ℝ)⁻¹*physicalRadius v := by
  simp only [physicalRadius,scaleState_Y,scaleState_J]
  ring

lemma scaleState_logGreen (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    (v : State) (hv : 0<Y v) :
    logGreen a (scaleState c v)=alpha a*Real.log c+logGreen a v := by
  have hcR : 0<(c:ℝ) := hc
  have hn : (c:ℝ)≠0 := hcR.ne'
  have hq := (Q_pos hv).ne'
  simp only [logGreen,scaleState_Y,scaleState_Q,scaleState_J,
    Real.log_mul (inv_ne_zero hn) hv.ne',
    Real.log_mul (pow_ne_zero 2 (inv_ne_zero hn)) hq,
    Real.log_pow,Real.log_inv]
  ring

lemma scaleState_green (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    (v : State) (hv : 0<Y v) :
    physicalGreen a (scaleState c v)=(c:ℝ)^(alpha a)*physicalGreen a v := by
  rw [physicalGreen,scaleState_logGreen a hc v hv,Real.exp_add,
    Real.rpow_def_of_pos (show 0<(c:ℝ) from hc)]
  rw [mul_comm (Real.log c)]
  rfl

lemma physicalRadius_scaled (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (t : ℝ≥0) (z : ℂ)
    (hz : alive a (scaled c b) t z) :
    physicalRadius (actualState a (scaled c b) t z) =
      (c:ℝ)⁻¹*physicalRadius (actualState a b (c^2*t) (((c:ℝ):ℂ)*z)) := by
  rw [actualState_scaled a hc hb t z hz]
  exact scaleState_radius c _

lemma image_radialHits (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (z : ℂ) (ρ : ℝ) :
    (fun u : ℝ≥0∞ => (c:ℝ≥0∞)^2*u) ''
      {u : ℝ≥0∞ | ∃ t : ℝ≥0, u=t ∧ alive a (scaled c b) t z ∧
        physicalRadius (actualState a (scaled c b) t z)=ρ} =
      {u : ℝ≥0∞ | ∃ t : ℝ≥0, u=t ∧ alive a b t (((c:ℝ):ℂ)*z) ∧
        physicalRadius (actualState a b t (((c:ℝ):ℂ)*z))=(c:ℝ)*ρ} := by
  have hn : (c:ℝ)≠0 := NNReal.coe_ne_zero.mpr hc.ne'
  ext u
  constructor
  · rintro ⟨w,⟨t,rfl,ht,hr⟩,rfl⟩
    refine ⟨c^2*t,by simp, (alive_scaled_iff a hc b t z).mp ht,?_⟩
    rw [physicalRadius_scaled a hc hb t z ht] at hr
    calc
      _ = (c:ℝ)*((c:ℝ)⁻¹*physicalRadius (actualState a b (c^2*t) (((c:ℝ):ℂ)*z))) := by simp [hn]
      _ = _ := by rw [hr]
  · rintro ⟨t,rfl,ht,hr⟩
    let v : ℝ≥0 := (c^2)⁻¹*t
    have hvt : c^2*v=t := by simp [v,hc.ne']
    have hv : alive a (scaled c b) v z := by
      rw [alive_scaled_iff a hc b v z,hvt]
      exact ht
    refine ⟨v,⟨v,rfl,hv,?_⟩,?_⟩
    · rw [physicalRadius_scaled a hc hb v z hv,hvt,hr]
      simp [hn]
    · simp only [←ENNReal.coe_pow,←ENNReal.coe_mul,hvt]

 
lemma radialTime_scaled (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (z : ℂ) (ρ : ℝ) :
    (c:ℝ≥0∞)^2*radialTime a (scaled c b) z ρ =
      radialTime a b (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ) := by
  let e := ENNReal.mulLeftOrderIso ((c:ℝ≥0∞)^2)
    (ENNReal.isUnit_iff.mpr ⟨pow_ne_zero _ (by exact_mod_cast hc.ne'),
      ENNReal.pow_ne_top ENNReal.coe_ne_top⟩)
  change e (sInf _) = sInf _
  rw [e.map_sInf,←sInf_image]
  congr 1
  exact image_radialHits a hc hb z ρ

lemma radialTime_scaled_eq_top_iff (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (z : ℂ) (ρ : ℝ) :
    radialTime a (scaled c b) z ρ = ∞ ↔
      radialTime a b (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ) = ∞ := by
  rw [←radialTime_scaled a hc hb z ρ]
  simp [ENNReal.mul_eq_top,
    pow_ne_zero 2 (show (c:ℝ≥0∞)≠0 by exact_mod_cast hc.ne')]

end SLEExactGauge.LoewnerScaling
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerScaling
open ExactSLEMain ExactSLEGreen

lemma Y_actual_pos {a : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {t : ℝ≥0}
    (ht : alive a b t z) : 0 < Y (actualState a b t z) := by
  obtain ⟨f,hf⟩ := ht
  simpa only [Y_apply,actualState,Complex.sub_im,Complex.ofReal_im,sub_zero,
    loewnerMap_eq hf] using (hf.2 t ⟨t.coe_nonneg,le_rfl⟩).1

lemma radialTime_scaled_toNNReal (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (z : ℂ) (ρ : ℝ) :
    (radialTime a b (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ)).toNNReal =
      c^2*(radialTime a (scaled c b) z ρ).toNNReal := by
  rw [←radialTime_scaled a hc hb z ρ,ENNReal.toNNReal_mul]
  simp

lemma radialTime_scaled_le_iff (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (z : ℂ) (ρ : ℝ) (t : ℝ≥0∞) :
    radialTime a (scaled c b) z ρ ≤ t ↔
      radialTime a b (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ) ≤ (c:ℝ≥0∞)^2*t := by
  rw [←radialTime_scaled a hc hb z ρ]
  exact (ENNReal.mul_le_mul_iff_right
    (pow_ne_zero _ (by exact_mod_cast hc.ne')) (ENNReal.pow_ne_top ENNReal.coe_ne_top)).symm

lemma radialWeight_scaled (a : ℝ) (ha : 0<a) {c : ℝ≥0} (hc : 0<c)
    (b : ExactSLEGenerator.Driver) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hρz : ρ≤z.im) :
    radialWeight a (scaleDriver c b).1 z ρ =
      (c:ℝ)^(alpha a)*radialWeight a b.1 (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ) := by
  change radialWeight a (scaled c b.1) z ρ = _
  have ht := radialTime_scaled_eq_top_iff a hc b.1.continuous z ρ
  by_cases hs : radialTime a (scaled c b.1) z ρ=∞
  · simp only [radialWeight,ht.mp hs,ite_true,mul_zero]
    exact ite_eq_left hs
  · have hl := (radialTime_attained a ha z hz ρ hρ hρz (scaleDriver c b) hs).1
    change alive a (scaled c b.1) (radialTime a (scaled c b.1) z ρ).toNNReal z at hl
    have hl' := (alive_scaled_iff a hc b.1 _ z).mp hl
    rw [radialWeight,ite_eq_right hs,radialWeight,ite_eq_right (ht.not.mp hs),
      radialTime_scaled_toNNReal a hc b.1.continuous z ρ,
      actualState_scaled a hc b.1.continuous _ z hl]
    exact scaleState_green a hc _ (Y_actual_pos hl')

lemma massDensity_scaled_upper (a : ℝ) (ha : 0<a) {c : ℝ≥0} (hc : 0<c)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (b : ExactSLEGenerator.Driver)
    (z : ℂ) (hz : 0<z.im) :
    massDensity a q (scaleDriver c b) z = ENNReal.ofReal ((c:ℝ)^(alpha a))*
      massDensity a q b (((c:ℝ):ℂ)*z) := by
  have hz' : 0<(((c:ℝ):ℂ)*z).im := by
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      using mul_pos (show 0<(c:ℝ) from hc) hz
  simp only [massDensity,ite_eq_left hz,ite_eq_left hz',fullRadialDensity]
  have he : 2*z.im*q/2=z.im*q := by ring
  have he' : 2*(((c:ℝ):ℂ)*z).im*q/2=(c:ℝ)*(z.im*q) := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring
  have hcp : 0≤(c:ℝ)^(alpha a) := (Real.rpow_pos_of_pos (show 0<(c:ℝ) from hc) _).le
  rw [he,he',radialWeight_scaled a ha hc b z hz (z.im*q) (mul_pos hz hq)
    (mul_le_of_le_one_right hz.le hq1),←ENNReal.ofReal_mul hcp]
  congr 1
  ring

lemma timeMassDensity_scaled_upper (a : ℝ) (ha : 0<a) {c : ℝ≥0} (hc : 0<c)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver)
    (z : ℂ) (hz : 0<z.im) :
    timeMassDensity a q t (scaleDriver c b) z = ENNReal.ofReal ((c:ℝ)^(alpha a))*
      timeMassDensity a q ((c:ℝ≥0∞)^2*t) b (((c:ℝ):ℂ)*z) := by
  have he : (((c:ℝ):ℂ)*z).im*q=(c:ℝ)*(z.im*q) := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring
  simp only [timeMassDensity,he]
  change (if radialTime a (scaled c b.1) z (z.im*q)≤t then _ else _) = _
  simp only [radialTime_scaled_le_iff a hc b.1.continuous z (z.im*q) t,
    massDensity_scaled_upper a ha hc q hq hq1 b z hz]
  split_ifs <;> simp

end SLEExactGauge.LoewnerScaling
end
end

end OAI
