import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.AngleGenerators

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
open Filter Set
namespace ExactSLEFiniteTilt
open Filter
open scoped Topology

lemma regFactor_hasDerivAt (a δ θ : ℝ) (hθ : 0 < Real.sin θ) :
    HasDerivAt (regFactor a δ)
      (Real.cos θ*regP a*Real.sin θ^(regP a-1) +
        δ*(Real.cos θ*regQ a*Real.sin θ^(regQ a-1))) θ := by
  convert (sinePower_hasDerivAt (regP a) θ hθ).add
      (((sinePower_hasDerivAt (regQ a) θ hθ).const_add 1).const_mul δ) using 1
  rfl

lemma sineDerivative_hasDerivAt (r θ : ℝ) (hθ : 0 < Real.sin θ) :
    HasDerivAt (fun x => Real.cos x*r*Real.sin x^(r-1))
      (deriv (deriv (sinePower r)) θ) θ := by
  rw [sinePower_secondDeriv r θ hθ]
  convert ((Real.hasDerivAt_cos θ).mul_const r).mul
    ((Real.hasDerivAt_sin θ).rpow_const (p := r-1) (Or.inl hθ.ne')) using 1
  congr 2
  ring_nf

lemma regFactor_secondDeriv (a δ θ : ℝ) (hθ : 0 < Real.sin θ) :
    deriv (deriv (regFactor a δ)) θ = deriv (deriv (sinePower (regP a))) θ +
      δ*deriv (deriv (sinePower (regQ a))) θ := by
  have he : deriv (regFactor a δ) =ᶠ[𝓝 θ]
      (fun x => Real.cos x*regP a*Real.sin x^(regP a-1) +
        δ*(Real.cos x*regQ a*Real.sin x^(regQ a-1))) := by
    have hp : ∀ᶠ x in 𝓝 θ, 0 < Real.sin x :=
      (isOpen_lt continuous_const Real.continuous_sin).mem_nhds hθ
    filter_upwards [hp] with x hx using (regFactor_hasDerivAt a δ x hx).deriv
  rw [he.deriv_eq]
  exact ((sineDerivative_hasDerivAt (regP a) θ hθ).add
    ((sineDerivative_hasDerivAt (regQ a) θ hθ).const_mul δ)).deriv

lemma regFactor_generator (a δ θ : ℝ) (hθ : 0 < Real.sin θ) :
    angleGenerator (1-2*a) (regFactor a δ) θ =
      angleGenerator (1-2*a) (sinePower (regP a)) θ +
      δ*angleGenerator (1-2*a) (sinePower (regQ a)) θ := by
  dsimp only [angleGenerator]
  rw [regFactor_secondDeriv a δ θ hθ,(regFactor_hasDerivAt a δ θ hθ).deriv,
    (sinePower_hasDerivAt (regP a) θ hθ).deriv,
    (sinePower_hasDerivAt (regQ a) θ hθ).deriv]
  ring

lemma sinePower_mul_cot_sq (r θ : ℝ) (hθ : 0 < Real.sin θ) :
    sinePower r θ*Real.cot θ^2 = Real.sin θ^(r-2)-sinePower r θ := by
  dsimp only [sinePower]
  rw [Real.cot_eq_cos_div_sin,div_pow,Real.rpow_sub hθ,Real.rpow_two]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma regFactor_exact_drift (a δ σ θ : ℝ) (hθ : 0 < Real.sin θ) :
    regNormalizedDrift a δ σ θ = δ/regFactor a δ θ *
      (regP a/2+(regP a-regQ a)*(1+regQ a)/2*Real.sin θ^(regQ a) -
        regK a*Real.sin θ^(regQ a-2) + σ*(1+Real.sin θ^(regQ a))) := by
  have hG := angleGenerator_sinePower (1-2*a) (regQ a) θ hθ
  have hP := angleGenerator_sinePower (1-2*a) (regP a) θ hθ
  have hpq : regP a-1+2*(1-2*a) = 0 := by dsimp [regP]; ring
  have hqp : regQ a-1+2*(1-2*a) = regQ a-regP a := by dsimp [regP]; ring
  simp only [hpq,hqp] at hP hG
  rw [show sinePower (regQ a) θ *
    (-regQ a/2+regQ a*(regQ a-regP a)/2*Real.cot θ^2) =
      -regQ a/2*sinePower (regQ a) θ + regQ a*(regQ a-regP a)/2*
        (sinePower (regQ a) θ*Real.cot θ^2) by ring,
    sinePower_mul_cot_sq _ _ hθ] at hG
  dsimp only [regNormalizedDrift]
  rw [regFactor_generator a δ θ hθ,hP,hG]
  dsimp only [regFactor,regK,sinePower]
  ring

end ExactSLEFiniteTilt

namespace ExactSLEFiniteTilt

lemma regFactor_bounds {a δ θ : ℝ} (ha : 1/4 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < Real.sin θ) :
    0 < regFactor a δ θ ∧ δ ≤ regFactor a δ θ ∧
    Real.sin θ^(regP a) ≤ regFactor a δ θ ∧ regFactor a δ θ ≤ 3 := by
  have hs1 := Real.sin_le_one θ
  have hp := Real.rpow_pos_of_pos hθ (regP a)
  have hq := Real.rpow_pos_of_pos hθ (regQ a)
  have hp1 := Real.rpow_le_one hθ.le hs1 (regP_pos ha).le
  have hq1 := Real.rpow_le_one hθ.le hs1 (regQ_pos ha).le
  dsimp only [regFactor,sinePower]
  have hmul := mul_nonneg hδ.le hq.le
  have hm1 := mul_le_mul_of_nonneg_left hq1 hδ.le
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

lemma regDrift_bound {a δ σ θ : ℝ} (ha : 1/4 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ : |σ| ≤ regBeta a) (hθ : 0 < Real.sin θ) :
    regNormalizedDrift a δ σ θ ≤ regC a*δ-regK a/2*regD a δ θ := by
  obtain ⟨hfp,hδf,hspf,hf3⟩ := regFactor_bounds ha hδ hδ1 hθ
  have hp := regP_pos ha
  have hq := regQ_pos ha
  have hq1 := regQ_lt_one ha
  have hpq := sub_pos.mpr (regQ_lt_p ha)
  have hk := regK_pos ha
  have hA := regA_pos ha
  have hs0 := Real.rpow_pos_of_pos hθ (regQ a)
  have hs1 := Real.rpow_le_one hθ.le (Real.sin_le_one θ) hq.le
  have hσ1 : σ ≤ 1 := (le_abs_self σ).trans (hσ.trans (regBeta_le_one a))
  have hσterm := mul_le_mul_of_nonneg_right hσ1 (show 0 ≤ 1+Real.sin θ^(regQ a) by positivity)
  have hqterm := mul_le_mul_of_nonneg_left hs1
    (show 0 ≤ (regP a-regQ a)*(1+regQ a)/2 by positivity)
  have hbracket : regP a/2+(regP a-regQ a)*(1+regQ a)/2*Real.sin θ^(regQ a) -
      regK a*Real.sin θ^(regQ a-2) + σ*(1+Real.sin θ^(regQ a)) ≤
      regA a-regK a*Real.sin θ^(regQ a-2) := by
    dsimp only [regA]; linarith
  have hx : 0 ≤ δ/regFactor a δ θ := (div_pos hδ hfp).le
  have hraw := mul_le_mul_of_nonneg_left hbracket hx
  rw [←regFactor_exact_drift a δ σ θ hθ] at hraw
  have hD : 0 ≤ regD a δ θ := mul_nonneg hx (Real.rpow_nonneg hθ.le _)
  by_cases hsmall : Real.sin θ < regH a
  · have hpow := Real.rpow_le_rpow_of_nonpos hθ hsmall.le (show regQ a-2 ≤ 0 by linarith)
    rw [regH_power ha] at hpow
    have hthresh : regA a ≤ regK a/2*Real.sin θ^(regQ a-2) := by
      have hh := (div_le_iff₀ hk).mp hpow
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hthresh hx
    have hCδ : 0 ≤ regC a*δ := mul_nonneg (regC_pos ha).le hδ.le
    dsimp only [regD]
    nlinarith
  · have hpow := Real.rpow_le_rpow (regH_pos ha).le (le_of_not_gt hsmall) hp.le
    have hpowf := hpow.trans hspf
    have hdiv := div_le_div_of_nonneg_left hA.le (Real.rpow_pos_of_pos (regH_pos ha) (regP a)) hpowf
    have hh := mul_le_mul_of_nonneg_left hdiv hδ.le
    have hC : regC a = regA a/(regH a^(regP a)) := by
      dsimp [regC]; rw [Real.rpow_neg (regH_pos ha).le]; ring
    rw [←hC] at hh
    have hKD := mul_nonneg hk.le hD
    dsimp only [regD] at hD hKD ⊢
    simp only [div_eq_mul_inv] at hraw hh hKD ⊢
    nlinarith only [hraw,hh,hKD]

end ExactSLEFiniteTilt

namespace ExactSLEFiniteTilt

lemma regFactor_derivative_simple {a δ θ : ℝ} (ha : 1/4 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < Real.sin θ) :
    |deriv (regFactor a δ) θ| ≤ (regP a+regQ a)*Real.sin θ^(regQ a-1) := by
  have hp := regP_pos ha
  have hq := regQ_pos ha
  have hpq := regQ_lt_p ha
  have hs1 := Real.sin_le_one θ
  have hsp := Real.rpow_pos_of_pos hθ (regP a-1)
  have hsq := Real.rpow_pos_of_pos hθ (regQ a-1)
  have hpow := Real.rpow_le_rpow_of_exponent_ge hθ hs1 (show regQ a-1 ≤ regP a-1 by linarith)
  have hpp := mul_le_mul_of_nonneg_left hpow hp.le
  have hδp := mul_le_mul_of_nonneg_right hδ1 (mul_nonneg hq.le hsq.le)
  have hcos := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ)
    (show 0 ≤ regP a*Real.sin θ^(regP a-1)+δ*regQ a*Real.sin θ^(regQ a-1) by positivity)
  rw [(regFactor_hasDerivAt a δ θ hθ).deriv]
  rw [show Real.cos θ*regP a*Real.sin θ^(regP a-1)+
    δ*(Real.cos θ*regQ a*Real.sin θ^(regQ a-1)) =
      Real.cos θ*(regP a*Real.sin θ^(regP a-1)+δ*regQ a*Real.sin θ^(regQ a-1)) by ring]
  rw [abs_mul,abs_of_nonneg (show 0 ≤ regP a*Real.sin θ^(regP a-1)+
    δ*regQ a*Real.sin θ^(regQ a-1) by positivity)]
  nlinarith

lemma regFactor_interpolation {a δ θ : ℝ} (ha : 1/4 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < Real.sin θ) :
    Real.sin θ^(regQ a-1)/regFactor a δ θ ≤
      3^(regEta a)*δ^(-1-regEta a)*(regD a δ θ)^(regEta a) := by
  obtain ⟨hfp,hδf,hspf,hf3⟩ := regFactor_bounds ha hδ hδ1 hθ
  have hη := regEta_pos ha
  have hs := Real.rpow_pos_of_pos hθ (regQ a-1)
  have hiden : 3^(regEta a)*δ^(-1-regEta a)*(regD a δ θ)^(regEta a) =
      (3/regFactor a δ θ)^(regEta a)*Real.sin θ^(regQ a-1)/δ := by
    dsimp only [regD]
    rw [Real.mul_rpow (div_nonneg hδ.le hfp.le) (Real.rpow_nonneg hθ.le _),
      Real.div_rpow hδ.le hfp.le,←Real.rpow_mul hθ.le,
      mul_comm (regQ a-2) (regEta a),regEta_identity ha,
      Real.rpow_sub hδ,Real.rpow_neg_one,
      Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) hfp.le]
    field_simp
  have hpow : 1 ≤ (3/regFactor a δ θ)^(regEta a) :=
    Real.one_le_rpow ((one_le_div hfp).mpr hf3) hη.le
  have hdiv := div_le_div_of_nonneg_left hs.le hδ hδf
  rw [hiden]
  calc
    _ ≤ Real.sin θ^(regQ a-1)/δ := hdiv
    _ ≤ _ := div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_right hpow hs.le]) hδ.le

lemma regDerivative_bound {a δ θ : ℝ} (ha : 1/4 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < Real.sin θ) :
    |deriv (regFactor a δ) θ|/regFactor a δ θ ≤
      (regP a+regQ a)*3^(regEta a)*δ^(-1-regEta a)*(regD a δ θ)^(regEta a) := by
  have hf := (regFactor_bounds ha hδ hδ1 hθ).1
  have hsimple := div_le_div_of_nonneg_right (regFactor_derivative_simple ha hδ hδ1 hθ) hf.le
  have hinter := mul_le_mul_of_nonneg_left (regFactor_interpolation ha hδ hδ1 hθ)
    (add_nonneg (regP_pos ha).le (regQ_pos ha).le)
  calc
    _ ≤ (regP a+regQ a)*Real.sin θ^(regQ a-1)/regFactor a δ θ := hsimple
    _ = (regP a+regQ a)*(Real.sin θ^(regQ a-1)/regFactor a δ θ) := by ring
    _ ≤ _ := hinter
    _ = _ := by ring

 
theorem regularized_factor_estimates {a δ σ θ : ℝ} (ha : 1/4 < a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : |σ| ≤ regBeta a)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    0 < regBeta a ∧ 2*regM a*regBeta a < a ∧
    0 < regK a ∧ 0 < regC a ∧
    regNormalizedDrift a δ σ θ ≤ regC a*δ-regK a/2*regD a δ θ ∧
    |deriv (regFactor a δ) θ|/regFactor a δ θ ≤
      (regP a+regQ a)*3^(regEta a)*δ^(-1-regEta a)*(regD a δ θ)^(regEta a) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  exact ⟨regBeta_pos ha,regBeta_discount ha,regK_pos ha,regC_pos ha,
    regDrift_bound ha hδ hδ1 hσ hs,regDerivative_bound ha hδ hδ1 hs⟩

end ExactSLEFiniteTilt

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt
noncomputable def physicalDelta (a cap σ off : ℝ) (v : State) : ℝ :=
  Real.exp (off+σ*physicalClock a cap v)
noncomputable def physicalRegularized (a cap σ off : ℝ) (v : State) : ℝ :=
  clockExp a cap (regP a/2) v/3*regFactor a (physicalDelta a cap σ off v) (physicalTheta v)
lemma clockExp_shift (a cap c σ off : ℝ) (v : State) :
    clockExp a cap c v*physicalDelta a cap σ off v = Real.exp off*clockExp a cap (c+σ) v := by
  dsimp only [clockExp,physicalDelta]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  ring
lemma physicalRegularized_decomposition (a cap σ off : ℝ) :
    physicalRegularized a cap σ off = fun v => (1/3:ℝ)*
      (clockExp a cap (regP a/2) v*angleLift (sinePower (regP a)) v +
        Real.exp off*(clockExp a cap (regP a/2+σ) v +
          clockExp a cap (regP a/2+σ) v*angleLift (sinePower (regQ a)) v)) := by
  funext v
  have h := clockExp_shift a cap (regP a/2) σ off v
  dsimp only [physicalRegularized,regFactor,angleLift]
  nlinarith only [h,h |> congrArg (fun x => x*sinePower (regQ a) (physicalTheta v))]
lemma physicalRegularized_smooth (a cap σ off : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ 2 (physicalRegularized a cap σ off) v := by
  have hθ := physicalTheta_mem v
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [physicalRegularized_decomposition]
  apply contDiffAt_const.mul
  exact (((clockExp_smooth a cap (regP a/2) v hv).mul
    (angleLift_smooth _ v hv (sinePower_smooth _ _ hs))).add
    (contDiffAt_const.mul ((clockExp_smooth a cap (regP a/2+σ) v hv).add
      ((clockExp_smooth a cap (regP a/2+σ) v hv).mul
        (angleLift_smooth _ v hv (sinePower_smooth _ _ hs))))))
lemma physicalRegularized_L (a cap σ off : ℝ) (ha : a≠0) (v : State) (hv : 0<Y v) :
    L (physicalRegularized a cap σ off) (physicalDrift a v) noise v =
      clockExp a cap (regP a/2) v/3*
      (angleGenerator (1-2*a) (regFactor a (physicalDelta a cap σ off v)) (physicalTheta v) +
        regP a/2*regFactor a (physicalDelta a cap σ off v) (physicalTheta v) +
        σ*physicalDelta a cap σ off v*(1+sinePower (regQ a) (physicalTheta v)))*(physicalV v)^2 := by
  have hθ := physicalTheta_mem v
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hp := (clockExp_smooth a cap (regP a/2) v hv).mul
    (angleLift_smooth _ v hv (sinePower_smooth (regP a) _ hs))
  have hq := (clockExp_smooth a cap (regP a/2+σ) v hv).mul
    (angleLift_smooth _ v hv (sinePower_smooth (regQ a) _ hs))
  have hc := clockExp_smooth a cap (regP a/2+σ) v hv
  rw [physicalRegularized_decomposition,L_const_mul (hp.add (contDiffAt_const.mul (hc.add hq))),
    L_add hp (contDiffAt_const.mul (hc.add hq)),L_const_mul (hc.add hq),L_add hc hq,
    clockExp_L a cap (regP a/2+σ) ha v hv,
    exponential_angle_generator _ a cap (regP a/2) ha v hv (sinePower_smooth _ _ hs),
    exponential_angle_generator _ a cap (regP a/2+σ) ha v hv (sinePower_smooth _ _ hs),
    regFactor_generator _ _ _ hs]
  dsimp only [regFactor]
  have h := clockExp_shift a cap (regP a/2) σ off v
  linear_combination -(physicalV v)^2/3 *
    ((regP a/2+σ)*(1+sinePower (regQ a) (physicalTheta v)) +
      angleGenerator (1-2*a) (sinePower (regQ a)) (physicalTheta v)) * h
lemma physicalRegularized_N (a cap σ off : ℝ) (v : State) (hv : 0<Y v) :
    N (physicalRegularized a cap σ off) noise v =
      clockExp a cap (regP a/2) v/3*
        deriv (regFactor a (physicalDelta a cap σ off v)) (physicalTheta v)*physicalV v := by
  have hθ := physicalTheta_mem v
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have he := (clockExp_smooth a cap (regP a/2) v hv).differentiableAt (by norm_num)
  have hc := (clockExp_smooth a cap (regP a/2+σ) v hv).differentiableAt (by norm_num)
  have hp := (angleLift_smooth _ v hv (sinePower_smooth (regP a) _ hs)).differentiableAt (by norm_num)
  have hq := (angleLift_smooth _ v hv (sinePower_smooth (regQ a) _ hs)).differentiableAt (by norm_num)
  have hconst : DifferentiableAt ℝ (fun _ : State => Real.exp off) v := differentiableAt_const _
  erw [physicalRegularized_decomposition,N_const_mul ((he.mul hp).add (hconst.mul (hc.add (hc.mul hq)))) (1/3:ℝ),
    N_add (he.mul hp) (hconst.mul (hc.add (hc.mul hq))),N_const_mul (hc.add (hc.mul hq)) (Real.exp off),
    N_add hc (hc.mul hq),N_mul he hp,N_mul hc hq,
    clockExp_N a cap (regP a/2) v hv,clockExp_N a cap (regP a/2+σ) v hv,
    angleLift_N _ v hv (sinePower_hasDerivAt (regP a) _ hs).differentiableAt,
    angleLift_N _ v hv (sinePower_hasDerivAt (regQ a) _ hs).differentiableAt,
    (regFactor_hasDerivAt a _ _ hs).deriv,
    (sinePower_hasDerivAt (regP a) _ hs).deriv,(sinePower_hasDerivAt (regQ a) _ hs).deriv]
  have h := clockExp_shift a cap (regP a/2) σ off v
  linear_combination -(Real.cos (physicalTheta v)*regQ a*
    Real.sin (physicalTheta v)^(regQ a-1)*physicalV v/3)*h

 
theorem actual_regularized_factor {a cap σ off : ℝ} (ha : 1/4<a)
    (v : State) (hv : 0<Y v) (hδ : physicalDelta a cap σ off v≤1) (hσ : |σ|≤regBeta a) :
    0<physicalRegularized a cap σ off v ∧
    L (physicalRegularized a cap σ off) (physicalDrift a v) noise v / physicalRegularized a cap σ off v ≤
      (regC a*physicalDelta a cap σ off v-regK a/2*regD a (physicalDelta a cap σ off v) (physicalTheta v))*(physicalV v)^2 ∧
    |N (physicalRegularized a cap σ off) noise v|/physicalRegularized a cap σ off v ≤
      (regP a+regQ a)*3^(regEta a)*(physicalDelta a cap σ off v)^(-1-regEta a)*
        (regD a (physicalDelta a cap σ off v) (physicalTheta v))^(regEta a)*physicalV v := by
  have hθ := physicalTheta_mem v
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hδp : 0<physicalDelta a cap σ off v := Real.exp_pos _
  have hf := (regFactor_bounds ha hδp hδ hs).1
  have he : 0<clockExp a cap (regP a/2) v := Real.exp_pos _
  have hV : 0<physicalV v := div_pos hv (Q_pos hv)
  have hpos : 0<physicalRegularized a cap σ off v := by
    dsimp only [physicalRegularized]; positivity
  refine ⟨hpos,?_,?_⟩
  · have hL : L (physicalRegularized a cap σ off) (physicalDrift a v) noise v /
        physicalRegularized a cap σ off v =
          regNormalizedDrift a (physicalDelta a cap σ off v) σ (physicalTheta v)*(physicalV v)^2 := by
      rw [physicalRegularized_L a cap σ off (by linarith) v hv]
      dsimp only [physicalRegularized,regNormalizedDrift]
      field_simp
    rw [hL]
    exact mul_le_mul_of_nonneg_right (regDrift_bound ha hδp hδ hσ hs) (sq_nonneg _)
  · rw [physicalRegularized_N a cap σ off v hv,abs_mul,abs_mul,
      abs_of_pos (div_pos he (by norm_num)),abs_of_pos hV]
    have hN : clockExp a cap (regP a/2) v/3 *
        |deriv (regFactor a (physicalDelta a cap σ off v)) (physicalTheta v)| * physicalV v /
        physicalRegularized a cap σ off v =
        |deriv (regFactor a (physicalDelta a cap σ off v)) (physicalTheta v)| /
          regFactor a (physicalDelta a cap σ off v) (physicalTheta v)*physicalV v := by
      dsimp only [physicalRegularized]; field_simp
    rw [hN]
    exact mul_le_mul_of_nonneg_right (regDerivative_bound ha hδp hδ hs) hV.le

end ExactSLEGreen

namespace ExactSLEFiniteTilt

lemma weighted_pair_young {η ε C X Y Z : ℝ} (hη : 0<η) (hη2 : η<1/2)
    (hε : 0<ε) (hC : 0<C) (hX : 0≤X) (hY : 0≤Y) (hZ : 0≤Z) :
    C*X^η*Y^η*Z^(1-2*η) ≤ ε*(X+Y) +
      (1-2*η)*C^(1/(1-2*η))*(η/ε)^(2*η/(1-2*η))*Z := by
  let r : ℝ := 1-2*η
  have hr : 0<r := by dsimp [r]; linarith
  let A : ℝ := (C*(η/ε)^(2*η))^(1/r)
  have hA : 0<A := by dsimp [A]; positivity
  have hg := Real.geom_mean_le_arith_mean3_weighted hη.le hη.le hr.le
    (show 0≤ε/η*X by positivity) (show 0≤ε/η*Y by positivity)
    (show 0≤A*Z by positivity) (show η+η+r=1 by dsimp [r]; ring)
  have hAr : A^r = C*(η/ε)^(2*η) := by
    dsimp [A]
    rw [← Real.rpow_mul (by positivity : 0≤C*(η/ε)^(2*η)),div_mul_cancel₀ _ hr.ne',Real.rpow_one]
  have hcancel : (ε/η)^η*(ε/η)^η*(η/ε)^(2*η)=1 := by
    rw [← Real.rpow_add (by positivity),show η+η=2*η by ring,
      ← Real.mul_rpow (by positivity) (by positivity)]
    have he : ε/η*(η/ε)=1 := by field_simp
    rw [he,Real.one_rpow]
  have hleft : (ε/η*X)^η*(ε/η*Y)^η*(A*Z)^r = C*X^η*Y^η*Z^r := by
    rw [Real.mul_rpow (by positivity) hX,Real.mul_rpow (by positivity) hY,
      Real.mul_rpow hA.le hZ,hAr]
    calc
      _ = C*X^η*Y^η*Z^r*((ε/η)^η*(ε/η)^η*(η/ε)^(2*η)) := by ring
      _ = _ := by rw [hcancel,mul_one]
  rw [hleft] at hg
  have hAe : A = C^(1/r)*(η/ε)^(2*η/r) := by
    dsimp [A]
    rw [Real.mul_rpow hC.le (by positivity),← Real.rpow_mul (by positivity)]
    congr 2
    ring
  have hs : η*(ε/η*X)+η*(ε/η*Y)=ε*(X+Y) := by field_simp
  rw [hs,hAe] at hg
  simpa only [r,mul_assoc] using hg

noncomputable def regC2 (a : ℝ) : ℝ := (regP a+regQ a)^2 * 3^(2*regEta a)
noncomputable def regYoungC (a ε : ℝ) : ℝ :=
  (1-2*regEta a) * regC2 a ^ (1/(1-2*regEta a)) *
    (regEta a/ε) ^ (2*regEta a/(1-2*regEta a))

lemma regC2_pos {a : ℝ} (ha : 1/4<a) : 0<regC2 a := by
  have hp := regP_pos ha
  have hq := regQ_pos ha
  dsimp [regC2]
  positivity

 
theorem regularized_pair_absorption {a ε δᵢ δⱼ Dᵢ Dⱼ Vᵢ Vⱼ : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hδᵢ : 0<δᵢ) (hδⱼ : 0<δⱼ)
    (hDᵢ : 0≤Dᵢ) (hDⱼ : 0≤Dⱼ) (hVᵢ : 0≤Vᵢ) (hVⱼ : 0≤Vⱼ) :
    regC2 a * (δᵢ*δⱼ)^(-1-regEta a) *
      (Dᵢ*Vᵢ^2)^(regEta a)*(Dⱼ*Vⱼ^2)^(regEta a)*(Vᵢ*Vⱼ)^(1-2*regEta a) ≤
    ε*(Dᵢ*Vᵢ^2+Dⱼ*Vⱼ^2) + regYoungC a ε*(δᵢ*δⱼ)^(-regM a)*Vᵢ*Vⱼ := by
  have hC := regC2_pos ha
  have hd : 0<δᵢ*δⱼ := mul_pos hδᵢ hδⱼ
  have hy := weighted_pair_young (regEta_pos ha) (regEta_lt_half ha) hε
    (show 0<regC2 a*(δᵢ*δⱼ)^(-1-regEta a) by positivity)
    (show 0≤Dᵢ*Vᵢ^2 by positivity) (show 0≤Dⱼ*Vⱼ^2 by positivity)
    (show 0≤Vᵢ*Vⱼ by positivity)
  have he : (regC2 a*(δᵢ*δⱼ)^(-1-regEta a))^(1/(1-2*regEta a)) =
      regC2 a^(1/(1-2*regEta a))*(δᵢ*δⱼ)^(-regM a) := by
    rw [Real.mul_rpow hC.le (by positivity),← Real.rpow_mul hd.le]
    congr 2
    dsimp [regM]
    ring
  rw [he] at hy
  dsimp only [regYoungC]
  convert hy using 1
  ring

end ExactSLEFiniteTilt

namespace ExactSLECalculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end ExactSLECalculus
end

end OAI
