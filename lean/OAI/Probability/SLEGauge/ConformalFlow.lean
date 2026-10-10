import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.LoewnerSolutions

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
namespace ExactSLEMain
open Set Metric
theorem hasDerivAt_loewnerMap {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {T : ℝ≥0} {z : ℂ} (hz : alive A b T z) :
    HasDerivAt (loewnerMap A b T)
      (Complex.exp (∫ u in (0 : ℝ)..(T : ℝ),
        -(A : ℂ) / (loewnerMap A b u.toNNReal z - (b u.toNNReal : ℂ))^2)) z := by
  obtain ⟨ε,δ,F,hε,hδ,hFc,hFe,hode,hmap,hIm⟩ := loewner_local_cutoff hb hz
  have hzball : z ∈ ball z δ := mem_ball_self hδ
  let q : ℂ → ℝ → ℂ := fun w u => -(A : ℂ) /
    (heightClamp ε (F u.toNNReal w - (b u.toNNReal : ℂ)) *
     heightClamp ε (F u.toNNReal z - (b u.toNNReal : ℂ)))
  have hqc (w : ℂ) : Continuous (q w) := continuous_const.div
    (((heightClamp_lipschitz ε).continuous.comp
      (((hFc w).comp continuous_real_toNNReal).sub
        (Complex.continuous_ofReal.comp (hb.comp continuous_real_toNNReal)))).mul
     ((heightClamp_lipschitz ε).continuous.comp
      (((hFc z).comp continuous_real_toNNReal).sub
        (Complex.continuous_ofReal.comp (hb.comp continuous_real_toNNReal)))))
    (fun u => mul_ne_zero (heightClamp_ne_zero hε _) (heightClamp_ne_zero hε _))
  have hqw (u : ℝ) : Continuous (fun w => q w u) := continuous_const.div
    ((((heightClamp_lipschitz ε).continuous.comp
      ((cutoff_loewner_continuous_start hε hb hFc hFe u.toNNReal).sub continuous_const))).mul
      continuous_const)
    (fun w => mul_ne_zero (heightClamp_ne_zero hε _) (heightClamp_ne_zero hε _))
  have hIc : Continuous (fun w => ∫ u in (0 : ℝ)..(T : ℝ), q w u) :=
    intervalIntegral.continuous_of_dominated_interval
      (fun w => (hqc w).aestronglyMeasurable)
      (fun w => ae_of_all volume (fun u hu => invprod_heightClamp_bound A ε hε _ _))
      (show IntervalIntegrable (fun _ : ℝ => |A|/ε^2) volume 0 T from intervalIntegrable_const)
      (ae_of_all volume (fun u hu => hqw u))
  have hqe (w : ℂ) (hw : w ∈ ball z δ) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      q w u = -(A : ℂ) /
        ((F u.toNNReal w - (b u.toNNReal : ℂ)) * (F u.toNNReal z - (b u.toNNReal : ℂ))) := by
    have huT : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
    have hc₁ : heightClamp ε (F u.toNNReal w - (b u.toNNReal : ℂ)) =
        F u.toNNReal w - (b u.toNNReal : ℂ) := heightClamp_eq (by simpa using (hIm w hw _ huT).le)
    have hc₂ : heightClamp ε (F u.toNNReal z - (b u.toNNReal : ℂ)) =
        F u.toNNReal z - (b u.toNNReal : ℂ) := heightClamp_eq (by simpa using (hIm z hzball _ huT).le)
    simp only [q,hc₁,hc₂]
  have hIe (w : ℂ) (hw : w ∈ ball z δ) :
      (∫ u in (0 : ℝ)..(T : ℝ), q w u) =
      ∫ u in (0 : ℝ)..(T : ℝ), -(A : ℂ) /
        ((F u.toNNReal w - (b u.toNNReal : ℂ)) * (F u.toNNReal z - (b u.toNNReal : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact hqe w hw u (by simpa only [uIcc_of_le T.coe_nonneg] using hu)
  have hIz : (∫ u in (0 : ℝ)..(T : ℝ), q z u) =
      ∫ u in (0 : ℝ)..(T : ℝ),
        -(A : ℂ) / (loewnerMap A b u.toNNReal z - (b u.toNNReal : ℂ))^2 := by
    rw [hIe z hzball]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) T := by simpa only [uIcc_of_le T.coe_nonneg] using hu
    have huT : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu'.2).trans_eq (by simp)
    dsimp only
    rw [hmap z hzball _ huT,pow_two]
  rw [← hIz,hasDerivAt_iff_tendsto_slope]
  have ht := (Complex.continuous_exp.comp hIc).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z)
  apply ht.congr'
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ w in 𝓝 z, w ∈ ball z δ from Metric.ball_mem_nhds z hδ),
    self_mem_nhdsWithin] with w hw hwn
  have hwz : w ≠ z := by simpa only [mem_compl_iff,mem_singleton_iff] using hwn
  have hd := loewner_solution_difference hb (hode w hw) (hode z hzball)
  simp only [Real.toNNReal_coe] at hd
  rw [← hIe w hw] at hd
  rw [slope,vsub_eq_sub,smul_eq_mul,hmap w hw T le_rfl,hmap z hzball T le_rfl,hd]
  rw [← mul_assoc,inv_mul_cancel₀ (sub_ne_zero.mpr hwz),one_mul]
  rfl

lemma deriv_loewnerMap_ne_zero {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {T : ℝ≥0} {z : ℂ} (hz : alive A b T z) : deriv (loewnerMap A b T) z ≠ 0 := by
  rw [(hasDerivAt_loewnerMap hb hz).deriv]
  exact Complex.exp_ne_zero _

end ExactSLEMain

namespace ExactSLEMain
open Set

lemma loewnerMap_eq_solution_time {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {T : ℝ≥0}
    {f : ℝ → ℂ} (hf : odeUntil A b z T f) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) :
    loewnerMap A b u.toNNReal z = f u := by
  have huT : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
  simpa only [Real.coe_toNNReal _ hu.1] using loewnerMap_eq (odeUntil_mono hf huT)

lemma odeUntil_center_ne_zero {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {T : ℝ≥0}
    {f : ℝ → ℂ} (hf : odeUntil A b z T f) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) :
    f u - (b u.toNNReal : ℂ) ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  have hp := (hf.2 u hu).1
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
  linarith

lemma odeUntil_center_continuousOn {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil A b z T f) :
    ContinuousOn (fun u : ℝ => f u - (b u.toNNReal : ℂ)) (Icc (0 : ℝ) T) :=
  (odeUntil_continuousOn hf).sub
    (Complex.continuous_ofReal.comp (hb.comp continuous_real_toNNReal)).continuousOn

lemma loewner_derivative_integrable {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {T : ℝ≥0} {z : ℂ} (hz : alive A b T z) :
    IntervalIntegrable (fun u : ℝ => -(A : ℂ) /
      (loewnerMap A b u.toNNReal z - (b u.toNNReal : ℂ))^2) volume 0 T := by
  obtain ⟨f,hf⟩ := hz
  have hc : ContinuousOn (fun u : ℝ => -(A : ℂ) / (f u - (b u.toNNReal : ℂ))^2)
      (Icc (0 : ℝ) T) := continuousOn_const.div
    ((odeUntil_center_continuousOn hb hf).pow 2)
    (fun u hu => pow_ne_zero 2 (odeUntil_center_ne_zero hf hu))
  apply (hc.intervalIntegrable_of_Icc T.coe_nonneg).congr
  intro u hu
  dsimp only
  rw [loewnerMap_eq_solution_time hf (by
    simpa only [uIcc_of_le T.coe_nonneg] using (uIoc_subset_uIcc hu))]

 

theorem log_norm_deriv_loewnerMap {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {T : ℝ≥0} {z : ℂ} (hz : alive A b T z) :
    Real.log ‖deriv (loewnerMap A b T) z‖ =
      ∫ u in (0 : ℝ)..(T : ℝ), (-(A : ℂ) /
        (loewnerMap A b u.toNNReal z - (b u.toNNReal : ℂ))^2).re := by
  rw [(hasDerivAt_loewnerMap hb hz).deriv,Complex.norm_exp,Real.log_exp]
  exact (Complex.reCLM.intervalIntegral_comp_comm (loewner_derivative_integrable hb hz)).symm

lemma loewner_radius_drift (A : ℝ) (z : ℂ) (hz : z ≠ 0) :
    -A / Complex.normSq z - (-(A : ℂ)/z^2).re =
      -2*A*(z.im/Complex.normSq z)^2 := by
  have hn : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  simp only [Complex.div_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
    Complex.ofReal_im,neg_zero,zero_mul,zero_div,add_zero,map_pow]
  field_simp
  simp only [pow_two,Complex.mul_re,Complex.normSq_apply]
  ring

lemma real_scalar_linear_solution_on (H c : ℝ → ℝ) (T : ℝ≥0)
    (hc : ContinuousOn c (Icc (0 : ℝ) T))
    (hH : ∀ u ∈ Icc (0 : ℝ) T, HasDerivWithinAt H (c u * H u) (Icc (0 : ℝ) T) u) :
    H T = H 0 * Real.exp (∫ u in (0 : ℝ)..(T : ℝ), c u) := by
  have hc' : ContinuousOn (fun u => (c u : ℂ)) (Icc (0 : ℝ) T) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  have hd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt (fun u => (H u : ℂ)) ((c u : ℂ)*(H u : ℂ)) (Icc (0 : ℝ) T) u := by
    simpa only [Complex.ofReal_mul] using (hH u hu).ofReal_comp
  have he := scalar_linear_solution_on (fun u => (H u : ℂ)) (fun u => (c u : ℂ)) T hc' hd
  have hi := Complex.ofRealCLM.intervalIntegral_comp_comm (μ := volume) (hc.intervalIntegrable_of_Icc T.coe_nonneg)
  change (∫ u in (0 : ℝ)..(T : ℝ), (c u : ℂ)) = (∫ u in (0 : ℝ)..(T : ℝ), c u) at hi
  rw [hi,← Complex.ofReal_exp,← Complex.ofReal_mul] at he
  exact Complex.ofReal_injective he

 
theorem loewner_height_formula {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil A b z T f) :
    (f T).im = z.im * Real.exp (∫ u in (0 : ℝ)..(T : ℝ),
      -A / Complex.normSq (f u - (b u.toNNReal : ℂ))) := by
  have hc : ContinuousOn (fun u : ℝ => -A / Complex.normSq (f u - (b u.toNNReal : ℂ)))
      (Icc (0 : ℝ) T) := continuousOn_const.div
    (Complex.continuous_normSq.comp_continuousOn (odeUntil_center_continuousOn hb hf))
    (fun u hu => (Complex.normSq_pos.mpr (odeUntil_center_ne_zero hf hu)).ne')
  have hd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt (fun u => (f u).im)
        ((-A / Complex.normSq (f u - (b u.toNNReal : ℂ))) * (f u).im) (Icc (0 : ℝ) T) u := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt u (hf.2 u hu).2
    convert h using 1 <;> try rfl
    simp only [Complex.imCLM_apply,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,zero_div,zero_sub,Complex.sub_im,sub_zero]
    ring
  simpa only [hf.1] using real_scalar_linear_solution_on (fun u => (f u).im) _ T hc hd

 

theorem loewner_radius_ratio {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hz : alive A b T z) :
    (loewnerMap A b T z).im / ‖deriv (loewnerMap A b T) z‖ =
      z.im * Real.exp (-2*A * (∫ u in (0 : ℝ)..(T : ℝ),
        ((loewnerMap A b u.toNNReal z - (b u.toNNReal : ℂ)).im /
          Complex.normSq (loewnerMap A b u.toNNReal z - (b u.toNNReal : ℂ)))^2)) := by
  obtain ⟨f,hf⟩ := hz
  have hz : alive A b T z := ⟨f,hf⟩
  let Z : ℝ → ℂ := fun u => f u - (b u.toNNReal : ℂ)
  have hZc : ContinuousOn Z (Icc (0 : ℝ) T) := odeUntil_center_continuousOn hb hf
  have hZn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : Z u ≠ 0 := odeUntil_center_ne_zero hf hu
  have hJc : ContinuousOn (fun u => (-(A : ℂ)/(Z u)^2).re) (Icc (0 : ℝ) T) :=
    Complex.continuous_re.comp_continuousOn
      (continuousOn_const.div (hZc.pow 2) (fun u hu => pow_ne_zero 2 (hZn u hu)))
  have hYc : ContinuousOn (fun u => -A/Complex.normSq (Z u)) (Icc (0 : ℝ) T) :=
    continuousOn_const.div (Complex.continuous_normSq.comp_continuousOn hZc)
      (fun u hu => (Complex.normSq_pos.mpr (hZn u hu)).ne')
  have hJe : (∫ u in (0 : ℝ)..(T : ℝ), (-(A : ℂ)/
      (loewnerMap A b u.toNNReal z - (b u.toNNReal : ℂ))^2).re) =
      ∫ u in (0 : ℝ)..(T : ℝ), (-(A : ℂ)/(Z u)^2).re := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only [Z]
    rw [loewnerMap_eq_solution_time hf (by simpa only [uIcc_of_le T.coe_nonneg] using hu)]
  have hi : (∫ u in (0 : ℝ)..(T : ℝ), -A/Complex.normSq (Z u)) -
      (∫ u in (0 : ℝ)..(T : ℝ), (-(A : ℂ)/(Z u)^2).re) =
      -2*A*(∫ u in (0 : ℝ)..(T : ℝ), ((Z u).im/Complex.normSq (Z u))^2) := by
    rw [← intervalIntegral.integral_sub (hYc.intervalIntegrable_of_Icc T.coe_nonneg)
      (hJc.intervalIntegrable_of_Icc T.coe_nonneg),← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    exact loewner_radius_drift A (Z u) (hZn u (by simpa only [uIcc_of_le T.coe_nonneg] using hu))
  have hd : ‖deriv (loewnerMap A b T) z‖ =
      Real.exp (∫ u in (0 : ℝ)..(T : ℝ), (-(A : ℂ)/(Z u)^2).re) := by
    rw [← hJe, ← log_norm_deriv_loewnerMap hb hz,Real.exp_log (norm_pos_iff.mpr (deriv_loewnerMap_ne_zero hb hz))]
  rw [loewnerMap_eq hf,loewner_height_formula hb hf,hd,mul_div_assoc,← Real.exp_sub]
  change z.im * Real.exp ((∫ u in (0 : ℝ)..(T : ℝ), -A/Complex.normSq (Z u)) - _) = _
  rw [hi]
  congr 3
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only [Z]
  rw [loewnerMap_eq_solution_time hf (by simpa only [uIcc_of_le T.coe_nonneg] using hu)]

end ExactSLEMain

namespace ExactSLEGreen
abbrev State := ℂ × ℝ
noncomputable def X : State →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)
noncomputable def Y : State →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)
noncomputable def J : State →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℂ ℝ
noncomputable def Q (v : State) : ℝ := (X v)^2 + (Y v)^2
noncomputable def p (a : ℝ) : ℝ := 4*a-1
noncomputable def alpha (a : ℝ) : ℝ := 1-1/(4*a)
noncomputable def logGreen (a : ℝ) (v : State) : ℝ :=
  alpha a * J v + (p a-alpha a)*Real.log (Y v) - (p a/2)*Real.log (Q v)
noncomputable def physicalGreen (a : ℝ) (v : State) : ℝ := Real.exp (logGreen a v)
noncomputable def logGreenDeriv (a : ℝ) (v : State) : State →L[ℝ] ℝ :=
  alpha a • J + ((p a-alpha a)/(Y v)) • Y - ((p a/2)/(Q v)) •
    ((2*X v) • X + (2*Y v) • Y)
noncomputable def physicalDrift (a : ℝ) (v : State) : State :=
  ((a : ℂ)/v.1, (-(a : ℂ)/v.1^2).re)
def noise : State := (-1,0)

@[simp] lemma X_apply (v : State) : X v = v.1.re := rfl
@[simp] lemma Y_apply (v : State) : Y v = v.1.im := rfl
@[simp] lemma J_apply (v : State) : J v = v.2 := rfl
lemma Q_eq (v : State) : Q v = Complex.normSq v.1 := by
  simp only [Q,X_apply,Y_apply,Complex.normSq_apply,pow_two]
lemma Q_pos {v : State} (hv : 0 < Y v) : 0 < Q v := by
  change 0 < X v ^ 2 + Y v ^ 2
  nlinarith [sq_nonneg (X v),sq_pos_of_pos hv]

lemma hasFDerivAt_Q (v : State) :
    HasFDerivAt Q ((2*X v) • X + (2*Y v) • Y) v := by
  have hX : HasFDerivAt (fun v => X v) X v := X.hasFDerivAt
  have hY : HasFDerivAt (fun v => Y v) Y v := Y.hasFDerivAt
  convert (hX.pow 2).add (hY.pow 2) using 1 <;> try rfl
  simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat]

lemma hasFDerivAt_logGreen (a : ℝ) (v : State) (hv : 0 < Y v) :
    HasFDerivAt (logGreen a) (logGreenDeriv a v) v := by
  have hY := Y.hasFDerivAt.log hv.ne'
  have hQ := (hasFDerivAt_Q v).log (Q_pos hv).ne'
  convert ((J.hasFDerivAt.const_mul (alpha a)).add (hY.const_mul (p a-alpha a))).sub
    (hQ.const_mul (p a/2)) using 1 <;> try rfl
  simp only [logGreenDeriv,smul_smul,div_eq_mul_inv]

lemma hasFDerivAt_physicalGreen (a : ℝ) (v : State) (hv : 0 < Y v) :
    HasFDerivAt (physicalGreen a) (physicalGreen a v • logGreenDeriv a v) v :=
  (hasFDerivAt_logGreen a v hv).exp

lemma contDiffAt_physicalGreen (a : ℝ) (v : State) (hv : 0 < Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (physicalGreen a) v := by
  have hQc : ContDiff ℝ (↑(⊤ : ℕ∞)) Q := (X.contDiff.pow 2).add (Y.contDiff.pow 2)
  exact ((((contDiffAt_const (c := alpha a)).mul (J.contDiff.contDiffAt)).add
    ((contDiffAt_const (c := p a-alpha a)).mul (Y.contDiff.contDiffAt.log hv.ne'))).sub
    ((contDiffAt_const (c := p a/2)).mul (hQc.contDiffAt.log (Q_pos hv).ne'))).exp

lemma logGreenDeriv_noise (a : ℝ) (v : State) :
    logGreenDeriv a v noise = p a * X v / Q v := by
  simp only [logGreenDeriv,add_apply,sub_apply,
    smul_apply,smul_eq_mul,noise,X_apply,Y_apply,J_apply,
    Complex.neg_re,Complex.one_re,Complex.neg_im,Complex.one_im,neg_zero,mul_zero,
    mul_neg,mul_one,add_zero,zero_sub]
  ring

lemma logGreenDeriv_drift (a : ℝ) (v : State) (hv : 0 < Y v) :
    logGreenDeriv a v (physicalDrift a v) =
      -a*(alpha a+p a)*(X v^2-Y v^2)/(Q v)^2 - a*(p a-alpha a)/(Q v) := by
  have hy : Y v ≠ 0 := hv.ne'
  have hq : Q v ≠ 0 := (Q_pos hv).ne'
  simp only [logGreenDeriv,add_apply,sub_apply,
    smul_apply,smul_eq_mul,physicalDrift,X_apply,Y_apply,J_apply,
    Complex.div_re,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,neg_zero,zero_mul,zero_div,add_zero,zero_sub,map_pow]
  simp only [← Q_eq,pow_two,Complex.mul_re]
  change alpha a * (-a * (X v*X v-Y v*Y v)/(Q v*Q v)) +
    ((p a-alpha a)/Y v)*(- (a*Y v/Q v)) - ((p a/2)/Q v)*
      (2*X v*(a*X v/Q v) + 2*Y v*(- (a*Y v/Q v))) = _
  field_simp
  simp only [X_apply,Y_apply]
  ring

noncomputable def noiseLog (a : ℝ) (v : State) : ℝ := p a * X v / Q v
noncomputable def noiseLogDeriv (a : ℝ) (v : State) : State →L[ℝ] ℝ :=
  (p a / Q v) • X - (p a * X v / Q v^2) • ((2*X v) • X + (2*Y v) • Y)

lemma hasFDerivAt_noiseLog (a : ℝ) (v : State) (hv : 0 < Y v) :
    HasFDerivAt (noiseLog a) (noiseLogDeriv a v) v := by
  have hQinv := (hasDerivAt_inv (Q_pos hv).ne').comp_hasFDerivAt v (hasFDerivAt_Q v)
  convert (X.hasFDerivAt.const_mul (p a)).mul hQinv using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro w
  simp only [noiseLogDeriv,smul_apply,sub_apply,
    add_apply, smul_eq_mul,smul_smul,Function.comp_apply]
  ring

lemma noiseLogDeriv_noise (a : ℝ) (v : State) (hv : 0 < Y v) :
    noiseLogDeriv a v noise = p a * (X v^2-Y v^2)/(Q v)^2 := by
  have hq := (Q_pos hv).ne'
  simp only [noiseLogDeriv,sub_apply,smul_apply,add_apply,
    smul_eq_mul,noise,X_apply,Y_apply,Complex.neg_re,Complex.one_re,
    Complex.neg_im,Complex.one_im,neg_zero,mul_zero,mul_neg,mul_one,add_zero]
  field_simp
  unfold Q
  simp only [X_apply,Y_apply]
  ring

lemma green_fderiv_noise (a : ℝ) (v : State) (hv : 0 < Y v) :
    fderiv ℝ (physicalGreen a) v noise = physicalGreen a v * noiseLog a v := by
  rw [(hasFDerivAt_physicalGreen a v hv).fderiv]
  simp only [smul_apply,smul_eq_mul,logGreenDeriv_noise,noiseLog]

lemma hasFDerivAt_green_noise (a : ℝ) (v : State) (hv : 0 < Y v) :
    HasFDerivAt (fun w => fderiv ℝ (physicalGreen a) w noise)
      ((noiseLog a v) • (physicalGreen a v • logGreenDeriv a v) +
        (physicalGreen a v) • noiseLogDeriv a v) v := by
  have h := (hasFDerivAt_physicalGreen a v hv).mul (hasFDerivAt_noiseLog a v hv)
  rw [add_comm]
  apply h.congr_of_eventuallyEq
  filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hv)] with w hw
  exact green_fderiv_noise a w hw

lemma green_second_noise (a : ℝ) (v : State) (hv : 0 < Y v) :
    fderiv ℝ (fun w => fderiv ℝ (physicalGreen a) w noise) v noise =
      physicalGreen a v * ((p a)^2 * (X v)^2 + p a * (X v^2-Y v^2)) / (Q v)^2 := by
  rw [(hasFDerivAt_green_noise a v hv).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,
    logGreenDeriv_noise, noiseLogDeriv_noise a v hv,noiseLog]
  ring

 
lemma green_generator_zero (a : ℝ) (ha : a ≠ 0) (v : State) (hv : 0 < Y v) :
    (1/2 : ℝ) * fderiv ℝ (fun w => fderiv ℝ (physicalGreen a) w noise) v noise +
      fderiv ℝ (physicalGreen a) v (physicalDrift a v) = 0 := by
  rw [green_second_noise a v hv,(hasFDerivAt_physicalGreen a v hv).fderiv]
  simp only [smul_apply,smul_eq_mul,logGreenDeriv_drift a v hv]
  have hq := (Q_pos hv).ne'
  unfold alpha p
  field_simp
  unfold Q
  ring

end ExactSLEGreen

namespace ExactSLEGreen
open Metric

def spaceBump (N : ℝ≥0) : ContDiffBump (0 : State) where
  rIn := N+1
  rOut := N+2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def heightTurn (ε : ℝ) (v : State) : ℝ :=
  Real.smoothTransition (4 * Y v / ε - 1)

noncomputable def greenCutoff (a ε : ℝ) (N : ℝ≥0) (v : State) : ℝ :=
  spaceBump N v * heightTurn ε v * physicalGreen a v

lemma heightTurn_smooth (ε : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (heightTurn ε) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul Y.contDiff).div_const ε).sub contDiff_const)

lemma heightTurn_zero {ε : ℝ} (hε : 0 < ε) {v : State} (hv : Y v ≤ ε/4) :
    heightTurn ε v = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos,div_le_iff₀ hε]
  linarith

lemma heightTurn_one {ε : ℝ} (hε : 0 < ε) {v : State} (hv : ε/2 ≤ Y v) :
    heightTurn ε v = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le,le_div_iff₀ hε]
  linarith

lemma greenCutoff_smooth (a ε : ℝ) (hε : 0 < ε) (N : ℝ≥0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (greenCutoff a ε N) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : 0 < Y v
  · exact (((spaceBump N).contDiffAt.mul (heightTurn_smooth ε).contDiffAt).mul
      (contDiffAt_physicalGreen a v hv))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hv' : Y v < ε/4 := lt_of_le_of_lt (le_of_not_gt hv) (by positivity)
    filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Iio_mem_nhds hv')] with w hw
    simp only [greenCutoff,heightTurn_zero hε (le_of_lt hw),mul_zero,zero_mul]

lemma greenCutoff_compact (a ε : ℝ) (N : ℝ≥0) : HasCompactSupport (greenCutoff a ε N) :=
  ((spaceBump N).hasCompactSupport.mul_right).mul_right

lemma greenCutoff_eq_near (a ε : ℝ) (hε : 0 < ε) (N : ℝ≥0)
    (v : State) (hv : ‖v‖ ≤ N) (hy : ε ≤ Y v) :
    greenCutoff a ε N =ᶠ[𝓝 v] physicalGreen a := by
  have hv' : v ∈ ball (0 : State) (spaceBump N).rIn := by
    simp only [mem_ball,dist_zero_right,spaceBump]
    linarith
  have hy' : ε/2 < Y v := lt_of_lt_of_le (by linarith) hy
  filter_upwards [(spaceBump N).eventuallyEq_one_of_mem_ball hv',
    Y.continuous.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hy')] with w hw hyw
  simp only [greenCutoff,hw,heightTurn_one hε (le_of_lt hyw),Pi.one_apply,one_mul]

lemma greenCutoff_generator_zero (a ε : ℝ) (ha : a ≠ 0) (hε : 0 < ε) (N : ℝ≥0)
    (v : State) (hv : ‖v‖ ≤ N) (hy : ε ≤ Y v) :
    (1/2 : ℝ) * fderiv ℝ (fun w => fderiv ℝ (greenCutoff a ε N) w noise) v noise +
      fderiv ℝ (greenCutoff a ε N) v (physicalDrift a v) = 0 := by
  have he := greenCutoff_eq_near a ε hε N v hv hy
  have hd : (fun w => fderiv ℝ (greenCutoff a ε N) w noise) =ᶠ[𝓝 v]
      (fun w => fderiv ℝ (physicalGreen a) w noise) :=
    he.fderiv.mono fun w hw => congrArg (fun f : State →L[ℝ] ℝ => f noise) hw
  rw [hd.fderiv_eq,he.fderiv_eq]
  exact green_generator_zero a ha v (hε.trans_le hy)

end ExactSLEGreen

end

end OAI
