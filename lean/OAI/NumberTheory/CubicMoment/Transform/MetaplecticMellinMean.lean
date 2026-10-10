import OAI.NumberTheory.CubicMoment.Estimates.TypeIHeight
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Absolute Fubini for the metaplectic height average. The integrable
majorant is deduced from the published mean square and the actual smooth
Mellin transform; no contour identity is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- A bound for the integral in the finite height variable is enough for
absolute Fubini and a bound after integrating in the other variable. -/
lemma integral_height_norm_le (K : ℝ × ℝ → ℂ) (hK : Continuous K)
    {a b : ℝ} (hab : a ≤ b) (B : ℝ → ℝ) (hB : Integrable B)
    (hbound : ∀ v : ℝ, (∫ t in a..b, ‖K (v,t)‖) ≤ B v) :
    (∫ t in a..b, ‖∫ v : ℝ, K (v,t)‖) ≤ ∫ v : ℝ, B v := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hm : AEStronglyMeasurable K (volume.prod μ) := hK.aestronglyMeasurable
  have hb (v : ℝ) : (∫ t, ‖K (v,t)‖ ∂μ) ≤ B v := by
    simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
      using hbound v
  have hi : Integrable K (volume.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun v =>
        (hK.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc)
    · apply hB.mono' hm.norm.integral_prod_right'
      exact Filter.Eventually.of_forall (fun v => by
        rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => _root_.norm_nonneg _))]
        exact hb v)
  have h := calc
    (∫ t, ‖∫ v : ℝ, K (v,t)‖ ∂μ) ≤ ∫ t, (∫ v : ℝ, ‖K (v,t)‖) ∂μ :=
      integral_mono hi.integral_prod_right.norm hi.integral_norm_prod_right
        (fun t => norm_integral_le_integral_norm _)
    _ = ∫ v : ℝ, ∫ t, ‖K (v,t)‖ ∂μ := (integral_integral_swap hi.norm).symm
    _ ≤ ∫ v : ℝ, B v := integral_mono hi.integral_norm_prod_left hB hb
  simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab] using h

lemma mellin_linear_weight_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    Integrable (fun v : ℝ => ‖mellin W ((σ:ℂ)+(v:ℂ)*Complex.I)‖*(3+|v|)) := by
  let F := mellinVerticalSchwartz W hW hpos hsm σ
  have h0 : Integrable (fun v : ℝ => 3*‖F v‖) := F.integrable.norm.const_mul (3:ℝ)
  have h1 := F.integrable_pow_mul volume 1
  convert h0.add h1 using 1
  ext v
  change _ = 3*‖F v‖+‖v‖^1*‖F v‖
  rw [show F v = mellin W ((σ:ℂ)+(v:ℂ)*Complex.I) from
    mellinVerticalSchwartz_apply W hW hpos hsm σ v]
  simp only [pow_one,Real.norm_eq_abs]
  ring

/-- The actual shifted Mellin integral satisfies the required square-root
height mean. This step uses only HB's mean square, continuation on the
integration line, and the decay of the chosen smooth weight. -/
theorem metaplectic_mellin_height_mean {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ U : ℝ, 0 < U → ∀ T : ℝ, 1 ≤ T →
      (∫ t in -(2*T)..(2*T), ‖∫ v : ℝ,
        mellin W ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)*
          (U:ℂ)^((1/2+ε:ℝ)+(v:ℂ)*Complex.I)*
          F r ((1/2+ε:ℝ)+((v-t):ℂ)*Complex.I)‖)/T ≤
        C*U^(1/2+ε)*(norm r)^(1/4+2*ε)*Real.sqrt T := by
  obtain ⟨K,hK,hmean⟩ := translated_metaplectic_mean hF hHB hε hεsmall
  let w : ℝ → ℝ := fun v => ‖mellin W ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)‖*(3+|v|)
  have hw : Integrable w := mellin_linear_weight_integrable W hW hpos hsm _
  refine ⟨K*(∫ v, w v),mul_nonneg hK.le (integral_nonneg (fun v => by dsimp [w]; positivity)),?_⟩
  intro r hr hs U hU T hT
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let Q : ℝ × ℝ → ℂ := fun p =>
    mellin W ((1/2+ε:ℝ)+(p.1:ℂ)*Complex.I)*
      (U:ℂ)^((1/2+ε:ℝ)+(p.1:ℂ)*Complex.I)*
      F r ((1/2+ε:ℝ)+((p.1-p.2):ℂ)*Complex.I)
  have hUn : (U:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
  have : NeZero (U:ℂ) := ⟨hUn⟩
  have hq : Continuous Q := by
    have hm := (smooth_mellin_entire W hW hpos hsm.continuous).continuous
    have hc := hF.continuous_line hr hs (by linarith)
      (by linarith : (1/2+ε:ℝ) ≠ 5/6)
    have hp := (differentiable_const_cpow_of_neZero (U:ℂ)).continuous
    have hcf : Continuous (fun p : ℝ × ℝ =>
        F r ((1/2+ε:ℝ)+((p.1-p.2):ℂ)*Complex.I)) := by
      simpa only [Function.comp_def,Pi.sub_apply,Complex.ofReal_sub] using
        hc.comp (continuous_fst.sub continuous_snd)
    exact ((hm.comp (by fun_prop)).mul (hp.comp (by fun_prop))).mul hcf
  have hnorm (v t : ℝ) : ‖Q (v,t)‖ =
      (‖mellin W ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)‖*U^(1/2+ε))*
        ‖F r ((1/2+ε:ℝ)+((v-t):ℂ)*Complex.I)‖ := by
    simp [Q,Complex.norm_cpow_eq_rpow_re_of_pos hU]
  let A : ℝ := U^(1/2+ε)*K*(norm r)^(1/4+2*ε)*Real.sqrt T*T
  have hR : 0 ≤ (norm r)^(1/4+2*ε) := Real.rpow_nonneg (norm_nonneg r) _
  have hb (v : ℝ) : (∫ t in -(2*T)..(2*T), ‖Q (v,t)‖) ≤ A*w v := by
    simp_rw [hnorm]
    rw [intervalIntegral.integral_const_mul]
    have hh := (div_le_iff₀ hTp).mp (hmean r hr hs T hT v)
    calc
      _ ≤ (‖mellin W ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)‖*U^(1/2+ε))*
          (K*(norm r)^(1/4+2*ε)*(3+|v|)*Real.sqrt T*T) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by dsimp [A,w]; ring
  have hint := integral_height_norm_le Q hq (show -(2*T) ≤ 2*T by linarith)
    (fun v => A*w v) (hw.const_mul A) hb
  rw [integral_const_mul] at hint
  apply (div_le_iff₀ hTp).mpr
  calc
    _ ≤ A*(∫ v, w v) := hint
    _ = _ := by dsimp [A]; ring

/-- The actual pole contribution has arbitrarily rapid height decay.
Its level factor is the proved residue bound, with no divisor loss. -/
theorem metaplectic_mellin_pole_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (D : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Eisenstein, primary r → ∀ U : ℝ, 0 < U → ∀ t : ℝ,
      ‖metaplecticResidue r*(U:ℂ)^((5/6:ℝ)+(t:ℂ)*Complex.I)*
        mellin W ((5/6:ℝ)+(t:ℂ)*Complex.I)‖ ≤
          C*U^(5/6:ℝ)*(norm r)^(-1/6:ℝ)/(1+|t|)^D := by
  obtain ⟨K,hK,hdecay⟩ := smooth_mellin_vertical_decay W hW hpos hsm (5/6) D
  refine ⟨|metaplecticA0| * K,by positivity,?_⟩
  intro r hr U hU t
  have hm : ‖mellin W ((5/6:ℝ)+(t:ℂ)*Complex.I)‖ ≤ K/(1+|t|)^D := by
    apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^D)).mpr
    simpa only [mul_comm] using hdecay t
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hU]
  norm_num only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  calc
    _ ≤ (|metaplecticA0| * norm r^(-1/6:ℝ))*U^(5/6:ℝ)*(K/(1+|t|)^D) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (norm_metaplecticResidue_le hr)
          (Real.rpow_nonneg hU.le _)) hm (_root_.norm_nonneg _)
        (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg r) _))
          (Real.rpow_nonneg hU.le _))
    _ = _ := by ring_nf

end CubicFirstMoment

end

end OAI
