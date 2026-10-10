import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHeight

namespace OAI

/-! Derivations of the integrated height bound from the metaplectic mean square. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

/-- Cauchy on a finite real interval, with the interval length explicit. -/
lemma continuous_interval_cauchy (f : ℝ → ℂ) (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖f t‖)^2 ≤ (b-a)*(∫ t in a..b, ‖f t‖^2) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hm : MemLp f 2 μ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
    (hf.norm.pow 2).integrableOn_Icc
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (show MemLp f (ENNReal.ofReal 2) μ by simpa using hm)
    (show MemLp (fun _ : ℝ => (1:ℂ)) (ENNReal.ofReal 2) μ by
      simpa using (memLp_const (μ := μ) (1:ℂ) (p := 2)))
  have hlen : ∫ _t, (1:ℝ) ∂μ = b-a := by
    simp [μ,hab]
  simp only [norm_one,mul_one,Real.rpow_two,one_pow] at h
  rw [hlen,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at h
  have hsq := pow_le_pow_left₀ (integral_nonneg (fun t => _root_.norm_nonneg (f t))) h 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
    Real.sq_sqrt (sub_nonneg.mpr hab)] at hsq
  simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,mul_comm] using hsq

/-- Translate the actual mean square to any frequency window before
integrating against the Mellin transform. -/
theorem translated_metaplectic_square {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ T : ℝ, 1 ≤ T → ∀ v : ℝ,
      (∫ t in -(2*T)..(2*T), ‖F r ((1/2+ε:ℝ)+((v-t):ℂ)*Complex.I)‖^2) ≤
        C*(norm r)^(1/2+4*ε)*(2*T+|v|+1)^2 := by
  obtain ⟨C,hC,hbound⟩ := hHB ε hε hεsmall
  refine ⟨C,hC,?_⟩
  intro r hr hs T hT v
  let M : ℝ := 2*T+|v|+1
  let f : ℝ → ℝ := fun t => ‖F r ((1/2+ε:ℝ)+(t:ℂ)*Complex.I)‖^2
  have hc : Continuous f := (hF.continuous_line hr hs (by linarith)
    (by linarith : (1/2+ε:ℝ) ≠ 5/6)).norm.pow 2
  have hM : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg v]
  have hleft : -M ≤ v-2*T := by dsimp [M]; linarith [neg_abs_le v]
  have hright : v-(-(2*T)) ≤ M := by dsimp [M]; linarith [le_abs_self v]
  simp_rw [← Complex.ofReal_sub]
  change (∫ t in -(2*T)..(2*T), f (v-t)) ≤ _
  rw [intervalIntegral.integral_comp_sub_left f v]
  exact (intervalIntegral.integral_mono_interval hleft (by linarith) hright
    (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hc.intervalIntegrable (-M) M)).trans
      (hbound r hr hs M hM)

/-- Averaged first moment on a translated height window. The complete
frequency dependence is retained for the subsequent Mellin integration. -/
theorem translated_metaplectic_mean {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ T : ℝ, 1 ≤ T → ∀ v : ℝ,
      (∫ t in -(2*T)..(2*T), ‖F r ((1/2+ε:ℝ)+((v-t):ℂ)*Complex.I)‖)/T ≤
        K*(norm r)^(1/4+2*ε)*(3+|v|)*Real.sqrt T := by
  obtain ⟨C,hC,hbound⟩ := translated_metaplectic_square hF hHB hε hεsmall
  refine ⟨2*Real.sqrt C,mul_pos (by norm_num) (Real.sqrt_pos.mpr hC),?_⟩
  intro r hr hs T hT v
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  let f : ℝ → ℂ := fun t => F r ((1/2+ε:ℝ)+((v-t):ℂ)*Complex.I)
  have hf : Continuous f := by
    simpa only [Function.comp_def,Pi.sub_apply,id_eq,f,Complex.ofReal_sub] using
      (hF.continuous_line hr hs (by linarith)
        (by linarith : (1/2+ε:ℝ) ≠ 5/6)).comp
          ((continuous_const : Continuous (fun _ : ℝ => v)).sub continuous_id)
  have hc := continuous_interval_cauchy f hf (show -(2*T) ≤ 2*T by linarith)
  have hsquare := hbound r hr hs T hT v
  have hfreq : 2*T+|v|+1 ≤ (3+|v|)*T := by
    nlinarith [mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hT)]
  have hpow : (norm r)^(1/2+4*ε) = ((norm r)^(1/4+2*ε))^2 := by
    rw [← Real.rpow_mul_natCast hR.le]
    congr 1
    ring
  have hi0 : 0 ≤ ∫ t in -(2*T)..(2*T), ‖f t‖ :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => _root_.norm_nonneg _)
  have hsq : (∫ t in -(2*T)..(2*T), ‖f t‖)^2 ≤
      (2*Real.sqrt C*(norm r)^(1/4+2*ε)*(3+|v|)*Real.sqrt T*T)^2 := by
    calc
      _ ≤ (4*T)*(C*(norm r)^(1/2+4*ε)*(2*T+|v|+1)^2) := by
        apply hc.trans
        convert mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 4*T by positivity) using 1
        ring
      _ ≤ (4*T)*(C*(norm r)^(1/2+4*ε)*((3+|v|)*T)^2) := by
        gcongr
      _ = _ := by
        rw [hpow]
        simp only [mul_pow,Real.sq_sqrt hC.le,Real.sq_sqrt hTp.le]
        ring
  apply (div_le_iff₀ hTp).mpr
  exact (sq_le_sq₀ hi0 (by positivity)).mp hsq

end CubicFirstMoment

end

end OAI
