import OAI.NumberTheory.CubicMoment.Estimates.TypeICompleted
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! Uniform Type-I height bounds over a smooth family. Uniformity comes
from the proved support/derivative-to-Mellin estimates. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem uniform_metaplectic_mellin_height_mean {ι : Type*} {W : ι → ℝ → ℂ}
    (hW : UniformLogWeights W) {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i r, primary r → Squarefree r →
      ∀ U : ℝ, 0 < U → ∀ T : ℝ, 1 ≤ T →
      (∫ t in -(2*T)..(2*T), ‖∫ v : ℝ,
        mellin (W i) ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)*
          (U:ℂ)^((1/2+ε:ℝ)+(v:ℂ)*Complex.I)*
          F r ((1/2+ε:ℝ)+((v-t):ℂ)*Complex.I)‖)/T ≤
        C*U^(1/2+ε)*(norm r)^(1/4+2*ε)*Real.sqrt T := by
  obtain ⟨K,hK,hmean⟩ := translated_metaplectic_mean hF hHB hε hεsmall
  obtain ⟨L,hLn,hL⟩ := hW.mellin_linear_integral (1/2+ε)
  have hLa : |(1/2+ε:ℝ)| ≤ 1/2+ε := abs_le.mpr ⟨by linarith,le_refl _⟩
  have hL' (i : ι) : (∫ v : ℝ,
      ‖mellin (W i) ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)‖*(3+|v|)) ≤ L :=
    hL i (1/2+ε) hLa
  refine ⟨K*L,mul_nonneg hK.le hLn,?_⟩
  intro i r hr hs U hU T hT
  let w : ℝ → ℝ := fun v => ‖mellin (W i) ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)‖*(3+|v|)
  have hw : Integrable w := mellin_linear_weight_integrable (W i) (hW.compact i) (hW.positive i) (hW.smooth i) _
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let Q : ℝ × ℝ → ℂ := fun p =>
    mellin (W i) ((1/2+ε:ℝ)+(p.1:ℂ)*Complex.I)*
      (U:ℂ)^((1/2+ε:ℝ)+(p.1:ℂ)*Complex.I)*
      F r ((1/2+ε:ℝ)+((p.1-p.2):ℂ)*Complex.I)
  have hUn : (U:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
  have : NeZero (U:ℂ) := ⟨hUn⟩
  have hq : Continuous Q := by
    have hm := (smooth_mellin_entire (W i) (hW.compact i) (hW.positive i) (hW.smooth i).continuous).continuous
    have hc := hF.continuous_line hr hs (by linarith)
      (by linarith : (1/2+ε:ℝ) ≠ 5/6)
    have hp := (differentiable_const_cpow_of_neZero (U:ℂ)).continuous
    have hcf : Continuous (fun p : ℝ × ℝ =>
        F r ((1/2+ε:ℝ)+((p.1-p.2):ℂ)*Complex.I)) := by
      simpa only [Function.comp_def,Pi.sub_apply,Complex.ofReal_sub] using
        hc.comp (continuous_fst.sub continuous_snd)
    exact ((hm.comp (by fun_prop)).mul (hp.comp (by fun_prop))).mul hcf
  have hnorm (v t : ℝ) : ‖Q (v,t)‖ =
      (‖mellin (W i) ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)‖*U^(1/2+ε))*
        ‖F r ((1/2+ε:ℝ)+((v-t):ℂ)*Complex.I)‖ := by
    simp [Q,Complex.norm_cpow_eq_rpow_re_of_pos hU]
  let A : ℝ := U^(1/2+ε)*K*(norm r)^(1/4+2*ε)*Real.sqrt T*T
  have hR : 0 ≤ (norm r)^(1/4+2*ε) := Real.rpow_nonneg (norm_nonneg r) _
  have hb (v : ℝ) : (∫ t in -(2*T)..(2*T), ‖Q (v,t)‖) ≤ A*w v := by
    simp_rw [hnorm]
    rw [intervalIntegral.integral_const_mul]
    have hh := (div_le_iff₀ hTp).mp (hmean r hr hs T hT v)
    calc
      _ ≤ (‖mellin (W i) ((1/2+ε:ℝ)+(v:ℂ)*Complex.I)‖*U^(1/2+ε))*
          (K*(norm r)^(1/4+2*ε)*(3+|v|)*Real.sqrt T*T) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by dsimp [A,w]; ring
  have hint := integral_height_norm_le Q hq (show -(2*T) ≤ 2*T by linarith)
    (fun v => A*w v) (hw.const_mul A) hb
  rw [integral_const_mul] at hint
  apply (div_le_iff₀ hTp).mpr
  calc
    _ ≤ A*(∫ v, w v) := hint
    _ ≤ A*L := mul_le_mul_of_nonneg_left (hL' i)
      (by dsimp [A]; positivity)
    _ = _ := by dsimp [A]; ring

/-- Uniform rapid decay of the residue across the same weight family. -/
theorem uniform_metaplectic_mellin_pole_decay {ι : Type*} {W : ι → ℝ → ℂ}
    (hW : UniformLogWeights W) (D : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i r, primary r → ∀ U : ℝ, 0 < U → ∀ t : ℝ,
      ‖metaplecticResidue r*(U:ℂ)^((5/6:ℝ)+(t:ℂ)*Complex.I)*
        mellin (W i) ((5/6:ℝ)+(t:ℂ)*Complex.I)‖ ≤
          C*U^(5/6:ℝ)*(norm r)^(-1/6:ℝ)/(1+|t|)^D := by
  obtain ⟨K,hK,hdecay⟩ := hW.mellin_decay (5/6) D
  refine ⟨|metaplecticA0| *K,by positivity,?_⟩
  intro i r hr U hU t
  have hm : ‖mellin (W i) ((5/6:ℝ)+(t:ℂ)*Complex.I)‖ ≤ K/(1+|t|)^D := by
    apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^D)).mpr
    simpa only [mul_comm] using hdecay i (5/6) (by norm_num) t
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


/-- The uniform original-sum height estimate. -/
theorem uniform_metaplectic_dyadic_height {ι : Type*} {W : ι → ℝ → ℂ}
    (hW : UniformLogWeights W) {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12) (D : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ i r, primary r → Squarefree r →
      ∀ U : ℝ, 1 ≤ U → ∀ T : ℝ, 1 ≤ T →
      ((∫ t in T..2*T, ‖metaplecticSmoothSum r (W i) U t‖)+
       (∫ t in -(2*T)..(-T), ‖metaplecticSmoothSum r (W i) U t‖))/T ≤
        C*U^(1/2+ε)*norm r^(1/4+2*ε)*Real.sqrt T+
        E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  obtain ⟨C,hC,hmean⟩ := uniform_metaplectic_mellin_height_mean hW hF hHB hε hεsmall
  obtain ⟨E,hE,hpole⟩ := uniform_metaplectic_mellin_pole_decay hW D
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  have hc : c ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact one_div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  refine ⟨2*‖c‖*C,2*E,by positivity,by positivity,?_⟩
  intro i r hr hs U hU T hT
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let I : ℝ → ℂ := fun t => ∫ v : ℝ,
    mellin (W i) (((1/2+ε:ℝ):ℂ)+(v:ℂ)*Complex.I)*
      (U:ℂ)^(((1/2+ε:ℝ):ℂ)+(v:ℂ)*Complex.I)*
      F r (((1/2+ε:ℝ):ℂ)+((v-t):ℂ)*Complex.I)
  let P : ℝ → ℂ := fun t => metaplecticResidue r*
    (U:ℂ)^((5/6:ℝ)+(t:ℂ)*Complex.I)*mellin (W i) ((5/6:ℝ)+(t:ℂ)*Complex.I)
  have he (t : ℝ) : metaplecticSmoothSum r (W i) U t = c*I t+P t :=
    metaplectic_smooth_shift_of_polynomial hF hr hs (by linarith) (by linarith)
      (hGrowth r hr hs ε hε)
      (W i) (hW.compact i) (hW.positive i) (hW.smooth i) hU t
  have : NeZero (U:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hUp.ne'⟩
  have hPc : Continuous P := by
    have hm := (smooth_mellin_entire (W i) (hW.compact i) (hW.positive i) (hW.smooth i).continuous).continuous
    have hu := (differentiable_const_cpow_of_neZero (U:ℂ)).continuous
    exact (continuous_const.mul (hu.comp (by fun_prop))).mul (hm.comp (by fun_prop))
  have hIc : Continuous I := by
    have hi (t : ℝ) : I t = c⁻¹*(metaplecticSmoothSum r (W i) U t-P t) := by
      rw [he t,add_sub_cancel_right,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
    exact (continuous_const.mul ((metaplecticSmoothSum_continuous r (W i) (hW.compact i) hUp).sub hPc)).congr
      (fun t => (hi t).symm)
  let H : ℝ := E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D
  have hrn : 0 ≤ norm r := norm_nonneg r
  have hpb (t : ℝ) (ht : T ≤ |t|) : ‖P t‖ ≤ H := by
    apply (hpole i r hr U hUp t).trans
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hTp D)
      (pow_le_pow_left₀ hTp.le (by linarith [abs_nonneg t]) D)
  have hm : (∫ t in -(2*T)..(2*T), ‖I t‖)/T ≤
      C*U^(1/2+ε)*norm r^(1/4+2*ε)*Real.sqrt T := hmean i r hr hs U hUp T hT
  have hd := dyadic_decomposition_mean (metaplecticSmoothSum r (W i) U) I P c hIc hPc he hTp hpb
  apply hd.trans
  calc
    _ ≤ 2*‖c‖*(C*U^(1/2+ε)*norm r^(1/4+2*ε)*Real.sqrt T)+2*H := by
      exact add_le_add (mul_le_mul_of_nonneg_left hm
        (mul_nonneg (by norm_num) (_root_.norm_nonneg c))) le_rfl
    _ = _ := by dsimp [H]; ring


end CubicFirstMoment

end

end OAI
