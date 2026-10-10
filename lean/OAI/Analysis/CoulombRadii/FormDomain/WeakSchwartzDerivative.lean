import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
section
end
end
section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology SchwartzMap LineDeriv FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma compact_mul_memLp_integrable (f:E → ℂ) (hf:Continuous f)
    (hc:HasCompactSupport f) (u:E → ℂ) (hu:MemLp u 2 volume) :
    Integrable (fun x => f x*u x) :=
  (hf.memLp_of_hasCompactSupport hc (p:=2)).integrable_mul hu
private lemma compact_complex_integral_decompose (f:E → ℂ) (hf:Continuous f)
    (hc:HasCompactSupport f) (u:E → ℂ) (hu:MemLp u 2 volume) :
    (∫ x,f x*u x)=(∫ x,((f x).re:ℂ)*u x)+Complex.I*(∫ x,((f x).im:ℂ)*u x) := by
  have hr := compact_mul_memLp_integrable _
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hf))
    (hc.comp_left (g:= fun z:ℂ => (z.re:ℂ)) (by simp)) u hu
  have hi := compact_mul_memLp_integrable _
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hf))
    (hc.comp_left (g:= fun z:ℂ => (z.im:ℂ)) (by simp)) u hu
  have he (x:E) : f x*u x=((f x).re:ℂ)*u x+Complex.I*(((f x).im:ℂ)*u x) := by
    conv_lhs => rw [←(f x).re_add_im]
    ring
  simp_rw [he]
  change Integrable (fun x => ((f x).re:ℂ)*u x) at hr
  change Integrable (fun x => ((f x).im:ℂ)*u x) at hi
  rw [integral_add hr (hi.const_mul _),integral_const_mul]

lemma weak_directional_complex_test {u d : E → ℂ} (hu : MemLp u 2 volume)
    (hd : MemLp d 2 volume) (a : E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x))
    (φ : E → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x,fderiv ℝ φ x a*u x)=-(∫ x,φ x*d x) := by
  have hr := hw (fun x => (φ x).re) (Complex.reCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hi := hw (fun x => (φ x).im) (Complex.imCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hdr (x:E) : fderiv ℝ (fun y => (φ y).re) x a=(fderiv ℝ φ x a).re := by
    exact congrArg (fun L:E →L[ℝ] ℝ => L a) ((Complex.reCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hdi (x:E) : fderiv ℝ (fun y => (φ y).im) x a=(fderiv ℝ φ x a).im := by
    exact congrArg (fun L:E →L[ℝ] ℝ => L a) ((Complex.imCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hD : Continuous (fun x => fderiv ℝ φ x a) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [compact_complex_integral_decompose _ hD (hc.fderiv_apply ℝ a) u hu,
    compact_complex_integral_decompose _ hφ.continuous hc d hd]
  simp only [hdr] at hr
  simp only [hdi] at hi
  rw [hr,hi]
  ring

section
omit [MeasurableSpace E] [BorelSpace E]

private def weakCutBump : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩
private def weakCut (k:ℕ) (x:E) : ℝ := (weakCutBump (E:=E)) (((k:ℝ)+1)⁻¹ • x)
private lemma weakCut_smooth (k:ℕ) : ContDiff ℝ ∞ (weakCut (E:=E) k) :=
  (weakCutBump (E:=E)).contDiff.comp (contDiff_const.smul contDiff_id)
private lemma weakCut_compact (k:ℕ) : HasCompactSupport (weakCut (E:=E) k) := by
  exact (weakCutBump (E:=E)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smul (Units.mk0 (((k:ℝ)+1)⁻¹) (by positivity)))
private lemma weakCut_fderiv (k:ℕ) (x a:E) :
    fderiv ℝ (weakCut k) x a=((k:ℝ)+1)⁻¹*fderiv ℝ (weakCutBump (E:=E)) (((k:ℝ)+1)⁻¹ • x) a := by
  have h := (((weakCutBump (E:=E)).contDiff (n:=⊤)).differentiable (by simp) _).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).const_smul (((k:ℝ)+1)⁻¹))
  have HH := congrArg (fun L:E →L[ℝ] ℝ => L a) h.fderiv
  unfold weakCut
  simpa only [Function.comp_def,Pi.smul_apply,id_eq,ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul] using HH
private lemma weakCut_bound : ∃ C:ℝ,0 ≤ C ∧ ∀ k x a,
    |fderiv ℝ (weakCut (E:=E) k) x a| ≤ ((k:ℝ)+1)⁻¹*C*‖a‖ := by
  obtain ⟨C,hC⟩ := (((weakCutBump (E:=E)).contDiff (n:=⊤)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((weakCutBump (E:=E)).hasCompactSupport.fderiv ℝ)
  refine ⟨C,(norm_nonneg _).trans (hC 0),?_⟩
  intro k x a
  rw [weakCut_fderiv,abs_mul,abs_of_pos (by positivity : (0:ℝ)<((k:ℝ)+1)⁻¹)]
  calc
    _ ≤ ((k:ℝ)+1)⁻¹*(C*‖a‖) := mul_le_mul_of_nonneg_left
      (((fderiv ℝ (weakCutBump (E:=E)) _).le_opNorm a).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))) (by positivity)
    _ = _ := by ring
private lemma weakCut_tendsto (x:E) : Tendsto (fun k => weakCut k x) atTop (𝓝 1) := by
  have ht : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹ • x) atTop (𝓝 (0:E)) := by
    have hi : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using hi.smul_const x
  have H := ((weakCutBump (E:=E)).continuous.tendsto (0:E)).comp ht
  have h1 : (weakCutBump (E:=E)) (0:E)=1 :=
    (weakCutBump (E:=E)).one_of_mem_closedBall (by simp [weakCutBump])
  simpa only [weakCut,Function.comp_def,h1] using H

end

lemma weak_directional_schwartz_test {u d : E → ℂ} (hu : MemLp u 2 volume)
    (hd : MemLp d 2 volume) (a : E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x))
    (Φ : 𝓢(E,ℂ)) :
    (∫ x,(∂_{a} Φ) x*u x)=-(∫ x,Φ x*d x) := by
  obtain ⟨C,hC,hb⟩ := weakCut_bound (E:=E)
  have hinv (k:ℕ) : ((k:ℝ)+1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
  have hi0 : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hdt (x:E) : Tendsto (fun k => fderiv ℝ (weakCut k) x a) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => hb k x a)
    simpa using (hi0.mul_const C).mul_const ‖a‖
  have hc0 (k:ℕ) (x:E) : 0 ≤ weakCut k x := (weakCutBump (E:=E)).nonneg
  have hc1 (k:ℕ) (x:E) : weakCut k x ≤ 1 := (weakCutBump (E:=E)).le_one
  let F : ℕ → E → ℂ := fun k x =>
    ((fderiv ℝ (weakCut k) x a:ℂ)*Φ x+(weakCut k x:ℂ)*(∂_{a} Φ) x)*u x
  let G : ℕ → E → ℂ := fun k x => (weakCut k x:ℂ)*Φ x*d x
  have he (k:ℕ) : (∫ x,F k x)=-(∫ x,G k x) := by
    let φ : E → ℂ := fun x => (weakCut k x:ℂ)*Φ x
    have hφ : ContDiff ℝ ∞ φ :=
      (Complex.ofRealCLM.contDiff.comp (weakCut_smooth k)).mul (Φ.smooth ⊤)
    have hf (x:E) : fderiv ℝ φ x a =
        (fderiv ℝ (weakCut k) x a:ℂ)*Φ x+(weakCut k x:ℂ)*(∂_{a} Φ) x := by
      have H := (((Complex.ofRealCLM.hasFDerivAt.comp x
        ((weakCut_smooth k).differentiable (by simp) x).hasFDerivAt)).mul (Φ.hasFDerivAt x)).fderiv
      have HH := congrArg (fun L:E →L[ℝ] ℂ => L a) H
      have HH2 : fderiv ℝ φ x a = (weakCut k x:ℂ)*fderiv ℝ Φ x a+Φ x*(fderiv ℝ (weakCut k) x a:ℂ) := by
        simpa only [φ,Pi.mul_def,Pi.mul_apply,Function.comp_def,add_apply,smul_apply,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,smul_eq_mul] using HH
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,HH2]
      ring
    have H := weak_directional_complex_test hu hd a hw φ hφ
      (((weakCut_compact k).comp_left (by simp : ((0:ℝ):ℂ)=0)).mul_right)
    simpa only [hf,φ,F,G] using H
  have hφu : Integrable (fun x => ‖Φ x‖*‖u x‖) :=
    ((Φ.memLp 2 volume).norm).integrable_mul hu.norm
  have hdu : Integrable (fun x => ‖(∂_{a} Φ) x‖*‖u x‖) :=
    (((∂_{a} Φ).memLp 2 volume).norm).integrable_mul hu.norm
  have hφd : Integrable (fun x => ‖Φ x‖*‖d x‖) :=
    ((Φ.memLp 2 volume).norm).integrable_mul hd.norm
  have hFm (k:ℕ) : AEStronglyMeasurable (F k) volume := by
    exact (((Complex.continuous_ofReal.comp
      (((weakCut_smooth k).continuous_fderiv (by simp)).clm_apply (continuous_const (y:=a)))).mul Φ.continuous).add
      ((Complex.continuous_ofReal.comp (weakCut_smooth k).continuous).mul
        (∂_{a} Φ).continuous)).aestronglyMeasurable.mul hu.aestronglyMeasurable
  have hF : Tendsto (fun k => ∫ x,F k x) atTop (𝓝 (∫ x,(∂_{a} Φ) x*u x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => C*‖a‖*(‖Φ x‖*‖u x‖)+‖(∂_{a} Φ) x‖*‖u x‖)
      hFm ((hφu.const_mul _).add hdu)
    · intro k
      filter_upwards [] with x
      dsimp [F]
      rw [norm_mul]
      have H1 : ‖(fderiv ℝ (weakCut k) x a:ℂ)‖ ≤ C*‖a‖ := by
        rw [Complex.norm_real,Real.norm_eq_abs]
        exact (hb k x a).trans (by nlinarith [mul_nonneg hC (norm_nonneg a),hinv k])
      have H2 : ‖(weakCut k x:ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc0 k x)] using hc1 k x
      calc
        _ ≤ (‖(fderiv ℝ (weakCut k) x a:ℂ)‖*‖Φ x‖+
          ‖(weakCut k x:ℂ)‖*‖(∂_{a} Φ) x‖)*‖u x‖ := by
          have HH := norm_add_le ((fderiv ℝ (weakCut k) x a:ℂ)*Φ x) ((weakCut k x:ℂ)*(∂_{a} Φ) x)
          simpa only [norm_mul] using mul_le_mul_of_nonneg_right HH (norm_nonneg (u x))
        _ ≤ (C*‖a‖*‖Φ x‖+1*‖(∂_{a} Φ) x‖)*‖u x‖ :=
          mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right H1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right H2 (norm_nonneg _))) (norm_nonneg _)
        _ = _ := by ring
    · filter_upwards [] with x
      have H := (((Complex.continuous_ofReal.tendsto 0).comp (hdt x)).mul_const (Φ x)).add
        (((Complex.continuous_ofReal.tendsto 1).comp (weakCut_tendsto x)).mul_const ((∂_{a} Φ) x))
      simpa only [F,Complex.ofReal_zero,zero_mul,Complex.ofReal_one,one_mul,zero_add,Function.comp_apply] using H.mul_const (u x)
  have hG : Tendsto (fun k => ∫ x,G k x) atTop (𝓝 (∫ x,Φ x*d x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖Φ x‖*‖d x‖)
      (fun k => (((Complex.continuous_ofReal.comp (weakCut_smooth k).continuous).mul
        Φ.continuous).aestronglyMeasurable.mul hd.aestronglyMeasurable)) hφd
    · intro k
      filter_upwards [] with x
      dsimp [G]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc0 k x)]
      nlinarith [hc1 k x,norm_nonneg (Φ x),norm_nonneg (d x),mul_nonneg (norm_nonneg (Φ x)) (norm_nonneg (d x))]
    · filter_upwards [] with x
      simpa only [G,Complex.ofReal_one,one_mul,Function.comp_apply,Pi.mul_apply] using
        (((Complex.continuous_ofReal.tendsto 1).comp (weakCut_tendsto x)).mul_const (Φ x)).mul_const (d x)
  exact tendsto_nhds_unique hF (by simpa only [he] using hG.neg)

lemma l2_weakDeriv_tempered {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    ∂_{a} (u:𝓢'(E,ℂ))=(d:𝓢'(E,ℂ)) := by
  ext Φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,map_neg,Lp.toTemperedDistribution_apply,smul_eq_mul]
  have H := weak_directional_schwartz_test (Lp.memLp u) (Lp.memLp d) a hw Φ
  simpa only [neg_neg] using congrArg Neg.neg H
end Coulomb
end

end

end OAI
