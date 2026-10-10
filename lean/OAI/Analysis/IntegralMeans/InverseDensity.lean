import OAI.Analysis.IntegralMeans.ExpectedDensity

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

def affineInverse (z : ℂ) : ℂ := (-(z.re : ℂ)+Complex.I)/(z.im : ℂ)

lemma affineInverse_re (z : ℂ) : (affineInverse z).re = -z.re/z.im := by
  simp [affineInverse,Complex.div_ofReal_re]

lemma affineInverse_im (z : ℂ) : (affineInverse z).im = z.im⁻¹ := by
  simp [affineInverse,Complex.div_ofReal_im]

lemma affineInverse_mem {z : ℂ} (hz : z ∈ halfPlane) : affineInverse z ∈ halfPlane := by
  simpa only [halfPlane,mem_ofPred_eq,affineInverse_im] using inv_pos.mpr hz

lemma affineInverse_invol {z : ℂ} (hz : z ∈ halfPlane) : affineInverse (affineInverse z) = z := by
  have hn : z.im ≠ 0 := ne_of_gt hz
  apply Complex.ext
  · simp only [affineInverse_re,affineInverse_im,neg_div,neg_neg,div_inv_eq_mul]
    exact div_mul_cancel₀ _ hn
  · simp only [affineInverse_im,inv_inv]

lemma affineInverse_injOn : InjOn affineInverse halfPlane := by
  intro z hz w hw he
  simpa only [affineInverse_invol hz,affineInverse_invol hw] using congrArg affineInverse he

lemma affineInverse_affine {z : ℂ} (hz : z ∈ halfPlane) : affine z (affineInverse z) = Complex.I := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [affine,affineInverse,mul_div_cancel₀ _ hn]
  ring

lemma hasFDerivAt_affineInverse {z : ℂ} (hz : z ∈ halfPlane) :
    HasFDerivAt affineInverse
      (((z.im : ℂ)⁻¹) • (-(Complex.ofRealCLM.comp Complex.reCLM)) +
        (-(z.re : ℂ)+Complex.I) •
          ((-((z.im : ℂ)^2)⁻¹) • (Complex.ofRealCLM.comp Complex.imCLM))) z := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hn).comp z
    (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt
  have h := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt.neg.add_const Complex.I).mul hi
  convert! h using 1
  ext v
  simp only [add_apply,smul_apply,neg_apply,Pi.neg_apply,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    ContinuousLinearMap.mulLeftRight_apply,Function.comp_apply,smul_eq_mul]
  ring

lemma differentiableAt_affineInverse {z : ℂ} (hz : z ∈ halfPlane) : DifferentiableAt ℝ affineInverse z :=
  (hasFDerivAt_affineInverse hz).differentiableAt

lemma fderiv_affineInverse_apply {z : ℂ} (hz : z ∈ halfPlane) (v : ℂ) :
    fderiv ℝ affineInverse z v =
      (-(v.re : ℂ)*(z.im : ℂ)-(-(z.re : ℂ)+Complex.I)*(v.im : ℂ))/(z.im : ℂ)^2 := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [(hasFDerivAt_affineInverse hz).fderiv]
  simp only [add_apply,smul_apply,neg_apply,
    ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    smul_eq_mul]
  field_simp
  ring

lemma det_affineInverse {z : ℂ} (hz : z ∈ halfPlane) :
    (fderiv ℝ affineInverse z).det = z.im⁻¹^3 := by
  change LinearMap.det (fderiv ℝ affineInverse z).toLinearMap = _
  rw [determinant_complex_real]
  change (fderiv ℝ affineInverse z 1).re*(fderiv ℝ affineInverse z Complex.I).im-
    (fderiv ℝ affineInverse z Complex.I).re*(fderiv ℝ affineInverse z 1).im = _
  rw [fderiv_affineInverse_apply hz,fderiv_affineInverse_apply hz]
  simp only [Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,Complex.ofReal_one,
    Complex.ofReal_zero,neg_zero,zero_mul,mul_zero,mul_one,sub_zero,zero_sub,neg_mul,
    ← Complex.ofReal_pow,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring

lemma affineInverse_change_variables {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ halfPlane)
    (hInv : affineInverse '' s = s) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in s, f z ∂volume) = ∫⁻ z in s, ENNReal.ofReal (z.im⁻¹^3)*f (affineInverse z) ∂volume := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (differentiableAt_affineInverse (hsub hz)).hasFDerivAt.hasFDerivWithinAt)
    (affineInverse_injOn.mono hsub) f
  rw [hInv] at h
  refine h.trans (setLIntegral_congr_fun hs (fun z hz => ?_))
  rw [det_affineInverse (hsub hz),abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hsub hz).le) _)]

lemma diskCayley_affineInverse {z : ℂ} (hz : z ∈ halfPlane) :
    diskCayley (affineInverse z) = (z-Complex.I)/(star (z+Complex.I)) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have h₁ : affineInverse z-Complex.I = -(z-Complex.I)/(z.im : ℂ) := by
    rw [affineInverse,div_sub' hy]
    congr 1
    apply Complex.ext <;> simp
  have h₂ : affineInverse z+Complex.I = -star (z+Complex.I)/(z.im : ℂ) := by
    rw [affineInverse,div_add' _ _ _ hy]
    congr 1
    apply Complex.ext <;> simp
  rw [diskCayley,h₁,h₂,div_div_div_cancel_right₀ hy,neg_div_neg_eq]

lemma diskCayley_affineInverse_norm {z : ℂ} (hz : z ∈ halfPlane) :
    ‖diskCayley (affineInverse z)‖ = ‖diskCayley z‖ := by
  rw [diskCayley_affineInverse hz,diskCayley,norm_div,norm_div,norm_star]

lemma affineInverse_mem_outsideCore {z : ℂ} (hz : z ∈ outsideCore) : affineInverse z ∈ outsideCore :=
  ⟨affineInverse_mem hz.1,by simpa only [diskCayley_affineInverse_norm hz.1] using hz.2⟩

lemma affineInverse_image_outsideCore : affineInverse '' outsideCore = outsideCore := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact affineInverse_mem_outsideCore hw
  · intro hz
    exact ⟨affineInverse z,affineInverse_mem_outsideCore hz,affineInverse_invol hz.1⟩

lemma reroot_at_affineInverse (g : DiskClass) {z : ℂ} (hz : z ∈ halfPlane) :
    classFun (rerootClass g ⟨z,hz⟩) (affineInverse z) =
      -classFun g z/((z.im : ℂ)*deriv (classFun g) z) := by
  rw [classFun_rerootClass g ⟨z,hz⟩ (affineInverse_mem hz)]
  simp only [reroot,affineInverse_affine hz,(classFun_schlicht g).2.1,zero_sub]

lemma classWeight_inverse_value (g : DiskClass) {z : ℂ} (hz : z ∈ outsideCore) :
    classWeight g ⟨z,hz.1⟩ *
      ‖classFun (rerootClass g ⟨z,hz.1⟩) (affineInverse z)‖⁻¹^4 =
    z.im^4*(‖deriv (classFun g) z‖^2*‖classFun g z‖⁻¹^4) := by
  have hn := classFun_ne_zero_outsideCore g hz
  have hd := univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz.1
  have hy : 0 < z.im := hz.1
  rw [classWeight,reciprocalDeriv,reroot_at_affineInverse g hz.1]
  simp only [norm_inv,norm_div,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
  field_simp

lemma inverse_area_bound {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z) (hi : InjOn f s)
    (hmin : ∀ z ∈ s, (1/16 : ℝ) ≤ ‖f z‖) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖^2*‖f z‖⁻¹^4)) ≤
      ENNReal.ofReal (256*Real.pi) := by
  have hn (z : ℂ) (hz : z ∈ s) : f z ≠ 0 := by
    have := hmin z hz
    exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
  have hd (z : ℂ) (hz : z ∈ s) := (hf z hz).hasDerivAt.inv (hn z hz)
  have hhi : InjOn (fun z => (f z)⁻¹) s := by
    intro z hz w hw he
    exact hi hz hw (inv_inj.mp he)
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hhi (fun _ => (1 : ℝ≥0∞))
  have hJac (z : ℂ) (hz : z ∈ s) :
      |(fderiv ℝ (fun z => (f z)⁻¹) z).det| = ‖deriv f z‖^2*‖f z‖⁻¹^4 := by
    have hdet : (fderiv ℝ (fun z => (f z)⁻¹) z).det = ‖deriv (fun z => (f z)⁻¹) z‖^2 := by
      exact det_fderiv_complex (hd z hz).differentiableAt
    rw [hdet,abs_of_nonneg (sq_nonneg _)]
    have hdr : deriv (fun z => (f z)⁻¹) z = -deriv f z/f z^2 := (hd z hz).deriv
    rw [hdr]
    change ‖(-deriv f z/f z^2 : ℂ)‖^2 = ‖deriv f z‖^2*‖f z‖⁻¹^4
    rw [Complex.norm_div,norm_neg,Complex.norm_pow]
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have he' : (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖^2*‖f z‖⁻¹^4)) =
      volume ((fun z => (f z)⁻¹) '' s) := by
    simp only [lintegral_const,one_mul,Measure.restrict_apply_univ] at he
    change _ = volume (f⁻¹ '' s)
    rw [he]
    apply setLIntegral_congr_fun hs
    intro z hz
    dsimp only
    rw [mul_one]
    have hfm := (hd z hz).hasFDerivAt.restrictScalars ℝ
    have hh : (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-deriv f z/f z^2))) =
        fderiv ℝ (fun z => (f z)⁻¹) z := by
      exact hfm.fderiv.symm
    rw [hh,hJac z hz]
  rw [he']
  have hsub : (fun z => (f z)⁻¹) '' s ⊆ Metric.closedBall 0 16 := by
    rintro _ ⟨z,hz,rfl⟩
    simp only [Metric.mem_closedBall,dist_zero_right,norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr (hn z hz)) (by norm_num)).mpr (by simpa using hmin z hz)
  calc
    _ ≤ volume (Metric.closedBall (0 : ℂ) 16) := measure_mono hsub
    _ = _ := by
      rw [Complex.volume_closedBall]
      have hp : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
        rw [ENNReal.ofReal,ENNReal.coe_inj]
        apply Subtype.ext
        exact (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
      rw [hp,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256)]
      norm_num [mul_comm]

def planeClassDeriv (g : DiskClass) (z : ℂ) : ℂ :=
  by classical exact if z ∈ halfPlane then deriv (classFun g) z else 0

lemma measurable_planeClassDeriv : Measurable (fun p : DiskClass × ℂ => planeClassDeriv p.1 p.2) := by
  classical
  let s : Set (DiskClass × ℂ) := Prod.snd ⁻¹' halfPlane
  have hc : Continuous (fun p : s => deriv (classFun p.val.1) p.val.2) := by
    have h : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
      simpa only [iteratedDeriv_one] using continuous_classJet_eval 1
    exact h.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [planeClassDeriv,s,Set.mem_preimage,dite_eq_ite] using
    hc.measurable.dite (measurable_const (a := (0 : ℂ)))
      (isOpen_halfPlane.measurableSet.preimage measurable_snd)

lemma planeClassDeriv_eq (g : DiskClass) {z : ℂ} (hz : z ∈ halfPlane) :
    planeClassDeriv g z = deriv (classFun g) z := by simp [planeClassDeriv,hz]

def inverseDensity (g : DiskClass) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖planeClassValue g z‖⁻¹^4)

def inverseJacDensity (g : DiskClass) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖planeClassDeriv g z‖^2*‖planeClassValue g z‖⁻¹^4)

def weightedInverseArea (β : ℝ) (g : DiskClass) : ℝ≥0∞ :=
  ∫⁻ z in outsideCore, ENNReal.ofReal (z.im^(β+1))*inverseDensity g z

lemma measurable_inverseDensity : Measurable (Function.uncurry inverseDensity) :=
  (measurable_planeClassValue.norm.inv.pow_const 4).ennreal_ofReal

lemma measurable_inverseJacDensity : Measurable (Function.uncurry inverseJacDensity) :=
  ((measurable_planeClassDeriv.norm.pow_const 2).mul
    (measurable_planeClassValue.norm.inv.pow_const 4)).ennreal_ofReal

lemma measurable_weightedInverseArea (β : ℝ) : Measurable (weightedInverseArea β) := by
  apply Measurable.lintegral_prod_right
  exact (((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
    measurable_inverseDensity

lemma inverseJacDensity_integral_le (g : DiskClass) :
    (∫⁻ z in outsideCore, inverseJacDensity g z) ≤ ENNReal.ofReal (256*Real.pi) := by
  have he : (∫⁻ z in outsideCore, inverseJacDensity g z) =
      ∫⁻ z in outsideCore, ENNReal.ofReal (‖deriv (classFun g) z‖^2*‖classFun g z‖⁻¹^4) := by
    apply setLIntegral_congr_fun measurableSet_outsideCore
    intro z hz
    simp only [inverseJacDensity,planeClassValue_eq g hz.1,planeClassDeriv_eq g hz.1]
  rw [he]
  exact inverse_area_bound measurableSet_outsideCore
    (fun _ hz => (classFun_schlicht g).1.1.differentiableAt (isOpen_halfPlane.mem_nhds hz.1))
    ((classFun_schlicht g).1.2.mono (fun _ h => h.1))
    (fun _ hz => classFun_lower_outsideCore g hz)

def HasWeightedLaw (P : ProbabilityMeasure DiskClass) (β : ℝ) : Prop :=
  ∀ z : halfPlane, ∀ f : DiskClass → ℝ≥0∞, Measurable f →
    (∫⁻ g, ENNReal.ofReal (classWeight g z)*f (rerootClass g z) ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g, f g ∂(P : Measure DiskClass))

attribute [local irreducible] inverseDensity inverseJacDensity

lemma weighted_inverse_identity (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {z : ℂ} (hz : z ∈ outsideCore) :
    (∫⁻ g, inverseJacDensity g z ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (z.im^(-β-4)) *
        (∫⁻ g, inverseDensity g (affineInverse z) ∂(P : Measure DiskClass)) := by
  have hy : 0 < z.im := hz.1
  have hden : Measurable (fun g => inverseDensity g (affineInverse z)) :=
    measurable_inverseDensity.comp (measurable_id.prodMk measurable_const)
  have he := hP ⟨z,hz.1⟩ _ hden
  have hid (g : DiskClass) :
      ENNReal.ofReal (classWeight g ⟨z,hz.1⟩)*inverseDensity (rerootClass g ⟨z,hz.1⟩) (affineInverse z) =
        ENNReal.ofReal (z.im^4)*inverseJacDensity g z := by
    simp only [inverseDensity,inverseJacDensity,planeClassValue_eq _ (affineInverse_mem hz.1),
      planeClassValue_eq _ hz.1,planeClassDeriv_eq _ hz.1]
    rw [← ENNReal.ofReal_mul (classWeight_pos g ⟨z,hz.1⟩).le,
      classWeight_inverse_value g hz,ENNReal.ofReal_mul (pow_nonneg hy.le 4)]
  simp_rw [hid] at he
  have hJac : Measurable (fun g => inverseJacDensity g z) :=
    measurable_inverseJacDensity.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_const_mul _ hJac] at he
  have hpow : ENNReal.ofReal (z.im^4) * ENNReal.ofReal (z.im^(-β-4)) = ENNReal.ofReal (z.im^(-β)) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hy.le 4),← Real.rpow_natCast,← Real.rpow_add hy]
    congr 1
    congr 1
    ring
  apply (ENNReal.mul_right_inj (by positivity : ENNReal.ofReal (z.im^4) ≠ 0) ENNReal.ofReal_ne_top).mp
  rw [← mul_assoc,hpow]
  exact he

lemma weightedInverseArea_expectation_le (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) :
    (∫⁻ g, weightedInverseArea β g ∂(P : Measure DiskClass)) ≤ ENNReal.ofReal (256*Real.pi) := by
  let A (z : ℂ) := ∫⁻ g, inverseJacDensity g z ∂(P : Measure DiskClass)
  let B (z : ℂ) := ∫⁻ g, inverseDensity g z ∂(P : Measure DiskClass)
  have hswap : (∫⁻ g, weightedInverseArea β g ∂(P : Measure DiskClass)) =
      ∫⁻ z in outsideCore, ENNReal.ofReal (z.im^(β+1))*B z := by
    unfold weightedInverseArea
    rw [lintegral_lintegral_swap]
    · apply lintegral_congr
      intro z
      have hm : Measurable (fun g => inverseDensity g z) :=
        measurable_inverseDensity.comp (measurable_id.prodMk measurable_const)
      exact lintegral_const_mul _ hm
    · exact ((((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
        measurable_inverseDensity).aemeasurable
  have hpoint (z : ℂ) (hz : z ∈ outsideCore) :
      ENNReal.ofReal (z.im^(β+1))*B z = ENNReal.ofReal (z.im⁻¹^3)*A (affineInverse z) := by
    have hy : 0 < z.im := hz.1
    dsimp only [A]
    rw [weighted_inverse_identity P β hP (affineInverse_mem_outsideCore hz),
      affineInverse_invol hz.1,affineInverse_im,← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hy.le) 3)]
    congr 1
    rw [Real.inv_rpow hy.le]
    have he : (z.im⁻¹^3 : ℝ) = z.im^(-3 : ℝ) := by
      rw [Real.rpow_neg hy.le]
      norm_cast
      simp
    rw [he,← Real.rpow_neg hy.le,← Real.rpow_add hy]
    congr 1
    ring
  rw [hswap,setLIntegral_congr_fun measurableSet_outsideCore hpoint,
    ← affineInverse_change_variables measurableSet_outsideCore (fun _ h => h.1)
      affineInverse_image_outsideCore A]
  have hswap₂ : (∫⁻ z in outsideCore, A z) =
      ∫⁻ g, (∫⁻ z in outsideCore, inverseJacDensity g z) ∂(P : Measure DiskClass) := by
    exact (lintegral_lintegral_swap measurable_inverseJacDensity.aemeasurable).symm
  rw [hswap₂]
  calc
    _ ≤ ∫⁻ _ : DiskClass, ENNReal.ofReal (256*Real.pi) ∂(P : Measure DiskClass) :=
      lintegral_mono inverseJacDensity_integral_le
    _ = _ := by simp

lemma weightedInverseArea_ae_finite (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) :
    ∀ᵐ g ∂(P : Measure DiskClass), weightedInverseArea β g < ∞ :=
  ae_lt_top (measurable_weightedInverseArea β)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (weightedInverseArea_expectation_le P β hP))

end Brennan

end

end OAI
