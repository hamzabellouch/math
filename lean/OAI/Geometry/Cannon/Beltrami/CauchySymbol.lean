import Mathlib
import OAI.Geometry.Cannon.Beltrami.Axis

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

namespace CannonBeltrami

lemma integral_inverse_fourier_mul {f g : ℂ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ z, (𝓕⁻ f) z*g z = ∫ z, f z*(𝓕⁻ g) z := by
  have hL : Continuous (fun p : ℂ × ℂ => (-(innerₗ ℂ)) p.1 p.2) :=
    continuous_inner.neg
  have he : (-(innerₗ ℂ)).flip= -(innerₗ ℂ) := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  have ht := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -(innerₗ ℂ)) Real.continuous_fourierChar hL hf hg
  rw [he] at ht
  exact ht

lemma inverse_fourier_l2_test (f : Lp ℂ 2 (volume : Measure ℂ))
    (hf : Integrable (f : ℂ → ℂ)) (g : SchwartzMap ℂ ℂ) :
    ∫ z, g z*(𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) z =
      ∫ z, g z*(𝓕⁻ (f : ℂ → ℂ)) z := by
  have ht := congrArg (fun u : TemperedDistribution ℂ ℂ => u g)
    (Lp.fourierInv_toTemperedDistribution_eq f)
  simp only [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,
    smul_eq_mul] at ht
  have hp := integral_inverse_fourier_mul hf g.integrable
  calc
    _ = ∫ z, (𝓕⁻ g) z*f z := ht.symm
    _ = ∫ z, f z*(𝓕⁻ (g : ℂ → ℂ)) z := by
      congr 1; funext z; rw [mul_comm,SchwartzMap.fourierInv_coe]
    _ = ∫ z, (𝓕⁻ (f : ℂ → ℂ)) z*g z := hp.symm
    _ = _ := by congr 1; funext z; exact mul_comm _ _

lemma inverse_fourier_l2_real_test (f : Lp ℂ 2 (volume : Measure ℂ))
    (hf : Integrable (f : ℂ → ℂ)) (g : ℂ → ℝ)
    (hgd : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    ∫ z, g z • (𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) z =
      ∫ z, g z • (𝓕⁻ (f : ℂ → ℂ)) z := by
  have hgs' : HasCompactSupport (fun z => (g z:ℂ)) := HasCompactSupport.comp_left (g := Complex.ofReal) hgs Complex.ofReal_zero
  have hgd' : ContDiff ℝ ∞ (fun z => (g z:ℂ)) := Complex.ofRealCLM.contDiff.comp hgd
  let sg : SchwartzMap ℂ ℂ := hgs'.toSchwartzMap hgd'
  have ht := inverse_fourier_l2_test f hf sg
  change (∫ z, (g z : ℂ)*(𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) z) =
    (∫ z, (g z:ℂ)*(𝓕⁻ (f:ℂ → ℂ)) z) at ht
  simpa only [Complex.real_smul] using ht

lemma continuous_inverse_fourier {f : ℂ → ℂ} (hf : Integrable f) :
    Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous (L := -(innerₗ ℂ))
    Real.continuous_fourierChar continuous_inner.neg hf

theorem inverse_fourier_l2_ae (f : Lp ℂ 2 (volume : Measure ℂ))
    (hf : Integrable (f : ℂ → ℂ)) :
    (𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) =ᵐ[volume] 𝓕⁻ (f : ℂ → ℂ) := by
  have hloc : LocallyIntegrable (𝓕⁻ f : Lp ℂ 2 (volume : Measure ℂ)) volume :=
    (Lp.memLp (𝓕⁻ f)).locallyIntegrable (by norm_num)
  exact ae_eq_of_integral_contDiff_smul_eq hloc
    (continuous_inverse_fourier hf).locallyIntegrable (inverse_fourier_l2_real_test f hf)

end CannonBeltrami

namespace CannonBeltrami
open FourierTransform
open scoped RealInnerProductSpace

lemma SmoothL2.representative_ae {f : PlaneL2} (hf : SmoothL2 f) :
    f =ᵐ[volume] smoothRepresentative f := by
  have h := inverse_fourier_l2_ae (planeFourier f) hf.fourier_integrable
  have he : (𝓕⁻ (planeFourier f) : PlaneL2)=f := planeFourier.symm_apply_apply f
  rw [he] at h
  exact h

lemma SmoothL2.beurling {f : PlaneL2} (hf : SmoothL2 f) : SmoothL2 (beurling f) :=
  fun n => (hf n).beurling

lemma fourierSMulRight_inverse (f : ℂ → ℂ) (z v : ℂ) :
    VectorFourier.fourierSMulRight (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) f z v =
      directionSymbol v z*f z := by
  change -(2*(Real.pi:ℂ)*Complex.I) • (-inner ℝ z v) • f z = directionSymbol v z*f z
  simp only [Complex.real_smul,smul_eq_mul,directionSymbol]
  push_cast
  rw [real_inner_comm z v]
  ring

lemma SmoothL2.integrable_fourierSMulRight {f : PlaneL2} (hf : SmoothL2 f) :
    Integrable (VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) (planeFourier f)) volume := by
  let L := -(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  apply ((hf.fourier_moments 1).const_mul (2*Real.pi*‖L‖)).mono'
    (Lp.aestronglyMeasurable (planeFourier f)).fourierSMulRight
  filter_upwards with z
  simpa only [pow_one,mul_assoc] using VectorFourier.norm_fourierSMulRight_le L (planeFourier f) z

theorem SmoothL2.representative_derivative {f : PlaneL2} (hf : SmoothL2 f)
    (df : PlaneL2) (v : ℂ)
    (hae : planeFourier df =ᵐ[volume] fun z => directionSymbol v z*planeFourier f z)
    (x : ℂ) :
    fderiv ℝ (smoothRepresentative f) x v = smoothRepresentative df x := by
  let L := -(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  have hm : Integrable (fun z => ‖z‖*‖planeFourier f z‖) volume := by
    simpa only [pow_one] using hf.fourier_moments 1
  have hd := VectorFourier.hasFDerivAt_fourierIntegral L hf.fourier_integrable hm x
  change HasFDerivAt (smoothRepresentative f) _ x at hd
  rw [hd.fderiv,Real.fourierIntegral_continuousLinearMap_apply' hf.integrable_fourierSMulRight]
  apply congrFun (VectorFourier.fourierIntegral_congr_ae _ _ _ ?_) x
  filter_upwards [hae] with z hz
  rw [fourierSMulRight_inverse,hz]

end CannonBeltrami

namespace CannonBeltrami

lemma smooth_beltrami_equation (μ b : SchwartzMap ℂ ℂ) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) (h : PlaneL2) (hh : SmoothL2 h)
    (he : h-multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h)=b.toLp 2) :
    ∀ z, smoothRepresentative h z-μ z*smoothRepresentative (beurling h) z=b z := by
  have hae : (fun z => smoothRepresentative h z-μ z*smoothRepresentative (beurling h) z) =ᵐ[volume] b := by
    have he' := congrArg (fun f : PlaneL2 => (f : ℂ → ℂ)) he
    have h0 := Lp.coeFn_sub h (multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h))
    rw [he'] at h0
    filter_upwards [h0,multiplier_ae μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h),
      hh.representative_ae,hh.beurling.representative_ae,b.coeFn_toLp 2 volume] with z h1 h2 h3 h4 h5
    simp only [Pi.sub_apply] at h1
    rw [h2,h3,h4,h5] at h1
    exact h1.symm
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae
    (hh.contDiff.continuous.sub (μ.continuous.mul hh.beurling.contDiff.continuous)) b.continuous
  exact congrFun heq

lemma smooth_beltrami_compactSupport (μ b : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) (hcb : HasCompactSupport (b : ℂ → ℂ))
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) (h : PlaneL2) (hh : SmoothL2 h)
    (he : h-multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling h)=b.toLp 2) :
    HasCompactSupport (smoothRepresentative h) := by
  have hp := smooth_beltrami_equation μ b hk hb h hh he
  apply (hcμ.union hcb).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport μ).union (isClosed_tsupport b))
  intro z hz
  by_contra hn
  have hμz : μ z=0 := image_eq_zero_of_notMem_tsupport (fun hz' => hn (Or.inl hz'))
  have hbz : b z=0 := image_eq_zero_of_notMem_tsupport (fun hz' => hn (Or.inr hz'))
  have hhz : smoothRepresentative h z=0 := by simpa [hμz,hbz] using hp z
  exact hz hhz

theorem solve_compact_smooth_beltrami (μ b : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) (hcb : HasCompactSupport (b : ℂ → ℂ))
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ h : SchwartzMap ℂ ℂ, HasCompactSupport (h : ℂ → ℂ) ∧
      ∀ z, h z-μ z*smoothRepresentative (beurling (h.toLp 2)) z=b z := by
  obtain ⟨h,he,hn,hh⟩ := solve_schwartz_beltrami μ b hk hk1 hb
  change SmoothL2 h at hh
  have hc := smooth_beltrami_compactSupport μ b hcμ hcb hk hb h hh he
  let hs : SchwartzMap ℂ ℂ := hc.toSchwartzMap hh.contDiff
  have hsLp : hs.toLp 2=h := by
    apply Lp.ext
    exact (hs.coeFn_toLp 2 volume).trans hh.representative_ae.symm
  refine ⟨hs,hc,?_⟩
  rw [hsLp]
  exact smooth_beltrami_equation μ b hk hb h hh he

end CannonBeltrami

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

namespace CannonBeltrami

def cauchySymbol (z : ℂ) : ℂ := (Real.pi*Complex.I*z)⁻¹

lemma measurable_cauchySymbol : Measurable cauchySymbol := by
  unfold cauchySymbol
  fun_prop

lemma norm_cauchySymbol (z : ℂ) : ‖cauchySymbol z‖ = Real.pi⁻¹*‖z‖⁻¹ := by
  simp [cauchySymbol,abs_of_pos Real.pi_pos,mul_comm]

lemma cauchySymbol_le_on_compl {z : ℂ} (hz : z ∉ ball (0:ℂ) 1) :
    ‖cauchySymbol z‖ ≤ Real.pi⁻¹ := by
  have hz' : 1 ≤ ‖z‖ := by simpa only [mem_ball_zero_iff,not_lt] using hz
  rw [norm_cauchySymbol]
  exact mul_le_of_le_one_right (inv_pos.mpr Real.pi_pos).le (inv_le_one_of_one_le₀ hz')

lemma cauchy_fourier_moments (f : SchwartzMap ℂ ℂ) (n : ℕ) :
    Integrable (fun z => ‖z‖^n*‖cauchySymbol z*f z‖) volume := by
  let F : ℂ → ℝ := fun z => ‖z‖^n*‖cauchySymbol z*f z‖
  have hm : AEStronglyMeasurable F volume :=
    (continuous_norm.pow n).aestronglyMeasurable.mul
      (measurable_cauchySymbol.aestronglyMeasurable.mul f.continuous.aestronglyMeasurable).norm
  have hi : IntegrableOn F (ball (0:ℂ) 1) volume := by
    apply integrableOn_ball_of_norm_le_rpow (by norm_num : 1 ≤ Module.finrank ℝ ℂ)
      (α:=1) (C:=Real.pi⁻¹*SchwartzMap.seminorm ℝ 0 0 f) (by norm_num) _ hm
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hn : ‖z‖^n ≤ 1 := pow_le_one₀ (norm_nonneg _) hz'
    change ‖‖z‖^n*‖cauchySymbol z*f z‖‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul,norm_cauchySymbol]
    rw [Real.rpow_neg_one]
    calc
      ‖z‖^n*(Real.pi⁻¹*‖z‖⁻¹*‖f z‖) ≤ 1*(Real.pi⁻¹*‖z‖⁻¹*SchwartzMap.seminorm ℝ 0 0 f) := by
        gcongr
        exact f.norm_le_seminorm ℝ z
      _ = _ := by ring
  have ho : IntegrableOn F (ball (0:ℂ) 1)ᶜ volume := by
    apply ((f.integrable_pow_mul volume n).const_mul Real.pi⁻¹).integrableOn.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    change ‖‖z‖^n*‖cauchySymbol z*f z‖‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul]
    calc
      ‖z‖^n*(‖cauchySymbol z‖*‖f z‖) ≤ ‖z‖^n*(Real.pi⁻¹*‖f z‖) := by
        gcongr
        exact cauchySymbol_le_on_compl hz
      _ = _ := by ring
  have hh := hi.union ho
  simpa only [union_compl_self,integrableOn_univ] using hh

lemma cauchy_fourier_integrable (f : SchwartzMap ℂ ℂ) :
    Integrable (fun z => cauchySymbol z*f z) volume := by
  apply integrable_norm_iff (measurable_cauchySymbol.aestronglyMeasurable.mul
    f.continuous.aestronglyMeasurable) |>.mp
  simpa using cauchy_fourier_moments f 0

def cauchyTransform (f : SchwartzMap ℂ ℂ) : ℂ → ℂ :=
  𝓕⁻ (fun z => cauchySymbol z*(𝓕 f) z)

lemma contDiff_cauchyTransform (f : SchwartzMap ℂ ℂ) :
    ContDiff ℝ ∞ (cauchyTransform f) := by
  have hc : ContDiff ℝ ∞ (𝓕 (fun z => cauchySymbol z*(𝓕 f) z)) :=
    Real.contDiff_fourier (fun n _ => cauchy_fourier_moments (𝓕 f) n)
  have he : cauchyTransform f=(fun z => (𝓕 (fun w => cauchySymbol w*(𝓕 f) w)) (-z)) := by
    funext z
    exact Real.fourierInv_eq_fourier_neg _ _
  rw [he]
  exact hc.comp contDiff_neg

lemma cauchyTransform_zero_at_infty (f : SchwartzMap ℂ ℂ) :
    Tendsto (cauchyTransform f) (cocompact ℂ) (𝓝 0) := by
  have ht : Tendsto (𝓕 (fun z => cauchySymbol z*(𝓕 f) z)) (cocompact ℂ) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact _
  have he : cauchyTransform f=(fun z => (𝓕 (fun w => cauchySymbol w*(𝓕 f) w)) (-z)) := by
    funext z
    exact Real.fourierInv_eq_fourier_neg _ _
  rw [he]
  exact ht.comp (Homeomorph.neg ℂ).toCocompactMap.cocompact_tendsto'

end CannonBeltrami

namespace CannonBeltrami
open scoped RealInnerProductSpace

lemma schwartz_smoothL2 (f : SchwartzMap ℂ ℂ) : SmoothL2 (f.toLp 2) :=
  fun n => schwartz_sobolev n f

lemma smoothRepresentative_schwartz (f : SchwartzMap ℂ ℂ) :
    smoothRepresentative (f.toLp 2) = f := by
  exact MeasureTheory.Measure.eq_of_ae_eq
    ((schwartz_smoothL2 f).representative_ae.symm.trans (f.coeFn_toLp 2 volume))
    (schwartz_smoothL2 f).contDiff.continuous f.continuous

def smoothBeurling (f : SchwartzMap ℂ ℂ) : ℂ → ℂ :=
  smoothRepresentative (beurling (f.toLp 2))

lemma contDiff_smoothBeurling (f : SchwartzMap ℂ ℂ) : ContDiff ℝ ∞ (smoothBeurling f) :=
  (schwartz_smoothL2 f).beurling.contDiff

lemma smoothBeurling_fourier (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    smoothBeurling f x = 𝓕⁻ (fun z => beurlingSymbol z*(𝓕 f) z) x := by
  unfold smoothBeurling smoothRepresentative
  apply Real.fourierInv_congr_ae
  have hf : planeFourier (f.toLp 2)=(𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq _
  have hB := fourier_beurling_ae (f.toLp 2)
  rw [hf] at hB
  filter_upwards [hB,(𝓕 f).coeFn_toLp 2 volume] with z hz hz'
  rw [hz,hz']

lemma inverse_fourier_derivative (f : ℂ → ℂ) (hf : Integrable f volume)
    (hm : Integrable (fun z => ‖z‖*‖f z‖) volume) (x v : ℂ) :
    fderiv ℝ (𝓕⁻ f) x v = 𝓕⁻ (fun z => directionSymbol v z*f z) x := by
  let L := -(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  have hi : Integrable (VectorFourier.fourierSMulRight L f) volume := by
    apply (hm.const_mul (2*Real.pi*‖L‖)).mono' hf.1.fourierSMulRight
    filter_upwards with z
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le L f z
  have hd := VectorFourier.hasFDerivAt_fourierIntegral L hf hm x
  change HasFDerivAt (𝓕⁻ f) _ x at hd
  rw [hd.fderiv,Real.fourierIntegral_continuousLinearMap_apply' hi]
  have he : (fun z => VectorFourier.fourierSMulRight L f z v)=
      (fun z => directionSymbol v z*f z) := funext (fun z => fourierSMulRight_inverse f z v)
  rw [he]
  rfl

lemma cauchySymbol_x {z : ℂ} (hz : z ≠ 0) :
    directionSymbol 1 z*cauchySymbol z=1+beurlingSymbol z := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hx : inner ℝ (1:ℂ) z=z.re := by simp [real_inner_eq_re_inner,RCLike.inner_apply]
  rw [directionSymbol,hx,cauchySymbol,beurlingSymbol,ite_eq_right hz]
  field_simp
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.star_def] using (Complex.add_conj z).symm

lemma cauchySymbol_y {z : ℂ} (hz : z ≠ 0) :
    directionSymbol Complex.I z*cauchySymbol z=Complex.I*(beurlingSymbol z-1) := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hy : inner ℝ Complex.I z=z.im := by simp [real_inner_eq_re_inner,RCLike.inner_apply]
  rw [directionSymbol,hy,cauchySymbol,beurlingSymbol,ite_eq_right hz]
  field_simp
  have hz' := Complex.sub_conj z
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

lemma integrable_beurling_fourier (f : SchwartzMap ℂ ℂ) :
    Integrable (fun z => beurlingSymbol z*(𝓕 f) z) volume := by
  apply ((𝓕 f).integrable (μ:=volume)).norm.mono'
    (measurable_beurlingSymbol.aestronglyMeasurable.mul (𝓕 f).continuous.aestronglyMeasurable)
  filter_upwards with z
  simp [norm_beurlingSymbol]

lemma inverseFourier_add {f g : ℂ → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (x : ℂ) :
    𝓕⁻ (fun z => f z+g z) x=𝓕⁻ f x+𝓕⁻ g x := by
  exact congrFun (VectorFourier.fourierIntegral_add (e:=Real.fourierChar)
    (L:= -innerₗ ℂ) Real.continuous_fourierChar (by exact continuous_inner.neg) hf hg) x

lemma inverseFourier_mul (f : ℂ → ℂ) (a x : ℂ) :
    𝓕⁻ (fun z => a*f z) x=a*𝓕⁻ f x := by
  exact congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
    (-innerₗ ℂ) f a) x

lemma inverseFourier_sub {f g : ℂ → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (x : ℂ) :
    𝓕⁻ (fun z => f z-g z) x=𝓕⁻ f x-𝓕⁻ g x := by
  have he : (fun z => f z-g z)=(fun z => f z+(-1)*g z) := by ext z; ring
  rw [he,inverseFourier_add hf (hg.const_mul (-1)),inverseFourier_mul]
  ring

lemma cauchyTransform_derivative_x (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    fderiv ℝ (cauchyTransform f) x 1 = f x+smoothBeurling f x := by
  have hm : Integrable (fun z => ‖z‖*‖cauchySymbol z*(𝓕 f) z‖) volume := by
    simpa only [pow_one] using cauchy_fourier_moments (𝓕 f) 1
  rw [cauchyTransform,inverse_fourier_derivative _ (cauchy_fourier_integrable _) hm]
  have hzero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := volume.ae_ne 0
  have he : (fun z => directionSymbol 1 z*(cauchySymbol z*(𝓕 f) z)) =ᵐ[volume]
      fun z => (𝓕 f) z+beurlingSymbol z*(𝓕 f) z := by
    filter_upwards [hzero] with z hz
    rw [← mul_assoc,cauchySymbol_x hz]
    ring
  rw [Real.fourierInv_congr_ae he]
  rw [inverseFourier_add ((𝓕 f).integrable (μ:=volume)) (integrable_beurling_fourier f)]
  rw [← smoothBeurling_fourier,← SchwartzMap.fourierInv_coe,fourierInv_fourier_eq]

lemma cauchyTransform_derivative_y (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    fderiv ℝ (cauchyTransform f) x Complex.I = Complex.I*(smoothBeurling f x-f x) := by
  have hm : Integrable (fun z => ‖z‖*‖cauchySymbol z*(𝓕 f) z‖) volume := by
    simpa only [pow_one] using cauchy_fourier_moments (𝓕 f) 1
  rw [cauchyTransform,inverse_fourier_derivative _ (cauchy_fourier_integrable _) hm]
  have hzero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := volume.ae_ne 0
  have he : (fun z => directionSymbol Complex.I z*(cauchySymbol z*(𝓕 f) z)) =ᵐ[volume]
      fun z => Complex.I*(beurlingSymbol z*(𝓕 f) z-(𝓕 f) z) := by
    filter_upwards [hzero] with z hz
    rw [← mul_assoc,cauchySymbol_y hz]
    ring
  rw [Real.fourierInv_congr_ae he]
  rw [inverseFourier_mul,inverseFourier_sub (integrable_beurling_fourier f) ((𝓕 f).integrable (μ:=volume))]
  rw [← smoothBeurling_fourier,← SchwartzMap.fourierInv_coe,fourierInv_fourier_eq]

def partialZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1-Complex.I*fderiv ℝ f z Complex.I)/2

def partialBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1+Complex.I*fderiv ℝ f z Complex.I)/2

theorem cauchyTransform_partials (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    partialBar (cauchyTransform f) z=f z ∧
    partialZ (cauchyTransform f) z=smoothBeurling f z := by
  simp only [partialZ,partialBar,cauchyTransform_derivative_x,cauchyTransform_derivative_y]
  constructor <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end CannonBeltrami

namespace CannonBeltrami
lemma realCLM_apply (D : ℂ →L[ℝ] ℂ) (v : ℂ) :
    D v = (v.re:ℂ)*D 1+(v.im:ℂ)*D Complex.I := by
  have hv : v = v.re • (1:ℂ)+v.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma fderiv_wirtinger (f : ℂ → ℂ) (z v : ℂ) :
    fderiv ℝ f z v=partialZ f z*v+partialBar f z*star v := by
  rw [realCLM_apply]
  unfold partialZ partialBar
  have hv := Complex.re_add_im v
  conv_rhs => rw [← hv]
  simp only [map_add,map_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

lemma differentiableAt_of_partialBar_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (h0 : partialBar f z=0) : DifferentiableAt ℂ f z := by
  let A : ℂ →L[ℂ] ℂ := (partialZ f z) • ContinuousLinearMap.id ℂ ℂ
  apply (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt (f':=A) ?_).differentiableAt
  ext v
  change partialZ f z*v = fderiv ℝ f z v
  rw [fderiv_wirtinger,h0,zero_mul,add_zero]

lemma partialBar_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : partialBar f z=0 := by
  unfold partialBar
  rw [hf.fderiv_restrictScalars ℝ]
  change (fderiv ℂ f z 1+Complex.I*fderiv ℂ f z Complex.I)/2=0
  have he : fderiv ℂ f z Complex.I=Complex.I*fderiv ℂ f z 1 := by
    simpa only [smul_eq_mul,mul_one] using (fderiv ℂ f z).map_smul Complex.I (1:ℂ)
  rw [he]
  calc
    (fderiv ℂ f z 1+Complex.I*(Complex.I*fderiv ℂ f z 1))/2 =
      ((1+Complex.I^2)*fderiv ℂ f z 1)/2 := by ring
    _ = 0 := by simp [Complex.I_sq]

lemma partials_const (a z : ℂ) :
    partialZ (fun _ : ℂ => a) z=0 ∧ partialBar (fun _ : ℂ => a) z=0 := by
  simp [partialZ,partialBar]

lemma partials_id (z : ℂ) : partialZ (fun w : ℂ => w) z=1 ∧
    partialBar (fun w : ℂ => w) z=0 := by
  simp [partialZ,partialBar]

lemma partials_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZ (fun w => f w+g w) z=partialZ f z+partialZ g z ∧
    partialBar (fun w => f w+g w) z=partialBar f z+partialBar g z := by
  unfold partialZ partialBar
  have hd : HasFDerivAt (fun w => f w+g w) (fderiv ℝ f z+fderiv ℝ g z) z :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  rw [hd.fderiv]
  simp only [add_apply]
  constructor <;> ring

lemma partials_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZ (fun w => f w-g w) z=partialZ f z-partialZ g z ∧
    partialBar (fun w => f w-g w) z=partialBar f z-partialBar g z := by
  unfold partialZ partialBar
  have hd : HasFDerivAt (fun w => f w-g w) (fderiv ℝ f z-fderiv ℝ g z) z :=
    hf.hasFDerivAt.sub hg.hasFDerivAt
  rw [hd.fderiv]
  simp only [sub_apply]
  constructor <;> ring

lemma partials_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZ (fun w => f w*g w) z=partialZ f z*g z+f z*partialZ g z ∧
    partialBar (fun w => f w*g w) z=partialBar f z*g z+f z*partialBar g z := by
  unfold partialZ partialBar
  rw [show fderiv ℝ (fun w => f w*g w) z =
    f z • fderiv ℝ g z+g z • fderiv ℝ f z from (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  constructor <;> ring

lemma partials_exp {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    partialZ (fun w => Complex.exp (f w)) z=Complex.exp (f z)*partialZ f z ∧
    partialBar (fun w => Complex.exp (f w)) z=Complex.exp (f z)*partialBar f z := by
  simp only [partialZ,partialBar,hf.hasFDerivAt.cexp.fderiv,
    smul_apply,smul_eq_mul]
  constructor <;> ring

lemma contDiff_partials {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialZ f) ∧ ContDiff ℝ ∞ (partialBar f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hx : ContDiff ℝ ∞ (fun z => fderiv ℝ f z 1) := hd.clm_apply contDiff_const
  have hy : ContDiff ℝ ∞ (fun z => fderiv ℝ f z Complex.I) := hd.clm_apply contDiff_const
  exact ⟨(hx.sub (contDiff_const.mul hy)).div_const 2,
    (hx.add (contDiff_const.mul hy)).div_const 2⟩

lemma wirtinger_commute {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    partialBar (partialZ f) z=partialZ (partialBar f) z := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp)
  let Dx : ℂ → ℂ := fun w => fderiv ℝ f w 1
  let Dy : ℂ → ℂ := fun w => fderiv ℝ f w Complex.I
  have hx : DifferentiableAt ℝ Dx z := (hd z).clm_apply (differentiableAt_const _)
  have hy : DifferentiableAt ℝ Dy z := (hd z).clm_apply (differentiableAt_const _)
  have he (v w : ℂ) : fderiv ℝ (fun u => fderiv ℝ f u v) z w =
      fderiv ℝ (fderiv ℝ f) z w v := by
    rw [fderiv_clm_apply (hd z) (differentiableAt_const _)]
    simp
  have hxy : fderiv ℝ Dx z Complex.I = fderiv ℝ Dy z 1 := by
    rw [he,he]
    exact hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _
  have hpx : fderiv ℝ (partialZ f) z =
      (2:ℂ)⁻¹ • (fderiv ℝ Dx z-Complex.I • fderiv ℝ Dy z) := by
    have heq : partialZ f=(fun w => (2:ℂ)⁻¹*(Dx w-Complex.I*Dy w)) := by
      ext w; dsimp [partialZ,Dx,Dy]; ring
    rw [heq]
    exact ((hx.hasFDerivAt.sub (hy.hasFDerivAt.const_mul Complex.I)).const_mul (2:ℂ)⁻¹).fderiv
  have hpy : fderiv ℝ (partialBar f) z =
      (2:ℂ)⁻¹ • (fderiv ℝ Dx z+Complex.I • fderiv ℝ Dy z) := by
    have heq : partialBar f=(fun w => (2:ℂ)⁻¹*(Dx w+Complex.I*Dy w)) := by
      ext w; dsimp [partialBar,Dx,Dy]; ring
    rw [heq]
    exact ((hx.hasFDerivAt.add (hy.hasFDerivAt.const_mul Complex.I)).const_mul (2:ℂ)⁻¹).fderiv
  change (fderiv ℝ (partialZ f) z 1+Complex.I*fderiv ℝ (partialZ f) z Complex.I)/2 =
    (fderiv ℝ (partialBar f) z 1-Complex.I*fderiv ℝ (partialBar f) z Complex.I)/2
  rw [hpx,hpy]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  rw [hxy]
  ring

lemma liouville_partialBar {f : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hbar : ∀ z, partialBar f z=0) {c : ℂ} (ht : Tendsto f (cocompact ℂ) (𝓝 c)) :
    ∀ z, f z=c := by
  have hc : Differentiable ℂ f := fun z => differentiableAt_of_partialBar_zero (hf z) (hbar z)
  exact fun z => hc.apply_eq_of_tendsto_cocompact z ht

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end

end OAI
