import Mathlib
import OAI.Probability.SLELocalization.WeightedEnergy

namespace OAI


/-! Conformal localization and Rectangle Energy estimates. -/

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
open Layer

lemma annular_invSquare_integral {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    (∫⁻ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}, ENNReal.ofReal (1/‖z‖^2)) ≤
      ENNReal.ofReal (2*Real.pi*Real.log (R/r)) := by
  apply (polar_annulus_lintegral_le _ hr).trans
  have he : (∫⁻ s in Ioo r R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal s*ENNReal.ofReal (1/‖s • circleMap 0 1 θ‖^2)) =
      ENNReal.ofReal (2*Real.pi)*(∫⁻ s in Ioo r R, ENNReal.ofReal s⁻¹) := by
    calc
      _ = ∫⁻ s in Ioo r R, ENNReal.ofReal (2*Real.pi)*ENNReal.ofReal s⁻¹ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        have hs0 := hr.trans hs.1
        simp only [radial_norm,abs_of_pos hs0]
        have hmul : ENNReal.ofReal s*ENNReal.ofReal (1/s^2) = ENNReal.ofReal s⁻¹ := by
          rw [← ENNReal.ofReal_mul hs0.le]
          congr 1
          field_simp
        simp only [hmul,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,
          show Real.pi - -Real.pi = 2*Real.pi by ring]
        exact mul_comm _ _
      _ = _ := by rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top
  rw [he]
  have hc : ContinuousOn (fun s : ℝ => s⁻¹) (Icc r R) :=
    continuousOn_id.inv₀ (fun s hs => (hr.trans_le hs.1).ne')
  have hi : IntegrableOn (fun s : ℝ => s⁻¹) (Ioc r R) :=
    (hc.intervalIntegrable_of_Icc hR.le).1
  have hnon : 0 ≤ᵐ[volume.restrict (Ioc r R)] (fun s : ℝ => s⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact inv_nonneg.2 (hr.trans hs.1).le
  have hint : (∫ s in r..R, s⁻¹) = Real.log (R/r) := by
    apply integral_inv
    rw [uIcc_of_le hR.le]
    intro hz
    exact (not_le_of_gt hr) hz.1
  have heq : (∫⁻ s in Ioo r R, ENNReal.ofReal s⁻¹) = ENNReal.ofReal (Real.log (R/r)) := by
    rw [restrict_Ioo_eq_restrict_Ioc,← ofReal_integral_eq_lintegral_ofReal hi hnon,
      ← intervalIntegral.integral_of_le hR.le,hint]
  rw [heq,← ENNReal.ofReal_mul (by positivity)]

def annularKernel (r R : ℝ) (z : ℂ) : ℝ≥0∞ :=
  if r < ‖z‖ ∧ ‖z‖ < R then ENNReal.ofReal (1/‖z‖^2) else 0

lemma annularKernel_integral {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    (∫⁻ z : ℂ, annularKernel r (Real.exp H*r) (z-q)) ≤ ENNReal.ofReal (2*Real.pi*H) := by
  rw [lintegral_sub_right_eq_self]
  have he : annularKernel r (Real.exp H*r) =
      {z : ℂ | r < ‖z‖ ∧ ‖z‖ < Real.exp H*r}.indicator (fun z => ENNReal.ofReal (1/‖z‖^2)) := by
    ext z
    simp [annularKernel,Set.indicator]
  have hA : MeasurableSet {z : ℂ | r < ‖z‖ ∧ ‖z‖ < Real.exp H*r} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  rw [he,lintegral_indicator hA]
  have hR : r < Real.exp H*r := (lt_mul_iff_one_lt_left hr).2 (Real.one_lt_exp_iff.2 hH)
  have hh := annular_invSquare_integral hr hR
  have hlog : Real.log (Real.exp H*r/r) = H := by
    rw [mul_div_cancel_right₀ _ hr.ne',Real.log_exp]
  simpa only [hlog] using hh

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma complex_real_jacobian (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖^2 := by
  simp [ContinuousLinearMap.det,LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq,Complex.normSq_eq_norm_sq]

theorem conformal_truncation_energy {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    (∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ (radialTruncation H q r ∘ F) z‖^2)) ≤
      ENNReal.ofReal (2*Real.pi*H) := by
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet
    (fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    hinj (fun w => annularKernel r (Real.exp H*r) (w-q))
  calc
    _ ≤ ∫⁻ z in U, ENNReal.ofReal (‖deriv F z‖^2)*annularKernel r (Real.exp H*r) (F z-q) := by
      apply setLIntegral_mono' hU.measurableSet
      intro z hz
      have hb := radialTruncation_fderiv_bound hH.le hr (q := q)
        (hF.differentiableAt (hU.mem_nhds hz))
      apply (ENNReal.ofReal_le_ofReal hb).trans
      by_cases hh : r < ‖F z-q‖ ∧ ‖F z-q‖ < Real.exp H*r
      · rw [ite_eq_left hh,annularKernel,ite_eq_left hh,← ENNReal.ofReal_mul (sq_nonneg _)]
        apply le_of_eq
        congr 1
        ring
      · simp only [ite_eq_right hh,annularKernel,ENNReal.ofReal_zero,mul_zero,le_refl]
    _ = ∫⁻ w in F '' U, annularKernel r (Real.exp H*r) (w-q) := by
      rw [hchange]
      apply setLIntegral_congr_fun hU.measurableSet
      intro z hz
      dsimp only
      rw [complex_real_jacobian,abs_of_nonneg (sq_nonneg _)]
    _ ≤ ∫⁻ w : ℂ, annularKernel r (Real.exp H*r) (w-q) := lintegral_mono_set (subset_univ _) |> fun h => by simpa using h
    _ ≤ _ := annularKernel_integral hH hr q

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal OnePoint
namespace SLEExactGauge.RectangleEnergy

def sphereTruncation (H : ℝ) (q : ℂ) (r : ℝ) : OnePoint ℂ → ℝ :=
  OnePoint.rec H (radialTruncation H q r)

@[simp] lemma sphereTruncation_coe (H : ℝ) (q : ℂ) (r : ℝ) (z : ℂ) :
    sphereTruncation H q r (z : OnePoint ℂ) = radialTruncation H q r z := rfl

@[simp] lemma sphereTruncation_infty (H : ℝ) (q : ℂ) (r : ℝ) :
    sphereTruncation H q r ∞ = H := rfl

lemma sphereTruncation_continuous {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) :
    Continuous (sphereTruncation H q r) := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty =>
    apply OnePoint.continuousAt_infty.2
    intro s hs
    refine ⟨closedBall q (Real.exp H*r),isClosed_closedBall,isCompact_closedBall _ _,?_⟩
    intro w hw
    have hd : Real.exp H*r ≤ ‖w-q‖ := by
      have hn : Real.exp H*r < dist w q := lt_of_not_ge hw
      exact (show Real.exp H*r < ‖w-q‖ by simpa [dist_eq_norm] using hn).le
    change radialTruncation H q r w ∈ s
    rw [radialTruncation_top hH hr hd]
    exact mem_of_mem_nhds hs
  | coe w =>
    exact OnePoint.continuousAt_coe.2 (radialTruncation_continuous hr H q).continuousAt

lemma sphereTruncation_bounds {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ)
    (z : OnePoint ℂ) : 0 ≤ sphereTruncation H q r z ∧ sphereTruncation H q r z ≤ H := by
  induction z using OnePoint.rec with
  | infty => exact ⟨hH,le_rfl⟩
  | coe w => exact radialTruncation_bounds hH hr q w

lemma sphereTruncation_top_of_outside {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ)
    {z : OnePoint ℂ} (hz : z ∉ (fun w : ℂ => (w : OnePoint ℂ)) '' ball q (Real.exp H*r)) :
    sphereTruncation H q r z = H := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe w =>
    apply radialTruncation_top hH hr
    have hn : w ∉ ball q (Real.exp H*r) := fun hw => hz ⟨w,hw,rfl⟩
    simpa [mem_ball,dist_eq_norm] using (le_of_not_gt hn : Real.exp H*r ≤ dist w q)

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

def openStrip : Set ℂ := {z | 0 < z.im ∧ z.im < Real.pi}

def closedStrip : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ Real.pi}

def stripPotential (H : ℝ) (q : ℂ) (r : ℝ) (Fbar : ℂ → OnePoint ℂ) (z : ℂ) : ℝ :=
  sphereTruncation H q r (Fbar (Complex.exp z))

lemma openStrip_isOpen : IsOpen openStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

lemma exp_mem_halfPlane {z : ℂ} (hz : z ∈ openStrip) : 0 < (Complex.exp z).im := by
  rw [Complex.exp_im]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)

lemma exp_mem_closedHalfPlane {z : ℂ} (hz : z ∈ closedStrip) : 0 ≤ (Complex.exp z).im := by
  rw [Complex.exp_im]
  exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_mem_Icc hz)

lemma exp_injOn_strip : InjOn Complex.exp openStrip := by
  intro z hz w hw hzw
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi
    ((neg_lt_zero.2 Real.pi_pos).trans hz.1) hz.2.le
    ((neg_lt_zero.2 Real.pi_pos).trans hw.1) hw.2.le hzw

lemma stripPotential_continuous {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ)
    {Fbar : ℂ → OnePoint ℂ} (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im}) :
    ContinuousOn (stripPotential H q r Fbar) closedStrip :=
  (sphereTruncation_continuous hH hr q).continuousOn.comp
    (hcont.comp Complex.continuous_exp.continuousOn (fun z hz => exp_mem_closedHalfPlane (z := z) hz))
    (fun _ _ => mem_univ _)

theorem strip_potential_energy {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    (∫⁻ z in openStrip, ENNReal.ofReal (‖fderiv ℝ (stripPotential H q r Fbar) z‖^2)) ≤
      ENNReal.ofReal (2*Real.pi*H) := by
  have hdiff : DifferentiableOn ℂ (F ∘ Complex.exp) openStrip := by
    intro z hz
    exact ((hF _ (exp_mem_halfPlane hz)).differentiableAt.comp z
      (Complex.differentiable_exp z)).differentiableWithinAt
  have hi : InjOn (F ∘ Complex.exp) openStrip :=
    hinj.comp exp_injOn_strip (fun z hz => exp_mem_halfPlane hz)
  have hb := conformal_truncation_energy openStrip_isOpen hdiff hi hH hr q
  have he : (∫⁻ z in openStrip, ENNReal.ofReal (‖fderiv ℝ (stripPotential H q r Fbar) z‖^2)) =
      ∫⁻ z in openStrip, ENNReal.ofReal (‖fderiv ℝ (radialTruncation H q r ∘ (F ∘ Complex.exp)) z‖^2) := by
    apply setLIntegral_congr_fun openStrip_isOpen.measurableSet
    intro z hz
    have heq : stripPotential H q r Fbar =ᶠ[𝓝 z]
        (radialTruncation H q r ∘ (F ∘ Complex.exp)) := by
      filter_upwards [openStrip_isOpen.mem_nhds hz] with w hw
      simp only [stripPotential,hext _ (exp_mem_halfPlane hw),sphereTruncation_coe,Function.comp_apply]
    dsimp only
    rw [heq.fderiv_eq]
  rw [he]
  exact hb

theorem access_section_zero {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ)
    {Fbar : ℂ → OnePoint ℂ} {η : ℝ → ℂ} (hη : ContinuousOn η (Icc 0 1))
    (hη0 : η 0 = 0) (hη1 : ‖η 1‖ = 1) (hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
    (haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
      (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r)
    {v : ℝ} (hv : v < 0) : ∃ φ ∈ Icc (0:ℝ) Real.pi,
      stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I) = 0 := by
  have hm : Real.exp v ∈ Icc ‖η 0‖ ‖η 1‖ := by
    rw [hη0,hη1,norm_zero]
    exact ⟨(Real.exp_pos _).le,(Real.exp_lt_one_iff.2 hv).le⟩
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hη.norm hm
  dsimp only at he
  have henz : η t ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; exact (Real.exp_pos _).ne')
  have hlogRe : (Complex.log (η t)).re = v := by rw [Complex.log_re,he,Real.log_exp]
  have hlog : (v:ℂ)+(Complex.arg (η t):ℂ)*Complex.I = Complex.log (η t) := by
    rw [← hlogRe,← Complex.log_im]
    exact Complex.re_add_im _
  refine ⟨Complex.arg (η t),⟨Complex.arg_nonneg_iff.2 (hηH t ht),Complex.arg_le_pi _⟩,?_⟩
  obtain ⟨w,hw,hew⟩ := haccess t ht
  simp only [stripPotential,hlog,Complex.exp_log henz,← hew,sphereTruncation_coe]
  apply radialTruncation_zero hH hr
  simpa only [mem_closedBall,dist_eq_norm] using hw

lemma stripPotential_interior_eq {F : ℂ → ℂ} {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (H r : ℝ) (q : ℂ) {z : ℂ} (hz : z ∈ openStrip) :
    stripPotential H q r Fbar =ᶠ[𝓝 z] radialTruncation H q r ∘ (F ∘ Complex.exp) := by
  filter_upwards [openStrip_isOpen.mem_nhds hz] with w hw
  simp only [stripPotential,hext _ (exp_mem_halfPlane hw),sphereTruncation_coe,Function.comp_apply]

lemma stripPotential_vertical_AC_interior {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hr : 0 < r) (q : ℂ) (v : ℝ) {a b : ℝ}
    (ha : a ∈ Ioo (0:ℝ) Real.pi) (hb : b ∈ Ioo (0:ℝ) Real.pi) :
    AbsolutelyContinuousOnInterval
      (fun φ : ℝ => stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I)) a b := by
  let c := fun φ : ℝ => (v:ℂ)+(φ:ℂ)*Complex.I
  have hc : ContDiff ℝ 1 c := contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hmap : MapsTo c (uIcc a b) openStrip := by
    intro φ hφ
    have hlo : 0 < φ := lt_of_lt_of_le (lt_min ha.1 hb.1) hφ.1
    have hhi : φ < Real.pi := lt_of_le_of_lt hφ.2 (max_lt ha.2 hb.2)
    simpa [c,openStrip] using And.intro hlo hhi
  have hdiff : DifferentiableOn ℂ (F ∘ Complex.exp) openStrip := by
    intro z hz
    exact ((hF _ (exp_mem_halfPlane hz)).differentiableAt.comp z
      (Complex.differentiable_exp z)).differentiableWithinAt
  have hG : ContDiffOn ℝ 1 ((F ∘ Complex.exp) ∘ c) (uIcc a b) :=
    ((hdiff.contDiffOn openStrip_isOpen).restrict_scalars ℝ).comp hc.contDiffOn hmap
  apply acl_congr (radialTruncation_along_C1_AC hr H q hG)
  intro φ hφ
  exact ((stripPotential_interior_eq hext H r q (hmap hφ)).self_of_nhds).symm

lemma stripPotential_vertical_deriv {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) (v : ℝ) {φ : ℝ}
    (hφ : φ ∈ Ioo (0:ℝ) Real.pi) :
    deriv (fun ψ : ℝ => stripPotential H q r Fbar ((v:ℂ)+(ψ:ℂ)*Complex.I)) φ =
      fderiv ℝ (stripPotential H q r Fbar) ((v:ℂ)+(φ:ℂ)*Complex.I) Complex.I := by
  let c := fun ψ : ℝ => (v:ℂ)+(ψ:ℂ)*Complex.I
  have hmem : c φ ∈ openStrip := by simpa [c,openStrip] using hφ
  have he := stripPotential_interior_eq hext H r q hmem
  have hc : HasDerivAt c Complex.I φ := by
    simpa [c,Complex.ofRealCLM] using ((Complex.ofRealCLM.hasDerivAt).mul_const Complex.I).const_add (v:ℂ)
  have hd := radialTruncation_directional_deriv hH hr q (c := c) (t := φ) (d := Complex.I)
    ((hF _ (exp_mem_halfPlane hmem)).differentiableAt.comp _ (Complex.differentiable_exp _)) hc
  rw [← he.fderiv_eq] at hd
  refine (he.comp_tendsto hc.continuousAt).deriv_eq.trans hd

theorem stripPotential_vertical_zero_energy {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) (v : ℝ)
    (hE : MemLp (fun φ : ℝ => ‖fderiv ℝ (stripPotential H q r Fbar)
      ((v:ℂ)+(φ:ℂ)*Complex.I)‖) 2 (volume.restrict (Ioc (0:ℝ) Real.pi)))
    {z : ℝ} (hz : z ∈ Icc (0:ℝ) Real.pi)
    (hzero : stripPotential H q r Fbar ((v:ℂ)+(z:ℂ)*Complex.I) = 0)
    {φ : ℝ} (hφ : φ ∈ Icc (0:ℝ) Real.pi) :
    (stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I))^2 ≤
      Real.pi*(∫ ψ in (0:ℝ)..Real.pi, ‖fderiv ℝ (stripPotential H q r Fbar)
        ((v:ℂ)+(ψ:ℂ)*Complex.I)‖^2) := by
  let f := fun φ : ℝ => stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I)
  let e := fun φ : ℝ => ‖fderiv ℝ (stripPotential H q r Fbar) ((v:ℂ)+(φ:ℂ)*Complex.I)‖
  have hb : ∀ᵐ ψ ∂volume.restrict (Ioc (0:ℝ) Real.pi), ‖deriv f ψ‖ ≤ e ψ := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ψ hψ
    rw [stripPotential_vertical_deriv hF hext hH hr q v hψ]
    simpa only [e,Complex.norm_I,mul_one] using
      (fderiv ℝ (stripPotential H q r Fbar) ((v:ℂ)+(ψ:ℂ)*Complex.I)).le_opNorm Complex.I
  have hD := hE.mono' (aestronglyMeasurable_deriv f _) hb
  have hc : ContinuousOn f (Icc 0 Real.pi) :=
    (stripPotential_continuous hH hr q hcont).comp
      (continuous_const.add (Complex.continuous_ofReal.mul_const _)).continuousOn
      (by intro ψ hψ; simpa [closedStrip] using hψ)
  have ht := boundary_zero_energy Real.pi_pos hc hD
    (fun a ha b hb => stripPotential_vertical_AC_interior hF hext hr q v ha hb) hz hzero hφ
  have hm : (∫ ψ in (0:ℝ)..Real.pi, (deriv f ψ)^2) ≤
      ∫ ψ in (0:ℝ)..Real.pi, (e ψ)^2 := by
    simp only [intervalIntegral.integral_of_le Real.pi_pos.le]
    apply integral_mono_ae hD.integrable_sq hE.integrable_sq
    filter_upwards [hb] with ψ hψ
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hψ 2
  simp only [sub_zero] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hm Real.pi_pos.le)

lemma strip_energy_integrable {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    IntegrableOn (fun z => ‖fderiv ℝ (stripPotential H q r Fbar) z‖^2) openStrip := by
  refine ⟨((measurable_fderiv ℝ _).norm.pow_const 2).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => sq_nonneg _))]
  exact (strip_potential_energy hF hinj hext hH hr q).trans_lt (ENNReal.ofReal_lt_top)

lemma strip_energy_integrable_prod {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    Integrable (fun p : ℝ × ℝ => ‖fderiv ℝ (stripPotential H q r Fbar)
      ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2)
      (volume.prod (volume.restrict (Ioo (0:ℝ) Real.pi))) := by
  have hi := (Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
    Complex.measurableEquivRealProd.symm.measurableEmbedding |>.2
      (strip_energy_integrable hF hinj hext hH hr q)
  have hs : Complex.measurableEquivRealProd.symm ⁻¹' openStrip =
      (univ : Set ℝ).prod (Ioo (0:ℝ) Real.pi) := by
    ext p
    change (0 < p.2 ∧ p.2 < Real.pi) ↔ True ∧ (0 < p.2 ∧ p.2 < Real.pi)
    simp
  rw [hs] at hi
  change Integrable _ ((volume.prod volume).restrict ((univ : Set ℝ) ×ˢ Ioo (0:ℝ) Real.pi)) at hi
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hi
  convert hi using 1
  funext p
  have hp : (p.1:ℂ)+(p.2:ℂ)*Complex.I = Complex.measurableEquivRealProd.symm p := by
    apply Complex.ext <;> simp
  rw [hp]
  rfl

theorem strip_vertical_memLp_ae {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    ∀ᵐ v : ℝ, MemLp (fun φ : ℝ => ‖fderiv ℝ (stripPotential H q r Fbar)
      ((v:ℂ)+(φ:ℂ)*Complex.I)‖) 2 (volume.restrict (Ioc (0:ℝ) Real.pi)) := by
  have hi := (strip_energy_integrable_prod hF hinj hext hH hr q).prod_right_ae
  filter_upwards [hi] with v hv
  rw [← restrict_Ioo_eq_restrict_Ioc]
  apply (memLp_two_iff_integrable_sq ?_).2 hv
  exact ((measurable_fderiv ℝ _).comp
    ((measurable_const.add (Complex.measurable_ofReal.mul_const _)))).norm.aestronglyMeasurable

theorem strip_negative_section_energy {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {η : ℝ → ℂ} (hη : ContinuousOn η (Icc 0 1)) (hη0 : η 0 = 0)
    (hη1 : ‖η 1‖ = 1) (hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
    (haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
      (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r) :
    ∀ᵐ v : ℝ, v < 0 → ∀ φ ∈ Icc (0:ℝ) Real.pi,
      (stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I))^2 ≤
        Real.pi*(∫ ψ in (0:ℝ)..Real.pi, ‖fderiv ℝ (stripPotential H q r Fbar)
          ((v:ℂ)+(ψ:ℂ)*Complex.I)‖^2) := by
  filter_upwards [strip_vertical_memLp_ae hF hinj hext hH hr q] with v hv
  intro hv0 φ hφ
  obtain ⟨z,hz,hzero⟩ := access_section_zero hH.le hr q hη hη0 hη1 hηH haccess hv0
  exact stripPotential_vertical_zero_energy hF hext hcont hH.le hr q v hv hz hzero hφ

lemma mean_difference_abs_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : α → ℝ} {v : β → ℝ} (hu : Integrable u μ) (hv : Integrable v ν) :
    |(∫ x, u x ∂μ)-(∫ y, v y ∂ν)| ≤ ∫ x, ∫ y, |u x-v y| ∂ν ∂μ := by
  have hD : Integrable (fun p : α × β => u p.1-v p.2) (μ.prod ν) :=
    (hu.comp_fst ν).sub (hv.comp_snd μ)
  have he : (∫ p : α × β, u p.1-v p.2 ∂μ.prod ν) =
      (∫ x, u x ∂μ)-(∫ y, v y ∂ν) := by
    rw [integral_prod _ hD]
    simp_rw [integral_sub (integrable_const _) hv]
    simp only [integral_const,probReal_univ,one_smul]
    rw [integral_sub hu (integrable_const _)]
    simp
  have hh := norm_integral_le_integral_norm (μ := μ.prod ν) (fun p : α × β => u p.1-v p.2)
  rw [he,integral_prod _ hD.norm] at hh
  simpa only [Real.norm_eq_abs] using hh

theorem rectangle_mean_L1_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ μ' : Measure X} {ν ν' : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {u : X × Y → ℝ} (hu : Integrable u (μ.prod ν)) (hu' : Integrable u (μ'.prod ν'))
    {R : Y → ℝ} {C : X → ℝ} (hR : Integrable R ν') (hC : Integrable C μ)
    (hbound : ∀ᵐ p ∂μ'.prod ν', ∀ᵐ q ∂μ.prod ν, |u p-u q| ≤ R p.2+C q.1) :
    |(∫ p, u p ∂μ'.prod ν')-(∫ p, u p ∂μ.prod ν)| ≤
      (∫ y, R y ∂ν')+(∫ x, C x ∂μ) := by
  let A := μ'.prod ν'
  let B := μ.prod ν
  have hD : Integrable (fun p : (X × Y) × (X × Y) => |u p.1-u p.2|) (A.prod B) :=
    ((hu'.comp_fst B).sub (hu.comp_snd A)).abs
  have hRi : Integrable (fun p : X × Y => R p.2) A := hR.comp_snd μ'
  have hCi : Integrable (fun p : X × Y => C p.1) B := hC.comp_fst ν
  have heC : (∫ p : X × Y, C p.1 ∂B) = ∫ x, C x ∂μ := by
    rw [integral_prod _ hCi]
    simp only [integral_const,probReal_univ,one_smul]
  have heR : (∫ p : X × Y, R p.2 ∂A) = ∫ y, R y ∂ν' := by
    rw [integral_prod _ hRi]
    simp only [integral_const,probReal_univ,one_smul]
  calc
    _ ≤ ∫ p, ∫ q, |u p-u q| ∂B ∂A := mean_difference_abs_le hu' hu
    _ ≤ ∫ p, R p.2+(∫ q, C q.1 ∂B) ∂A := by
      apply integral_mono_ae hD.integral_prod_left (hRi.add (integrable_const _))
      filter_upwards [hD.prod_right_ae,hbound] with p hp hb
      calc
        _ ≤ ∫ q, R p.2+C q.1 ∂B := integral_mono_ae hp ((integrable_const _).add hCi) hb
        _ = _ := by rw [integral_add (integrable_const _) hCi]; simp
    _ = _ := by
      rw [integral_add hRi (integrable_const _),heC,heR]
      simp

def intervalProb (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b-a))⁻¹ • volume.restrict (Ioc a b)

lemma intervalProb_isProbability {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (intervalProb a b) := by
  constructor
  simp only [intervalProb,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,Real.volume_Ioc]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.2 (sub_pos.2 hab)) ENNReal.ofReal_ne_top

lemma integral_intervalProb {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x, f x ∂intervalProb a b) = (b-a)⁻¹*(∫ x in a..b, f x) := by
  rw [intervalProb,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofReal (sub_nonneg.2 hab),
    smul_eq_mul,intervalIntegral.integral_of_le hab]

lemma intervalProb_ae {a b : ℝ} {p : ℝ → Prop} :
    (∀ᵐ x ∂intervalProb a b, p x) ↔ ∀ᵐ x ∂volume.restrict (Ioc a b), p x := by
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)

lemma integrable_intervalProb {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioc a b)) : Integrable f (intervalProb a b) := by
  exact hf.smul_measure (ENNReal.inv_ne_top.2 (ENNReal.ofReal_ne_zero_iff.2 (sub_pos.2 hab)))

lemma intervalProb_integral_subinterval {a b c d K : ℝ} (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hdb : d ≤ b) (hK : 0 ≤ K) (hlen : b-a ≤ K*(d-c))
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc a b))
    (hf0 : ∀ᵐ x ∂volume.restrict (Ioc a b), 0 ≤ f x) :
    (∫ x, f x ∂intervalProb c d) ≤ K*(∫ x, f x ∂intervalProb a b) := by
  have hsub : Ioc c d ⊆ Ioc a b := fun x hx => ⟨hac.trans_lt hx.1,hx.2.trans hdb⟩
  have him : (∫ x in c..d, f x) ≤ ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_of_le hcd.le,intervalIntegral.integral_of_le hab.le]
    exact setIntegral_mono_set hf hf0 (ae_of_all _ (fun x hx => hsub hx))
  have hnon : 0 ≤ ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact integral_nonneg_of_ae hf0
  have hcoef : (d-c)⁻¹ ≤ K*(b-a)⁻¹ := by
    rw [← one_div,← div_eq_mul_inv]
    exact (div_le_div_iff₀ (sub_pos.2 hcd) (sub_pos.2 hab)).2 (by simpa using hlen)
  rw [integral_intervalProb hcd.le,integral_intervalProb hab.le]
  calc
    _ ≤ (d-c)⁻¹*(∫ x in a..b, f x) := mul_le_mul_of_nonneg_left him (inv_nonneg.2 (sub_nonneg.2 hcd.le))
    _ ≤ (K*(b-a)⁻¹)*(∫ x in a..b, f x) :=
      mul_le_mul hcoef le_rfl hnon (mul_nonneg hK (inv_nonneg.2 (sub_nonneg.2 hab.le)))
    _ = _ := by ring

lemma acl_line_L1 {a b : ℝ} {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntegrableOn g (Ioc a b))
    (hbound : ∀ᵐ s ∂volume.restrict (Ioc a b), ‖deriv f s‖ ≤ g s)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f y-f x| ≤ ∫ s in a..b, g s := by
  have hab := hx.1.trans hx.2
  have hD : IntegrableOn (deriv f) (Ioc a b) :=
    hg.mono' (aestronglyMeasurable_deriv f _) hbound
  suffices ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      |f y-f x| ≤ ∫ s in a..b, g s by
    rcases le_total x y with h | h
    · exact this x hx y hy h
    · simpa only [abs_sub_comm] using this y hy x hx h
  intro x hx y hy hxy
  have hsub : Ioc x y ⊆ Ioc a b := fun s hs => ⟨hx.1.trans_lt hs.1,hs.2.trans hy.2⟩
  have hfac : AbsolutelyContinuousOnInterval f x y := hf.mono
    (by simpa only [uIcc_of_le hab,uIcc_of_le hxy] using Icc_subset_Icc hx.1 hy.2)
  calc
    _ = ‖∫ s in x..y, deriv f s‖ := by rw [hfac.integral_deriv_eq_sub,Real.norm_eq_abs]
    _ ≤ ∫ s in x..y, ‖deriv f s‖ := intervalIntegral.norm_integral_le_integral_norm hxy
    _ ≤ ∫ s in a..b, ‖deriv f s‖ := by
      rw [intervalIntegral.integral_of_le hxy,intervalIntegral.integral_of_le hab]
      exact setIntegral_mono_set hD.norm (ae_of_all _ (fun s => norm_nonneg _))
        (ae_of_all _ (fun s hs => hsub hs))
    _ ≤ ∫ s in a..b, g s := by
      rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
      exact integral_mono_ae hD.norm hg hbound

theorem rectangle_poincare_L1 {a b c d a' b' c' d' K : ℝ}
    (hab : a < b) (hcd : c < d) (hab' : a' < b') (hcd' : c' < d')
    (haa : a ≤ a') (hbb : b' ≤ b) (hcc : c ≤ c') (hdd : d' ≤ d)
    (hK : 0 ≤ K) (hlen : d-c ≤ K*(d'-c'))
    {u g : ℝ × ℝ → ℝ}
    (hu : Integrable u ((intervalProb a b).prod (intervalProb c d)))
    (hu' : Integrable u ((intervalProb a' b').prod (intervalProb c' d')))
    (hg : Integrable g ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))))
    (hg0 : ∀ p, 0 ≤ g p)
    (hhor : ∀ᵐ y ∂volume.restrict (Ioc c d),
      AbsolutelyContinuousOnInterval (fun x => u (x,y)) a b ∧
      ∀ᵐ x ∂volume.restrict (Ioc a b), ‖deriv (fun s => u (s,y)) x‖ ≤ g (x,y))
    (hver : ∀ᵐ x ∂volume.restrict (Ioc a b),
      AbsolutelyContinuousOnInterval (fun y => u (x,y)) c d ∧
      ∀ᵐ y ∂volume.restrict (Ioc c d), ‖deriv (fun s => u (x,s)) y‖ ≤ g (x,y)) :
    |(∫ p, u p ∂(intervalProb a' b').prod (intervalProb c' d'))-
      (∫ p, u p ∂(intervalProb a b).prod (intervalProb c d))| ≤
      (K/(d-c)+1/(b-a))*(∫ p, g p ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  let := intervalProb_isProbability hab
  let := intervalProb_isProbability hcd
  let := intervalProb_isProbability hab'
  let := intervalProb_isProbability hcd'
  let R := fun y => ∫ x in a..b, g (x,y)
  let C := fun x => ∫ y in c..d, g (x,y)
  have hRi : IntegrableOn R (Ioc c d) := by
    simpa only [IntegrableOn,R,intervalIntegral.integral_of_le hab.le] using hg.integral_prod_right
  have hCi : IntegrableOn C (Ioc a b) := by
    simpa only [IntegrableOn,C,intervalIntegral.integral_of_le hcd.le] using hg.integral_prod_left
  have subX : Ioc a' b' ⊆ Ioc a b := fun x hx => ⟨haa.trans_lt hx.1,hx.2.trans hbb⟩
  have subY : Ioc c' d' ⊆ Ioc c d := fun y hy => ⟨hcc.trans_lt hy.1,hy.2.trans hdd⟩
  have hH : ∀ᵐ y ∂intervalProb c' d', ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b,
      |u (x₁,y)-u (x₂,y)| ≤ R y := by
    apply intervalProb_ae.2
    apply (ae_mono (Measure.restrict_mono_set volume subY))
    filter_upwards [hhor,hg.prod_left_ae] with y hy hgy
    intro x₁ hx₁ x₂ hx₂
    exact acl_line_L1 hy.1 hgy hy.2 hx₂ hx₁
  have hV : ∀ᵐ x ∂intervalProb a b, ∀ y₁ ∈ Icc c d, ∀ y₂ ∈ Icc c d,
      |u (x,y₁)-u (x,y₂)| ≤ C x := by
    apply intervalProb_ae.2
    filter_upwards [hver,hg.prod_right_ae] with x hx hgx
    intro y₁ hy₁ y₂ hy₂
    exact acl_line_L1 hx.1 hgx hx.2 hy₂ hy₁
  have hmem {l r : ℝ} : ∀ᵐ x ∂intervalProb l r, x ∈ Icc l r :=
    intervalProb_ae.2 ((ae_restrict_mem measurableSet_Ioc).mono (fun x hx => Ioc_subset_Icc_self hx))
  have hb : ∀ᵐ p ∂(intervalProb a' b').prod (intervalProb c' d'),
      ∀ᵐ q ∂(intervalProb a b).prod (intervalProb c d), |u p-u q| ≤ R p.2+C q.1 := by
    have hpX := (Measure.quasiMeasurePreserving_fst (μ := intervalProb a' b') (ν := intervalProb c' d')).tendsto_ae.eventually (hmem (l := a') (r := b'))
    have hpY := (Measure.quasiMeasurePreserving_snd (μ := intervalProb a' b') (ν := intervalProb c' d')).tendsto_ae.eventually (hmem (l := c') (r := d'))
    have hpH := (Measure.quasiMeasurePreserving_snd (μ := intervalProb a' b') (ν := intervalProb c' d')).tendsto_ae.eventually hH
    have hqX := (Measure.quasiMeasurePreserving_fst (μ := intervalProb a b) (ν := intervalProb c d)).tendsto_ae.eventually (hmem (l := a) (r := b))
    have hqY := (Measure.quasiMeasurePreserving_snd (μ := intervalProb a b) (ν := intervalProb c d)).tendsto_ae.eventually (hmem (l := c) (r := d))
    have hqV := (Measure.quasiMeasurePreserving_fst (μ := intervalProb a b) (ν := intervalProb c d)).tendsto_ae.eventually hV
    filter_upwards [hpX,hpY,hpH] with p hpx hpy hph
    filter_upwards [hqX,hqY,hqV] with q hqx hqy hqv
    have hpx' : p.1 ∈ Icc a b := ⟨haa.trans hpx.1,hpx.2.trans hbb⟩
    have hpy' : p.2 ∈ Icc c d := ⟨hcc.trans hpy.1,hpy.2.trans hdd⟩
    exact (abs_sub_le (u p) (u (q.1,p.2)) (u q)).trans
      (add_le_add (hph p.1 hpx' q.1 hqx) (hqv p.2 hpy' q.2 hqy))
  have hmain := rectangle_mean_L1_bound hu hu'
    (integrable_intervalProb hcd' (hRi.mono_set subY)) (integrable_intervalProb hab hCi) hb
  have hR0 : ∀ y, 0 ≤ R y := fun y => intervalIntegral.integral_nonneg hab.le (fun x hx => hg0 (x,y))
  have hRbound := intervalProb_integral_subinterval hcd hcd' hcc hdd hK hlen hRi (ae_of_all _ hR0)
  have hRE : (∫ y, R y ∂intervalProb c d) =
      (d-c)⁻¹*(∫ p, g p ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [integral_intervalProb hcd.le]
    congr 1
    rw [intervalIntegral.integral_of_le hcd.le,integral_prod_symm _ hg]
    simp only [R,intervalIntegral.integral_of_le hab.le]
  have hCE : (∫ x, C x ∂intervalProb a b) =
      (b-a)⁻¹*(∫ p, g p ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [integral_intervalProb hab.le]
    congr 1
    rw [intervalIntegral.integral_of_le hab.le,integral_prod _ hg]
    simp only [C,intervalIntegral.integral_of_le hcd.le]
  calc
    _ ≤ (∫ y, R y ∂intervalProb c' d')+(∫ x, C x ∂intervalProb a b) := hmain
    _ ≤ K*(∫ y, R y ∂intervalProb c d)+(∫ x, C x ∂intervalProb a b) := add_le_add hRbound le_rfl
    _ = _ := by rw [hRE,hCE]; ring

lemma stripPotential_horizontal_AC {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hr : 0 < r) (q : ℂ) {φ : ℝ}
    (hφ : φ ∈ Ioo (0:ℝ) Real.pi) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun v : ℝ => stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I)) a b := by
  let c := fun v : ℝ => (v:ℂ)+(φ:ℂ)*Complex.I
  have hc : ContDiff ℝ 1 c := Complex.ofRealCLM.contDiff.add contDiff_const
  have hmap : MapsTo c (uIcc a b) openStrip := by
    intro v hv
    simpa [c,openStrip] using hφ
  have hdiff : DifferentiableOn ℂ (F ∘ Complex.exp) openStrip := by
    intro z hz
    exact ((hF _ (exp_mem_halfPlane hz)).differentiableAt.comp z
      (Complex.differentiable_exp z)).differentiableWithinAt
  have hG : ContDiffOn ℝ 1 ((F ∘ Complex.exp) ∘ c) (uIcc a b) :=
    ((hdiff.contDiffOn openStrip_isOpen).restrict_scalars ℝ).comp hc.contDiffOn hmap
  apply acl_congr (radialTruncation_along_C1_AC hr H q hG)
  intro v hv
  exact ((stripPotential_interior_eq hext H r q (hmap hv)).self_of_nhds).symm

lemma stripPotential_horizontal_deriv {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) (v : ℝ) {φ : ℝ}
    (hφ : φ ∈ Ioo (0:ℝ) Real.pi) :
    deriv (fun s : ℝ => stripPotential H q r Fbar ((s:ℂ)+(φ:ℂ)*Complex.I)) v =
      fderiv ℝ (stripPotential H q r Fbar) ((v:ℂ)+(φ:ℂ)*Complex.I) 1 := by
  let c := fun s : ℝ => (s:ℂ)+(φ:ℂ)*Complex.I
  have hmem : c v ∈ openStrip := by simpa [c,openStrip] using hφ
  have he := stripPotential_interior_eq hext H r q hmem
  have hc : HasDerivAt c 1 v := by
    simpa [c,Complex.ofRealCLM] using Complex.ofRealCLM.hasDerivAt.add_const ((φ:ℂ)*Complex.I)
  have hd := radialTruncation_directional_deriv hH hr q (c := c) (t := v) (d := 1)
    ((hF _ (exp_mem_halfPlane hmem)).differentiableAt.comp _ (Complex.differentiable_exp _)) hc
  rw [← he.fderiv_eq] at hd
  exact (he.comp_tendsto hc.continuousAt).deriv_eq.trans hd

lemma stripPotential_vertical_AC {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ) (v : ℝ)
    (hE : MemLp (fun φ : ℝ => ‖fderiv ℝ (stripPotential H q r Fbar)
      ((v:ℂ)+(φ:ℂ)*Complex.I)‖) 2 (volume.restrict (Ioc (0:ℝ) Real.pi))) :
    AbsolutelyContinuousOnInterval
      (fun φ : ℝ => stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I)) 0 Real.pi := by
  let f := fun φ : ℝ => stripPotential H q r Fbar ((v:ℂ)+(φ:ℂ)*Complex.I)
  have hb : ∀ᵐ ψ ∂volume.restrict (Ioc (0:ℝ) Real.pi), ‖deriv f ψ‖ ≤
      ‖fderiv ℝ (stripPotential H q r Fbar) ((v:ℂ)+(ψ:ℂ)*Complex.I)‖ := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ψ hψ
    rw [stripPotential_vertical_deriv hF hext hH hr q v hψ]
    simpa only [Complex.norm_I,mul_one] using
      (fderiv ℝ (stripPotential H q r Fbar) ((v:ℂ)+(ψ:ℂ)*Complex.I)).le_opNorm Complex.I
  have hD := hE.mono' (aestronglyMeasurable_deriv f _) hb
  have hc : ContinuousOn f (Icc 0 Real.pi) :=
    (stripPotential_continuous hH hr q hcont).comp
      (continuous_const.add (Complex.continuous_ofReal.mul_const _)).continuousOn
      (by intro ψ hψ; simpa [closedStrip] using hψ)
  exact acl_of_interior Real.pi_pos hc
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).2 (hD.integrable (by norm_num)))
    (fun a ha b hb => stripPotential_vertical_AC_interior hF hext hr q v ha hb)

theorem strip_coordinate_ACL {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {a b c d : ℝ} (hcd : c < d) (hc : 0 ≤ c) (hd : d ≤ Real.pi) :
    (∀ᵐ y : ℝ ∂volume.restrict (Ioc c d),
      AbsolutelyContinuousOnInterval
        (fun x : ℝ => stripPotential H q r Fbar ((x:ℂ)+(y:ℂ)*Complex.I)) a b ∧
      ∀ᵐ x : ℝ ∂volume.restrict (Ioc a b),
        ‖deriv (fun s : ℝ => stripPotential H q r Fbar ((s:ℂ)+(y:ℂ)*Complex.I)) x‖ ≤
          ‖fderiv ℝ (stripPotential H q r Fbar) ((x:ℂ)+(y:ℂ)*Complex.I)‖) ∧
    (∀ᵐ x : ℝ ∂volume.restrict (Ioc a b),
      AbsolutelyContinuousOnInterval
        (fun y : ℝ => stripPotential H q r Fbar ((x:ℂ)+(y:ℂ)*Complex.I)) c d ∧
      ∀ᵐ y : ℝ ∂volume.restrict (Ioc c d),
        ‖deriv (fun s : ℝ => stripPotential H q r Fbar ((x:ℂ)+(s:ℂ)*Complex.I)) y‖ ≤
          ‖fderiv ℝ (stripPotential H q r Fbar) ((x:ℂ)+(y:ℂ)*Complex.I)‖) := by
  have hy : ∀ᵐ y : ℝ ∂volume.restrict (Ioc c d), y ∈ Ioo (0:ℝ) Real.pi := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact ⟨hc.trans_lt hy.1,hy.2.trans_le hd⟩
  constructor
  · filter_upwards [hy] with y hy
    refine ⟨stripPotential_horizontal_AC hF hext hr q hy a b,ae_of_all _ (fun x => ?_)⟩
    rw [stripPotential_horizontal_deriv hF hext hH.le hr q x hy]
    simpa only [norm_one,mul_one] using
      (fderiv ℝ (stripPotential H q r Fbar) ((x:ℂ)+(y:ℂ)*Complex.I)).le_opNorm 1
  · filter_upwards [(strip_vertical_memLp_ae hF hinj hext hH hr q).filter_mono
      (ae_mono Measure.restrict_le_self)] with x hx
    refine ⟨(stripPotential_vertical_AC hF hext hcont hH.le hr q x hx).mono ?_,?_⟩
    · rw [uIcc_of_le hcd.le,uIcc_of_le Real.pi_pos.le]
      exact fun y hy => ⟨hc.trans hy.1,hy.2.trans hd⟩
    · filter_upwards [hy] with y hy
      rw [stripPotential_vertical_deriv hF hext hH.le hr q x hy]
      simpa only [Complex.norm_I,mul_one] using
        (fderiv ℝ (stripPotential H q r Fbar) ((x:ℂ)+(y:ℂ)*Complex.I)).le_opNorm Complex.I

lemma strip_gradient_rect_memLp {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    (a b : ℝ) {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ Real.pi) :
    MemLp (fun p : ℝ × ℝ => ‖fderiv ℝ (stripPotential H q r Fbar)
      ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖) 2
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  have hi := strip_energy_integrable_prod hF hinj hext hH hr q
  rw [restrict_Ioo_eq_restrict_Ioc] at hi
  have hm : (volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d)) ≤
      volume.prod (volume.restrict (Ioc (0:ℝ) Real.pi)) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono_set _
      (fun y hy => ⟨hc.trans_lt hy.1,hy.2.trans hd⟩))
  apply (memLp_two_iff_integrable_sq ?_).2 (hi.mono_measure hm)
  exact ((measurable_fderiv ℝ _).comp
    ((Complex.measurable_ofReal.comp measurable_fst).add
      ((Complex.measurable_ofReal.comp measurable_snd).mul_const _))).norm.aestronglyMeasurable

lemma strip_potential_rect_integrable {Fbar : ℂ → OnePoint ℂ}
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ)
    (a b : ℝ) {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ Real.pi) :
    Integrable (fun p : ℝ × ℝ => stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  have hh : ContinuousOn (fun p : ℝ × ℝ => stripPotential H q r Fbar
      ((p.1:ℂ)+(p.2:ℂ)*Complex.I)) ((Icc a b).prod (Icc c d)) :=
    (stripPotential_continuous hH hr q hcont).comp
      ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul_const _)).continuousOn
      (by intro p hp; simpa [closedStrip] using And.intro (hc.trans hp.2.1) (hp.2.2.trans hd))
  have hi := hh.integrableOn_compact (μ := volume) (isCompact_Icc.prod isCompact_Icc)
  have hj := hi.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict] at hj
  exact hj

lemma strip_potential_mean_integrable {Fbar : ℂ → OnePoint ℂ}
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) (hc : 0 ≤ c) (hd : d ≤ Real.pi) :
    Integrable (fun p : ℝ × ℝ => stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I))
      ((intervalProb a b).prod (intervalProb c d)) := by
  rw [intervalProb,intervalProb,Measure.prod_smul_left,Measure.prod_smul_right]
  exact ((strip_potential_rect_integrable hcont hH hr q a b hc hd).smul_measure
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_ne_zero_iff.2 (sub_pos.2 hcd)))).smul_measure
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_ne_zero_iff.2 (sub_pos.2 hab)))

theorem strip_rectangle_poincare {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {a b c d a' b' c' d' K : ℝ}
    (hab : a < b) (hcd : c < d) (hab' : a' < b') (hcd' : c' < d')
    (hlo : 0 ≤ c) (hhi : d ≤ Real.pi)
    (haa : a ≤ a') (hbb : b' ≤ b) (hcc : c ≤ c') (hdd : d' ≤ d)
    (hK : 0 ≤ K) (hlen : d-c ≤ K*(d'-c')) :
    |(∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb a' b').prod (intervalProb c' d'))-
      (∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb a b).prod (intervalProb c d))| ≤
      (K/(d-c)+1/(b-a))*(∫ p : ℝ × ℝ, ‖fderiv ℝ (stripPotential H q r Fbar)
        ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖
          ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  have hh := strip_coordinate_ACL hF hinj hext hcont hH hr q (a := a) (b := b) hcd hlo hhi
  exact rectangle_poincare_L1 hab hcd hab' hcd' haa hbb hcc hdd hK hlen
    (strip_potential_mean_integrable hcont hH.le hr q hab hcd hlo hhi)
    (strip_potential_mean_integrable hcont hH.le hr q hab' hcd' (hlo.trans hcc) (hdd.trans hhi))
    ((strip_gradient_rect_memLp hF hinj hext hH hr q a b hlo hhi).integrable (by norm_num))
    (fun _ => norm_nonneg _) hh.1 hh.2

lemma dyadic_subsum_le {a : ℕ → ℝ} (ha : ∀ j, a j = 0 ∨ a j = (2:ℝ)^j) (n : ℕ) :
    ∑ j ∈ Finset.range n, a j ≤ (2:ℝ)^n-1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,pow_succ]
    rcases ha n with h | h
    · rw [h,add_zero]
      linarith [pow_pos (by norm_num : (0:ℝ) < 2) n]
    · rw [h]
      linarith

lemma dyadic_subsum_square {a : ℕ → ℝ} (ha : ∀ j, a j = 0 ∨ a j = (2:ℝ)^j) (n : ℕ) :
    (∑ j ∈ Finset.range n, a j)^2 ≤ 3*∑ j ∈ Finset.range n, (a j)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    rcases ha n with h | h
    · simpa only [h,add_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using ih
    · rw [h]
      have hb := dyadic_subsum_le ha n
      have hp : 0 ≤ (2:ℝ)^n := by positivity
      have hm := mul_nonneg hp (show 0 ≤ (2:ℝ)^n-∑ j ∈ Finset.range n, a j by linarith)
      nlinarith

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

def dyadicKernel (Q : ℕ → Set α) (n : ℕ) (x : α) : ℝ :=
  ∑ j ∈ Finset.range n, (Q j).indicator (fun _ => (2:ℝ)^j) x

lemma dyadicKernel_memLp {Q : ℕ → Set α} (hQ : ∀ j, MeasurableSet (Q j)) (n : ℕ) :
    MemLp (dyadicKernel Q n) 2 μ := by
  have hh := memLp_finsetSum' (μ := μ) (p := (2:ℝ≥0∞)) (Finset.range n)
    (fun j hj => (memLp_const ((2:ℝ)^j)).indicator (hQ j))
  have he : dyadicKernel Q n = ∑ j ∈ Finset.range n, (Q j).indicator (fun _ => (2:ℝ)^j) := by
    funext x
    simp only [dyadicKernel,Finset.sum_apply]
  rw [he]
  exact hh

lemma dyadicKernel_square_energy {Q : ℕ → Set α} (hQ : ∀ j, MeasurableSet (Q j))
    {V : ℝ} (n : ℕ) (harea : ∀ j < n, ((2:ℝ)^j)^2*μ.real (Q j) ≤ V) :
    (∫ x, (dyadicKernel Q n x)^2 ∂μ) ≤ 3*(n:ℝ)*V := by
  have hpoint (x : α) : (dyadicKernel Q n x)^2 ≤
      3*∑ j ∈ Finset.range n, ((Q j).indicator (fun _ => (2:ℝ)^j) x)^2 := by
    apply dyadic_subsum_square
    intro j
    by_cases hx : x ∈ Q j
    · right; exact indicator_of_mem hx _
    · left; exact indicator_of_notMem hx _
  have hi (j : ℕ) : Integrable (fun x => ((Q j).indicator (fun _ => (2:ℝ)^j) x)^2) μ :=
    ((memLp_const ((2:ℝ)^j) : MemLp _ 2 μ).indicator (hQ j)).integrable_sq
  calc
    _ ≤ ∫ x, 3*∑ j ∈ Finset.range n, ((Q j).indicator (fun _ => (2:ℝ)^j) x)^2 ∂μ :=
      integral_mono (dyadicKernel_memLp hQ n).integrable_sq
        ((integrable_finsetSum _ (fun j hj => hi j)).const_mul 3) hpoint
    _ = 3*∑ j ∈ Finset.range n, ((2:ℝ)^j)^2*μ.real (Q j) := by
      rw [integral_const_mul,integral_finsetSum _ (fun j hj => hi j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have he : (fun x => ((Q j).indicator (fun _ => (2:ℝ)^j) x)^2) =
          (Q j).indicator (fun _ => ((2:ℝ)^j)^2) := by
        funext x
        by_cases hx : x ∈ Q j <;> simp [hx]
      rw [he,integral_indicator (hQ j),integral_const]
      simp [Measure.real,smul_eq_mul,mul_comm]
    _ ≤ 3*(n:ℝ)*V := by
      have hh := Finset.sum_le_sum (s := Finset.range n)
        (fun j hj => harea j (Finset.mem_range.1 hj))
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc] using
        mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 3)

end Measure

end SLEExactGauge.RectangleEnergy

end

end

end OAI
