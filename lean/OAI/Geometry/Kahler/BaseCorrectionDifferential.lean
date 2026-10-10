import OAI.Geometry.Kahler.BaseCorrectionEstimate

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityCorrectionRaw_direction_bound {k : ℕ} (hk : 0 < k)
    {D F B F₁ B₁ : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (p : Sphere) (ξ v : Base) (hξ : bracket ξ (p:Base) ≠ 0)
    (hdir : ‖bracket v (p:Base)/bracket ξ (p:Base)‖ ≤ D/k)
    (hS : 0 ≤ W (centralPoint p ξ))
    (hT : |phaseDerivative W (centralPoint p ξ)| ≤ k*W (centralPoint p ξ))
    (hTT : |phaseDerivative (phaseDerivative W) (centralPoint p ξ)| ≤ (k:ℝ)^2*W (centralPoint p ξ))
    (hfv : |f (densityHeight k p ξ)| ≤ F) (hbv : |b (densityHeight k p ξ)| ≤ B)
    (hfd : |deriv f (densityHeight k p ξ)| ≤ F₁) (hbd : |deriv b (densityHeight k p ξ)| ≤ B₁) :
    |fderiv ℝ (densityCorrectionRaw k f b W p) ξ v| ≤
      D*Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ)*(4*(F+B)+F₁+B₁) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  let γ : ℝ → Base := fun t => ξ+t • v
  have hγ : HasDerivAt γ v 0 := by simpa [γ] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add ξ
  have hγ0 : γ 0=ξ := by simp [γ]
  let ratio := bracket v (p:Base)/bracket ξ (p:Base)
  have hr : |ratio.re| ≤ D/k := (Complex.abs_re_le_norm _).trans hdir
  have hi : |ratio.im| ≤ D/k := (Complex.abs_im_le_norm _).trans hdir
  have hy := densityHeight_curve_derivative k p hγ (by rwa [hγ0])
  have hSd := centralValue_curve_derivative (hW.differentiable (by simp)) p hγ (by rwa [hγ0])
  have hTd := centralValue_curve_derivative ((phaseDerivative_smooth hW).differentiable (by simp)) p hγ (by rwa [hγ0])
  rw [hγ0] at hy hSd hTd
  have hc : HasDerivAt (fun t => bracket (γ t) (p:Base)) (bracket v (p:Base)) 0 :=
    (((innerSL ℂ (p:Base)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0 hγ
  have hz := (phase_derivative_complex hc (by rwa [hγ0])).pow k
  rw [hγ0] at hz
  have hpn : ‖bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ)‖=1 := by
    simp [Complex.norm_real,div_self (norm_ne_zero_iff.mpr hξ)]
  have hzb : ‖(k:ℂ)*(bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^(k-1) *
      ((Complex.I*ratio.im)*(bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ)))‖ ≤ D := by
    simp only [norm_mul,norm_pow,hpn,one_pow,Complex.norm_natCast,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul,mul_one]
    exact (mul_le_mul_of_nonneg_left hi hk0.le).trans_eq (by field_simp)
  have hyb : |-(k:ℝ)*ratio.re| ≤ D := by
    rw [abs_mul,abs_neg,abs_of_pos hk0]
    exact (mul_le_mul_of_nonneg_left hr hk0.le).trans_eq (by field_simp)
  have hSb : |ratio.im*phaseDerivative W (centralPoint p ξ)| ≤ D*W (centralPoint p ξ) := by
    rw [abs_mul]
    calc
      _ ≤ (D/k)*(k*W (centralPoint p ξ)) := mul_le_mul hi hT (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hTb : |ratio.im*phaseDerivative (phaseDerivative W) (centralPoint p ξ)| ≤ D*k*W (centralPoint p ξ) := by
    rw [abs_mul]
    calc
      _ ≤ (D/k)*((k:ℝ)^2*W (centralPoint p ξ)) := mul_le_mul hi hTT (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hmodel := correctionModel_derivative_bound hk1 hD hF hB hF₁ hB₁ hy hSd hTd hz
    (hf.differentiable (by simp) _ |>.hasDerivAt) (hb.differentiable (by simp) _ |>.hasDerivAt)
    (by simpa only [hγ0] using hS) hyb (by simpa only [hγ0] using hSb)
    (by simpa only [hγ0] using hTb) (by simpa only [hγ0] using hT)
    (by simp only [Pi.pow_apply,hγ0,norm_pow,hpn,one_pow,le_refl]) hzb
    (by simpa only [hγ0] using hfv) (by simpa only [hγ0] using hbv)
    (by simpa only [hγ0] using hfd) (by simpa only [hγ0] using hbd)
  have hlocal : (fun t => densityCorrectionRaw k f b W p (γ t)) =ᶠ[𝓝 0]
      (fun t => correctionModel k f b (densityHeight k p (γ t))
        (W (centralPoint p (γ t))) (phaseDerivative W (centralPoint p (γ t)))
        ((bracket (γ t) (p:Base)/(‖bracket (γ t) (p:Base)‖:ℂ))^k)) := by
    have hne := (hc.continuousAt.eventually_ne (by rwa [hγ0] : bracket (γ 0) (p:Base) ≠ 0))
    filter_upwards [hne] with t ht
    exact densityCorrectionRaw_model hk f b W p ht
  have hraw := (densityCorrectionRaw_smoothAt k hf hb hW p hξ).differentiableAt (by simp)
  rw [← hγ0] at hraw
  have hdr := hraw.hasFDerivAt.comp_hasDerivAt 0 hγ
  rw [hγ0] at hdr
  simp only [Pi.pow_apply] at hmodel
  rw [← hlocal.deriv_eq] at hmodel
  change HasDerivAt (fun t => densityCorrectionRaw k f b W p (γ t)) _ 0 at hdr
  rw [hdr.deriv,hγ0] at hmodel
  exact hmodel

lemma densityCorrection_fderiv_zero {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0)
    (W : Base → ℝ) (p : Sphere) (ξ : Base) (hξ : ¬ Real.exp (-R/k)<‖bracket ξ (p:Base)‖) :
    fderiv ℝ (densityCorrection k R f b W p) ξ=0 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hl : ‖bracket ξ (p:Base)‖ < Real.exp (-E/k) :=
    (le_of_not_gt hξ).trans_lt (Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hk0).mpr (neg_lt_neg hER)))
  have he : densityCorrection k R f b W p =ᶠ[𝓝 ξ] fun _ => 0 := by
    have hc : Continuous (fun z : Base => ‖bracket z (p:Base)‖) := (bracket_analytic (p:Base)).continuous.norm
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hl] with z hz
    exact densityCorrection_zero_low hk htail W p z hz.le
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0:ℝ) ξ).fderiv

lemma densityCorrection_fderiv_raw {k : ℕ} {R : ℝ} (f b : ℝ → ℝ) (W : Base → ℝ)
    (p : Sphere) (ξ : Base) (hξ : Real.exp (-R/k)<‖bracket ξ (p:Base)‖) :
    fderiv ℝ (densityCorrection k R f b W p) ξ=fderiv ℝ (densityCorrectionRaw k f b W p) ξ := by
  have he : densityCorrection k R f b W p =ᶠ[𝓝 ξ] densityCorrectionRaw k f b W p := by
    have hc : Continuous (fun z : Base => ‖bracket z (p:Base)‖) := (bracket_analytic (p:Base)).continuous.norm
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hξ] with z hz
    exact ite_eq_left hz
  exact he.fderiv_eq

end PinchedHartogs.BaseConstruction

end

end OAI
