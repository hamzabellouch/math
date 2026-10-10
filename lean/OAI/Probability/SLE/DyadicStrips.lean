import Mathlib
import OAI.Probability.SLE.RectangleMeans
import OAI.Probability.SLE.SausagePointBound

namespace OAI

/-! Dyadic Strips for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma inv_pow_rpow_two (k : ℕ) (α : ℝ) :
    (1/(2:ℝ)^k)^α = (2:ℝ)^(-α*(k:ℝ)) := by
  rw [one_div,Real.inv_rpow (by positivity)]
  rw [← Real.rpow_natCast (2:ℝ) k,← Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)),
    ← Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ))]
  congr 1
  ring

 

theorem sle_dyadic_strip_rectangle_hit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (j : ℤ) (k : ℕ) (i m : Fin (2^k)) :
    P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' dyadicStripRectangle j k i m} ≤
      ENNReal.ofReal (stripHittingConstant κ *
        (2:ℝ)^(-annularApproachPower κ*(k:ℝ))) := by
  have hk : 0 < (2:ℝ)^k := by positivity
  have hm : (m:ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast m.isLt.le
  have hz : 0 ≤ Real.pi*((m:ℝ)/(2:ℝ)^k) := by positivity
  have hp : Real.pi*((m:ℝ)/(2:ℝ)^k) ≤ Real.pi := by
    exact mul_le_of_le_one_right Real.pi_pos.le ((div_le_one hk).mpr hm)
  have hh := sle_exp_strip_rectangle_hit κ hκ hκ8 γ hSLE
    ((j:ℝ)+(i:ℝ)/(2:ℝ)^k) (Real.pi*((m:ℝ)/(2:ℝ)^k))
    (1/(2:ℝ)^k) hz hp (by positivity)
  simpa only [dyadicStripRectangle,inv_pow_rpow_two] using hh

 

theorem ordinary_sle_strip_hitting_constants
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
        ∀ (j : ℤ) (k : ℕ) (i m : Fin (2^k)),
        P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' dyadicStripRectangle j k i m} ≤
          ENNReal.ofReal (C*(2:ℝ)^(-α*(k:ℝ))) := by
  refine ⟨stripHittingConstant κ,annularApproachPower κ,
    stripHittingConstant_pos κ hκ hκ8,annularApproachPower_pos κ hκ hκ8,?_⟩
  intro Ω _ P γ hγ j k i m
  exact sle_dyadic_strip_rectangle_hit κ hκ hκ8 γ hγ j k i m

end SLEExactGauge
end

section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge

 
def IsStripWeakGradient (u : ℂ → ℝ) (D : ℂ → ℂ) : Prop :=
  MemLp u 2 (volume.restrict openUnitStrip) ∧
  MemLp D 2 (volume.restrict openUnitStrip) ∧
  ∀ φ : ℂ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → tsupport φ ⊆ openUnitStrip →
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) (1:ℂ)) =
      -(∫ z in openUnitStrip, (D z).re * φ z) ∧
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) Complex.I) =
      -(∫ z in openUnitStrip, (D z).im * φ z)

noncomputable def annulusKernel (q : ℂ) (r R : ℝ) (w : ℂ) : ℝ≥0∞ :=
  if r < ‖w-q‖ ∧ ‖w-q‖ < R then ENNReal.ofReal (‖w-q‖^2)⁻¹ else 0

lemma measurable_annulusKernel (q : ℂ) (r R : ℝ) : Measurable (annulusKernel q r R) := by
  unfold annulusKernel
  exact Measurable.ite ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet)
    (ENNReal.measurable_ofReal.comp ((((measurable_id.sub measurable_const).norm).pow_const 2).inv))
    measurable_const

lemma lintegral_inv_Ioo (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    (∫⁻ x in Ioo r R, ENNReal.ofReal x⁻¹) = ENNReal.ofReal (Real.log (R/r)) := by
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc r R) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt (hr.trans_le hx.1))
  have hi : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo r R) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    change (∫ x, x⁻¹ ∂volume.restrict (Ioo r R)) = _
    rw [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hrR.le]
    apply integral_inv
    rw [uIcc_of_le hrR.le]
    intro h
    exact not_le_of_gt hr h.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact inv_nonneg.mpr (hr.trans hx.1).le

lemma annulusKernel_polar (r R : ℝ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    ENNReal.ofReal p.1 * annulusKernel 0 r R (Complex.polarCoord.symm p) =
      (Ioo r R).indicator (fun x : ℝ => ENNReal.ofReal x⁻¹) p.1 := by
  simp only [annulusKernel,sub_zero,Complex.norm_polarCoord_symm,abs_of_pos hp]
  by_cases h : r < p.1 ∧ p.1 < R
  · simp only [Set.indicator,Set.mem_Ioo,ite_eq_left h]
    rw [← ENNReal.ofReal_mul hp.le]
    congr 1
    field_simp
  · simp only [Set.indicator,Set.mem_Ioo,ite_eq_right h,mul_zero]

 

theorem annulusKernel_integral (q : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    (∫⁻ w, annulusKernel q r R w) = ENNReal.ofReal (2*Real.pi*Real.log (R/r)) := by
  have hcenter : (∫⁻ w, annulusKernel q r R w) = ∫⁻ w, annulusKernel 0 r R w := by
    simpa only [annulusKernel,sub_zero] using
      (lintegral_sub_right_eq_self (μ := (volume : Measure ℂ)) (annulusKernel 0 r R) q)
  rw [hcenter,← Complex.lintegral_comp_polarCoord_symm]
  let f : ℝ → ℝ≥0∞ := (Ioo r R).indicator (fun x : ℝ => ENNReal.ofReal x⁻¹)
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp measurable_inv).indicator measurableSet_Ioo
  have he : (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
      annulusKernel 0 r R (Complex.polarCoord.symm p)) =
      ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, f p.1 := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    exact annulusKernel_polar r R p hp.1
  rw [he]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, f p.1 ∂volume.prod volume) = _
  rw [setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ => f p.1) ((hf.comp measurable_fst).aemeasurable)]
  simp only [setLIntegral_const,Real.volume_Ioo,sub_neg_eq_add]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hsub : Ioo r R ⊆ Ioi (0:ℝ) := fun x hx => hr.trans hx.1
  have hfint : (∫⁻ x in Ioi (0:ℝ), f x) = ENNReal.ofReal (Real.log (R/r)) := by
    dsimp [f]
    rw [setLIntegral_indicator measurableSet_Ioo,inter_eq_left.mpr hsub,
      lintegral_inv_Ioo r R hr hrR]
  rw [hfint,← ENNReal.ofReal_mul]
  · congr 1
    ring
  · exact Real.log_nonneg ((one_le_div hr).mpr hrR.le)

lemma complex_deriv_real_det (d : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ).det = ‖d‖^2 := by
  simp [ContinuousLinearMap.det,LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq,Complex.normSq_eq_norm_sq]

 

theorem univalent_annulus_dirichlet_bound {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) (q : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    (∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal (‖deriv F z‖^2) *
      annulusKernel q r R (F z)) ≤ ENNReal.ofReal (2*Real.pi*Real.log (R/r)) := by
  have ho : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  let D : ℂ → ℂ →L[ℝ] ℂ := fun z => (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
  have hD : ∀ z ∈ {z : ℂ | 0 < z.im}, HasFDerivWithinAt F (D z) {z : ℂ | 0 < z.im} z := by
    intro z hz
    exact ((hF.differentiableAt (ho.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume ho.measurableSet hD hi (annulusKernel q r R)
  have hdet (z : ℂ) : |(D z).det| = ‖deriv F z‖^2 := by
    rw [show D z = (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ from rfl,
      complex_deriv_real_det,abs_of_nonneg (sq_nonneg _)]
  simp only [hdet] at he
  rw [← he]
  calc
    _ ≤ ∫⁻ w, annulusKernel q r R w := setLIntegral_le_lintegral _ _
    _ = _ := annulusKernel_integral q r R hr hrR

noncomputable def truncatedConformalLog (F : ℂ → ℂ) (q : ℂ) (r H : ℝ) (z : ℂ) : ℝ :=
  min H (max 0 (Real.log (‖F z-q‖/r)))

lemma lipschitz_clip (H : ℝ) : LipschitzWith 1 (fun x : ℝ => min H (max 0 x)) := by
  have hmax : LipschitzWith 1 (fun x : ℝ => max 0 x) := by
    simpa [Function.comp_def] using lipschitzWith_max.comp ((LipschitzWith.const (0:ℝ)).prodMk LipschitzWith.id)
  simpa [Function.comp_def] using lipschitzWith_min.comp ((LipschitzWith.const H).prodMk hmax)

lemma norm_fderiv_clip_le {v : ℂ → ℝ} {z : ℂ} (hv : ContDiffAt ℝ 1 v z) (H : ℝ) :
    ‖fderiv ℝ (fun w => min H (max 0 (v w))) z‖ ≤ ‖fderiv ℝ v z‖ := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro K hK
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK.le
  obtain ⟨s,hs,hvs⟩ := hv.exists_lipschitzOnWith_of_nnnorm_lt ⟨K,hK0⟩ hK
  have hc := (lipschitz_clip H).comp_lipschitzOnWith hvs
  have he : (1 : ℝ≥0)*⟨K,hK0⟩ = ⟨K,hK0⟩ := one_mul _
  rw [he] at hc
  exact norm_fderiv_le_of_lipschitzOn ℝ hs hc

lemma norm_fderiv_log_norm_div_le {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (q : ℂ) {r : ℝ} (hr : 0 < r)
    (h0 : F z-q ≠ 0) :
    ‖fderiv ℝ (fun w => Real.log (‖F w-q‖/r)) z‖ ≤ ‖deriv F z‖ / ‖F z-q‖ := by
  let A : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
  have hA : HasFDerivAt (fun w => F w-q) A z :=
    ((hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).sub_const q)
  have hn := (differentiableAt_id.norm ℝ h0).hasFDerivAt
  have hnorm : ‖fderiv ℝ (fun w : ℂ => ‖w‖) (F z-q)‖ = 1 :=
    norm_fderiv_norm (differentiableAt_id.norm ℝ h0)
  have hn0 : 0 < ‖F z-q‖ := norm_pos_iff.mpr h0
  have hl := ((hn.comp z hA).log (norm_ne_zero_iff.mpr h0)).sub_const (Real.log r)
  have he : (fun w => Real.log (‖F w-q‖/r)) =ᶠ[𝓝 z]
      (fun w => Real.log ‖F w-q‖ - Real.log r) := by
    filter_upwards [(hA.continuousAt.norm).eventually (Ioi_mem_nhds hn0)] with w hw
    exact Real.log_div (ne_of_gt hw) hr.ne'
  have hd := hl.congr_of_eventuallyEq he
  rw [hd.fderiv,norm_smul,Real.norm_eq_abs]
  simp only [Function.comp_apply,id_eq] at *
  rw [abs_of_pos (inv_pos.mpr hn0)]
  have hAnorm : ‖A‖ = ‖deriv F z‖ := by
    simp [A]
  have hb := (fderiv ℝ (fun w : ℂ => ‖w‖) (F z-q)).opNorm_comp_le A
  rw [hnorm,one_mul,hAnorm] at hb
  simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hn0.le)

lemma truncatedConformalLog_eq_zero {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hl : ‖F z-q‖ ≤ r) :
    truncatedConformalLog F q r H z = 0 := by
  have hb : Real.log (‖F z-q‖/r) ≤ 0 := Real.log_nonpos
    (div_nonneg (norm_nonneg _) hr.le) ((div_le_one hr).mpr hl)
  simp [truncatedConformalLog,max_eq_left hb,min_eq_right hH]

lemma truncatedConformalLog_eq_height {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hr : 0 < r) (hu : Real.exp H*r ≤ ‖F z-q‖) :
    truncatedConformalLog F q r H z = H := by
  have hn : 0 < ‖F z-q‖ := (mul_pos (Real.exp_pos _) hr).trans_le hu
  have hb : H ≤ Real.log (‖F z-q‖/r) :=
    (Real.le_log_iff_exp_le (div_pos hn hr)).mpr ((le_div_iff₀ hr).mpr hu)
  exact min_eq_left (hb.trans (le_max_right _ _))

lemma fderiv_truncated_eq_zero_of_low {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hF : ContinuousAt F z) (hr : 0 < r) (hH : 0 ≤ H) (hl : ‖F z-q‖ < r) :
    fderiv ℝ (truncatedConformalLog F q r H) z = 0 := by
  have he : truncatedConformalLog F q r H =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [((hF.sub_const q).norm).eventually (Iio_mem_nhds hl)] with w hw
    exact truncatedConformalLog_eq_zero hr hH hw.le
  exact ((hasFDerivAt_const (0:ℝ) z).congr_of_eventuallyEq he).fderiv

lemma fderiv_truncated_eq_zero_of_high {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hF : ContinuousAt F z) (hr : 0 < r) (hu : Real.exp H*r < ‖F z-q‖) :
    fderiv ℝ (truncatedConformalLog F q r H) z = 0 := by
  have he : truncatedConformalLog F q r H =ᶠ[𝓝 z] (fun _ => H) := by
    filter_upwards [((hF.sub_const q).norm).eventually (Ioi_mem_nhds hu)] with w hw
    exact truncatedConformalLog_eq_height hr hw.le
  exact ((hasFDerivAt_const H z).congr_of_eventuallyEq he).fderiv

lemma norm_fderiv_truncated_le {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) {z : ℂ} (hz : z ∈ D) (q : ℂ) {r H : ℝ}
    (hr : 0 < r) (h0 : F z-q ≠ 0) :
    ‖fderiv ℝ (truncatedConformalLog F q r H) z‖ ≤ ‖deriv F z‖ / ‖F z-q‖ := by
  have hcF : ContDiffAt ℝ 1 F z := ((hF.analyticAt (hD.mem_nhds hz)).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hv : ContDiffAt ℝ 1 (fun w => Real.log (‖F w-q‖/r)) z :=
    (((hcF.sub contDiffAt_const).norm ℝ h0).div_const r).log
      (div_ne_zero (norm_ne_zero_iff.mpr h0) hr.ne')
  exact (norm_fderiv_clip_le hv H).trans
    (norm_fderiv_log_norm_div_le (hF.differentiableAt (hD.mem_nhds hz)) q hr h0)

 

lemma truncated_log_energy_pointwise {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) {z : ℂ} (hz : z ∈ D) (q : ℂ)
    {r H a b : ℝ} (hr : 0 < r) (hH : 0 < H) (ha : 0 < a) (har : a < r)
    (hRb : Real.exp H*r < b) :
    ENNReal.ofReal (‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2) ≤
      ENNReal.ofReal (‖deriv F z‖^2) * annulusKernel q a b (F z) := by
  have hc := (hF.differentiableAt (hD.mem_nhds hz)).continuousAt
  by_cases hband : a < ‖F z-q‖ ∧ ‖F z-q‖ < b
  · have hn : 0 < ‖F z-q‖ := ha.trans hband.1
    have hb := norm_fderiv_truncated_le hD hF hz q hr (norm_ne_zero_iff.mp hn.ne') (H := H)
    have hs : ‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2 ≤
        ‖deriv F z‖^2 * (‖F z-q‖^2)⁻¹ := by
      calc
        _ ≤ (‖deriv F z‖/‖F z-q‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = _ := by rw [div_pow,div_eq_mul_inv]
    simpa only [annulusKernel,ite_eq_left hband,← ENNReal.ofReal_mul (sq_nonneg _)] using
      ENNReal.ofReal_le_ofReal hs
  · have he : fderiv ℝ (truncatedConformalLog F q r H) z = 0 := by
      rcases not_and_or.mp hband with hl | hu
      · exact fderiv_truncated_eq_zero_of_low hc hr hH.le ((le_of_not_gt hl).trans_lt har)
      · exact fderiv_truncated_eq_zero_of_high hc hr (hRb.trans_le (le_of_not_gt hu))
    simp [he]

lemma truncated_log_lipschitz_near {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) {z : ℂ} (hz : z ∈ D) (q : ℂ) {r H : ℝ}
    (hr : 0 < r) (hH : 0 < H) :
    ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ z ∈ U ∧
      LipschitzOnWith K (truncatedConformalLog F q r H) U := by
  by_cases h0 : F z-q = 0
  · have hn : ‖F z-q‖ < r := by simpa [h0] using hr
    have he := (((hF.differentiableAt (hD.mem_nhds hz)).continuousAt.sub_const q).norm).eventually
      (Iio_mem_nhds hn)
    obtain ⟨U,hU,hUo,hzU⟩ := mem_nhds_iff.mp he
    refine ⟨0,U,hUo,hzU,?_⟩
    intro x hx y hy
    rw [truncatedConformalLog_eq_zero hr hH.le (hU hx).le,
      truncatedConformalLog_eq_zero hr hH.le (hU hy).le]
    simp
  · have hcF : ContDiffAt ℝ 1 F z :=
      ((hF.analyticAt (hD.mem_nhds hz)).restrictScalars (𝕜 := ℝ)).contDiffAt
    have hv : ContDiffAt ℝ 1 (fun w => Real.log (‖F w-q‖/r)) z :=
      (((hcF.sub contDiffAt_const).norm ℝ h0).div_const r).log
        (div_ne_zero (norm_ne_zero_iff.mpr h0) hr.ne')
    let K : ℝ≥0 := ‖fderiv ℝ (fun w => Real.log (‖F w-q‖/r)) z‖₊ + 1
    have hK : ‖fderiv ℝ (fun w => Real.log (‖F w-q‖/r)) z‖₊ < K := by
      dsimp [K]; simp
    obtain ⟨U,hU,hLip⟩ := hv.exists_lipschitzOnWith_of_nnnorm_lt K hK
    refine ⟨1*K,interior U,isOpen_interior,mem_interior_iff_mem_nhds.mpr hU,?_⟩
    exact ((lipschitz_clip H).comp_lipschitzOnWith hLip).mono interior_subset

 
theorem truncated_log_ae_differentiable {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    ∀ᵐ z ∂volume, z ∈ D → DifferentiableAt ℝ (truncatedConformalLog F q r H) z := by
  classical
  have hloc (x : D) := truncated_log_lipschitz_near hD hF x.2 q hr hH
  choose K U hUo hxU hULip using hloc
  have hcov : D ⊆ ⋃ x : D, U x := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hxU ⟨z,hz⟩⟩
  obtain ⟨t,ht,htcov⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover U hUo hcov
  have ha (x : D) : ∀ᵐ z ∂volume, z ∈ U x →
      DifferentiableAt ℝ (truncatedConformalLog F q r H) z := by
    filter_upwards [(hULip x).ae_differentiableWithinAt_of_mem (μ := volume)] with z hz hzU
    exact (hz hzU).differentiableAt ((hUo x).mem_nhds hzU)
  filter_upwards [(ae_ball_iff ht).mpr (fun x _ => ha x)] with z hz hzD
  obtain ⟨x,htx,hzx⟩ := mem_iUnion₂.mp (htcov hzD)
  exact hz x htx hzx

lemma local_lipschitz_weak_derivative {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hlocal : ∀ x ∈ D, ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ x ∈ U ∧ LipschitzOnWith K u U)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ⊤ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ D) (v : ℂ) :
    (∫ z in D, u z * (fderiv ℝ φ z) v) =
      -(∫ z in D, (fderiv ℝ u z) v * φ z) := by
  obtain ⟨S,hSc,hφS,hSD⟩ := exists_compact_between hcφ hD hsφ
  have huS : LocallyLipschitzOn S u := by
    intro x hx
    obtain ⟨K,U,hUo,hxU,hU⟩ := hlocal x (hSD hx)
    exact ⟨K,U,mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hxU),hU⟩
  obtain ⟨K,hK⟩ := huS.exists_lipschitzOnWith_of_compact hSc
  obtain ⟨g,hglip,hug⟩ := hK.extend_real
  obtain ⟨C,hφlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ (by simp)
  have hφdiff : ∀ z, DifferentiableAt ℝ φ z := fun z => (hφ.differentiable (by simp)).differentiableAt
  have ht (z : ℂ) (hz : z ∈ tsupport φ) : u =ᶠ[𝓝 z] g := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hφS hz)] with w hw
    exact hug hw
  have hid := hglip.integral_lineDeriv_mul_eq (μ := volume) hφlip hcφ v
  have hfull : (∫ z, (fderiv ℝ g z) v * φ z) = -(∫ z, g z * (fderiv ℝ φ z) v) := by
    calc
      _ = ∫ z, lineDeriv ℝ g z v * φ z := by
        apply integral_congr_ae
        filter_upwards [hglip.ae_differentiableAt (μ := volume)] with z hz
        rw [hz.lineDeriv_eq_fderiv]
      _ = ∫ z, lineDeriv ℝ φ z (-v) * g z := hid
      _ = _ := by
        simp_rw [(hφdiff _).lineDeriv_eq_fderiv,map_neg,neg_mul,mul_comm _ (g _)]
        rw [integral_neg]
  have he1 : (fun z => u z * (fderiv ℝ φ z) v) = (fun z => g z * (fderiv ℝ φ z) v) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [hug (interior_subset (hφS hz))]
    · simp [fderiv_of_notMem_tsupport ℝ hz]
  have he2 : (fun z => (fderiv ℝ u z) v * φ z) = (fun z => (fderiv ℝ g z) v * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(ht z hz).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hs1 : (∫ z in D, u z * (fderiv ℝ φ z) v) = ∫ z, u z * (fderiv ℝ φ z) v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [fderiv_of_notMem_tsupport ℝ hn]
  have hs2 : (∫ z in D, (fderiv ℝ u z) v * φ z) = ∫ z, (fderiv ℝ u z) v * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [image_eq_zero_of_notMem_tsupport hn]
  rw [hs1,hs2,he1,he2,hfull]
  simp

theorem truncated_log_weak_derivative {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ⊤ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ D) (v : ℂ) :
    (∫ z in D, truncatedConformalLog F q r H z * (fderiv ℝ φ z) v) =
      -(∫ z in D, (fderiv ℝ (truncatedConformalLog F q r H) z) v * φ z) :=
  local_lipschitz_weak_derivative hD (fun _ hx => truncated_log_lipschitz_near hD hF hx q hr hH)
    φ hφ hcφ hsφ v

lemma open_univalent_weighted_area {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (hi : InjOn F D) (q : ℂ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    (∫⁻ z in D, ENNReal.ofReal (‖deriv F z‖^2)*annulusKernel q a b (F z)) ≤
      ENNReal.ofReal (2*Real.pi*Real.log (b/a)) := by
  let B : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
  have hB : ∀ z ∈ D, HasFDerivWithinAt F (B z) D z := by
    intro z hz
    exact ((hF.differentiableAt (hD.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD.measurableSet hB hi (annulusKernel q a b)
  have hdet (z : ℂ) : |(B z).det| = ‖deriv F z‖^2 := by
    rw [show B z = (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ from rfl,
      complex_deriv_real_det,abs_of_nonneg (sq_nonneg _)]
  simp only [hdet] at he
  rw [← he]
  exact (setLIntegral_le_lintegral _ _).trans_eq (annulusKernel_integral q a b ha hab)

 

theorem truncated_log_dirichlet_bound {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (hi : InjOn F D)
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2)) ≤
      ENNReal.ofReal (2*Real.pi*H) := by
  have hbound (ε : ℝ) (hε : 0 < ε) :
      (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2)) ≤
        ENNReal.ofReal (2*Real.pi*(H+2*ε)) := by
    let a := r * Real.exp (-ε)
    let b := Real.exp (H+ε)*r
    have ha : 0 < a := mul_pos hr (Real.exp_pos _)
    have har : a < r := by
      dsimp [a]
      exact (mul_lt_mul_of_pos_left (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε)) hr).trans_eq (mul_one r)
    have hrR : r < Real.exp H*r := by
      simpa using mul_lt_mul_of_pos_right (Real.one_lt_exp_iff.mpr hH) hr
    have hRb : Real.exp H*r < b := by
      exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr (lt_add_of_pos_right _ hε)) hr
    have hab : a < b := har.trans (hrR.trans hRb)
    have hlog : Real.log (b/a) = H+2*ε := by
      have hid : b/a = Real.exp (H+2*ε) := by
        dsimp [a,b]
        rw [show H+2*ε = (H+ε)+ε by ring,Real.exp_add (H+ε) ε,Real.exp_neg]
        field_simp
      rw [hid,Real.log_exp]
    calc
      _ ≤ ∫⁻ z in D, ENNReal.ofReal (‖deriv F z‖^2)*annulusKernel q a b (F z) := by
        apply setLIntegral_mono' hD.measurableSet
        intro z hz
        exact truncated_log_energy_pointwise hD hF hz q hr hH ha har hRb
      _ ≤ ENNReal.ofReal (2*Real.pi*Real.log (b/a)) := open_univalent_weighted_area hD hF hi q a b ha hab
      _ = _ := by rw [hlog]
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (2*Real.pi*(H+2*ε))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (2*Real.pi*H))) := by
    have hc : Continuous (fun ε : ℝ => ENNReal.ofReal (2*Real.pi*(H+2*ε))) := ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with ε hε using hbound ε hε)

lemma measurable_real_gradient (u : ℂ → ℝ) : Measurable (gradient u) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ u)

lemma norm_real_gradient (u : ℂ → ℝ) (z : ℂ) : ‖gradient u z‖ = ‖fderiv ℝ u z‖ := by
  simp [gradient]

theorem truncated_log_sobolev_energy {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (hi : InjOn F D)
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    MemLp (gradient (truncatedConformalLog F q r H)) 2 (volume.restrict D) ∧
    (∫ z in D, ‖gradient (truncatedConformalLog F q r H) z‖^2) ≤ 2*Real.pi*H ∧
    ∀ (φ : ℂ → ℝ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → tsupport φ ⊆ D →
      ((∫ z in D, truncatedConformalLog F q r H z * (fderiv ℝ φ z) (1:ℂ)) =
        -(∫ z in D, (gradient (truncatedConformalLog F q r H) z).re * φ z)) ∧
      ((∫ z in D, truncatedConformalLog F q r H z * (fderiv ℝ φ z) Complex.I) =
        -(∫ z in D, (gradient (truncatedConformalLog F q r H) z).im * φ z)) := by
  let u := truncatedConformalLog F q r H
  have hgm : AEStronglyMeasurable (gradient u) (volume.restrict D) :=
    (measurable_real_gradient u).aestronglyMeasurable
  have hsq : AEStronglyMeasurable (fun z => ‖gradient u z‖^2) (volume.restrict D) := hgm.norm.pow 2
  have hb : (∫⁻ z in D, ENNReal.ofReal (‖gradient u z‖^2)) ≤ ENNReal.ofReal (2*Real.pi*H) := by
    simpa only [norm_real_gradient] using truncated_log_dirichlet_bound hD hF hi q r H hr hH
  have hint : Integrable (fun z => ‖gradient u z‖^2) (volume.restrict D) :=
    (lintegral_ofReal_ne_top_iff_integrable hsq (ae_of_all _ fun z => sq_nonneg _)).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  have henergy : (∫ z in D, ‖gradient u z‖^2) ≤ 2*Real.pi*H := by
    have he := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)
    rw [← he] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*Real.pi*H)).mp hb
  refine ⟨(memLp_two_iff_integrable_sq_norm hgm).mpr hint,henergy,?_⟩
  intro φ hφ hcφ hsφ
  constructor
  · simpa only [real_gradient_re] using truncated_log_weak_derivative hD hF q r H hr hH φ hφ hcφ hsφ (1:ℂ)
  · simpa only [real_gradient_im] using truncated_log_weak_derivative hD hF q r H hr hH φ hφ hcφ hsφ Complex.I

noncomputable def conformalStripLog (F : ℂ → ℂ) (q : ℂ) (r H : ℝ) (z : ℂ) : ℝ :=
  min H (max 0 (Real.log (‖F (Complex.exp z)-q‖/r)))

lemma exp_strip_halfplane : MapsTo Complex.exp {z : ℂ | 0 < z.im ∧ z.im < Real.pi}
    {z : ℂ | 0 < z.im} := by
  intro z hz
  change 0 < (Complex.exp z).im
  rw [Complex.exp_im]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)

lemma exp_injective_strip : InjOn Complex.exp {z : ℂ | 0 < z.im ∧ z.im < Real.pi} := by
  intro x hx y hy hxy
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi
    ((neg_neg_of_pos Real.pi_pos).trans hx.1) hx.2.le
    ((neg_neg_of_pos Real.pi_pos).trans hy.1) hy.2.le hxy

 
theorem conformal_strip_total_energy {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    MemLp (gradient (conformalStripLog F q r H)) 2
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) ∧
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
      ‖gradient (conformalStripLog F q r H) z‖^2) ≤ 2*Real.pi*H ∧
    ∀ (φ : ℂ → ℝ), ContDiff ℝ ⊤ φ → HasCompactSupport φ →
      tsupport φ ⊆ {z : ℂ | 0 < z.im ∧ z.im < Real.pi} →
      ((∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          conformalStripLog F q r H z * (fderiv ℝ φ z) (1:ℂ)) =
        -(∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          (gradient (conformalStripLog F q r H) z).re * φ z)) ∧
      ((∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          conformalStripLog F q r H z * (fderiv ℝ φ z) Complex.I) =
        -(∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          (gradient (conformalStripLog F q r H) z).im * φ z)) := by
  have hS : IsOpen {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hcomp : DifferentiableOn ℂ (F ∘ Complex.exp) {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    hF.comp Complex.differentiable_exp.differentiableOn exp_strip_halfplane
  have hicomp : InjOn (F ∘ Complex.exp) {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    hi.comp exp_injective_strip exp_strip_halfplane
  exact truncated_log_sobolev_energy hS hcomp hicomp q r H hr hH

lemma truncated_log_continuousOn {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    ContinuousOn (truncatedConformalLog F q r H) D := by
  apply LocallyLipschitzOn.continuousOn
  intro z hz
  obtain ⟨K,U,hU,hzU,hlip⟩ := truncated_log_lipschitz_near hD hF hz q hr hH
  exact ⟨K,U,mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hzU),hlip⟩

lemma truncated_log_bounds (F : ℂ → ℂ) (q : ℂ) (r H : ℝ) (hH : 0 ≤ H) (z : ℂ) :
    0 ≤ truncatedConformalLog F q r H z ∧ truncatedConformalLog F q r H z ≤ H := by
  exact ⟨le_min hH (le_max_left _ _),min_le_left _ _⟩

theorem conformal_unit_strip_weak_gradient {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    IsStripWeakGradient (conformalStripLog F q r H)
      (gradient (conformalStripLog F q r H)) ∧
    (∫ z in openUnitStrip, ‖gradient (conformalStripLog F q r H) z‖^2) ≤
      2*Real.pi*H := by
  have hsub : openUnitStrip ⊆ {z : ℂ | 0 < z.im ∧ z.im < Real.pi} := fun z hz => hz.2.2
  have hcm : DifferentiableOn ℂ (F ∘ Complex.exp) openUnitStrip :=
    (hF.comp Complex.differentiable_exp.differentiableOn exp_strip_halfplane).mono hsub
  have hicm : InjOn (F ∘ Complex.exp) openUnitStrip :=
    (hi.comp exp_injective_strip exp_strip_halfplane).mono hsub
  obtain ⟨hgrad,henergy,hweak⟩ :=
    truncated_log_sobolev_energy openUnitStrip_isOpen hcm hicm q r H hr hH
  have : IsFiniteMeasure (volume.restrict openUnitStrip) :=
    isFiniteMeasure_restrict.mpr openUnitStrip_measure_lt_top.ne
  have hu : MemLp (truncatedConformalLog (F ∘ Complex.exp) q r H) 2
      (volume.restrict openUnitStrip) :=
    memLp_of_bounded (ae_of_all _ fun z => truncated_log_bounds _ _ _ _ hH.le z)
      ((truncated_log_continuousOn openUnitStrip_isOpen hcm q r H hr hH).aestronglyMeasurable
        openUnitStrip_isOpen.measurableSet) 2
  exact ⟨⟨hu,hgrad,hweak⟩,henergy⟩

 
noncomputable def sphericalTruncatedLog (q : ℂ) (r H : ℝ) : OnePoint ℂ → ℝ :=
  OnePoint.rec H (fun z => min H (max 0 (Real.log (‖z-q‖/r))))

@[simp] lemma sphericalTruncatedLog_coe (q z : ℂ) (r H : ℝ) :
    sphericalTruncatedLog q r H (z : OnePoint ℂ) =
      truncatedConformalLog id q r H z := rfl

@[simp] lemma sphericalTruncatedLog_infty (q : ℂ) (r H : ℝ) :
    sphericalTruncatedLog q r H OnePoint.infty = H := rfl

lemma sphericalTruncatedLog_continuous (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    Continuous (sphericalTruncatedLog q r H) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  induction x using OnePoint.rec with
  | infty =>
    apply OnePoint.continuousAt_infty.mpr
    intro S hS
    refine ⟨Metric.closedBall q (Real.exp H*r),Metric.isClosed_closedBall,isCompact_closedBall _ _,?_⟩
    intro z hz
    have hb : Real.exp H*r ≤ ‖z-q‖ := by
      rw [mem_compl_iff,Metric.mem_closedBall,dist_eq_norm] at hz
      exact (lt_of_not_ge hz).le
    have he : sphericalTruncatedLog q r H (z : OnePoint ℂ) = H := by
      rw [sphericalTruncatedLog_coe]
      exact truncatedConformalLog_eq_height (F := id) hr hb
    change sphericalTruncatedLog q r H (z : OnePoint ℂ) ∈ S
    rw [he]
    exact mem_of_mem_nhds hS
  | coe z =>
    rw [OnePoint.continuousAt_coe]
    change ContinuousAt (truncatedConformalLog id q r H) z
    have hc := truncated_log_continuousOn isOpen_univ
      (differentiable_id.differentiableOn : DifferentiableOn ℂ id Set.univ) q r H hr hH
    exact (continuousOn_univ.mp hc).continuousAt

 
theorem spherical_strip_log_continuous {Fbar : ℂ → OnePoint ℂ}
    (hFbar : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    ContinuousOn (fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z)))
      {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} := by
  have hmap : MapsTo Complex.exp {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi}
      {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    change 0 ≤ (Complex.exp z).im
    rw [Complex.exp_im]
    exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi hz.1 hz.2)
  exact (sphericalTruncatedLog_continuous q r H hr hH).continuousOn.comp
    (hFbar.comp Complex.continuous_exp.continuousOn hmap) (mapsTo_univ _ _)

 

theorem source_strip_log_regularity {F : ℂ → ℂ} {Fbar : ℂ → OnePoint ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (hbar : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (hext : ∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    let U := fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))
    ContinuousOn U {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} ∧
    (∀ z, 0 ≤ U z ∧ U z ≤ H) ∧
    IsStripWeakGradient U (gradient U) ∧
    MemLp (gradient U) 2 (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) ∧
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi}, ‖gradient U z‖^2) ≤
      2*Real.pi*H := by
  let U := fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))
  let V := conformalStripLog F q r H
  let S := {z : ℂ | 0 < z.im ∧ z.im < Real.pi}
  have hS : IsOpen S := (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)
  have heq : EqOn U V S := by
    intro z hz
    dsimp [U]
    rw [hext (Complex.exp z) (exp_strip_halfplane hz),sphericalTruncatedLog_coe]
    rfl
  have hgeq : EqOn (gradient U) (gradient V) S := by
    intro z hz
    have he : U =ᶠ[𝓝 z] V := by
      filter_upwards [hS.mem_nhds hz] with w hw
      exact heq hw
    simp only [gradient,he.fderiv_eq]
  have heae : U =ᵐ[volume.restrict S] V := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact heq hz
  have hgae : gradient U =ᵐ[volume.restrict S] gradient V := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact hgeq hz
  have hsub : openUnitStrip ⊆ S := fun z hz => hz.2.2
  have heu : U =ᵐ[volume.restrict openUnitStrip] V :=
    heae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hgu : gradient U =ᵐ[volume.restrict openUnitStrip] gradient V :=
    hgae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  obtain ⟨hV,-⟩ := conformal_unit_strip_weak_gradient hF hi q r H hr hH
  obtain ⟨hgrad,henergy,-⟩ := conformal_strip_total_energy hF hi q r H hr hH
  refine ⟨spherical_strip_log_continuous hbar q r H hr hH,?_,?_,(memLp_congr_ae hgae).mpr hgrad,?_⟩
  · intro z
    change 0 ≤ sphericalTruncatedLog q r H (Fbar (Complex.exp z)) ∧
      sphericalTruncatedLog q r H (Fbar (Complex.exp z)) ≤ H
    generalize Fbar (Complex.exp z) = x
    induction x using OnePoint.rec with
    | infty => simpa using And.intro hH.le (le_refl H)
    | coe w => exact truncated_log_bounds id q r H hH.le w
  · refine ⟨(memLp_congr_ae heu).mpr hV.1,(memLp_congr_ae hgu).mpr hV.2.1,?_⟩
    intro φ hφ hc hs
    obtain ⟨hrx,hix⟩ := hV.2.2 φ hφ hc hs
    have h1 : (∫ z in openUnitStrip, U z * (fderiv ℝ φ z) (1:ℂ)) =
        (∫ z in openUnitStrip, V z * (fderiv ℝ φ z) (1:ℂ)) :=
      integral_congr_ae (heu.mono fun z hz => by dsimp only; rw [hz])
    have h2 : (∫ z in openUnitStrip, U z * (fderiv ℝ φ z) Complex.I) =
        (∫ z in openUnitStrip, V z * (fderiv ℝ φ z) Complex.I) :=
      integral_congr_ae (heu.mono fun z hz => by dsimp only; rw [hz])
    have h3 : (∫ z in openUnitStrip, (gradient U z).re * φ z) =
        (∫ z in openUnitStrip, (gradient V z).re * φ z) :=
      integral_congr_ae (hgu.mono fun z hz => by dsimp only; rw [hz])
    have h4 : (∫ z in openUnitStrip, (gradient U z).im * φ z) =
        (∫ z in openUnitStrip, (gradient V z).im * φ z) :=
      integral_congr_ae (hgu.mono fun z hz => by dsimp only; rw [hz])
    exact ⟨h1.trans (hrx.trans (congrArg Neg.neg h3.symm)),
      h2.trans (hix.trans (congrArg Neg.neg h4.symm))⟩
  · calc
      _ = ∫ z in S, ‖gradient V z‖^2 :=
        integral_congr_ae (hgae.mono fun z hz => by dsimp only; rw [hz])
      _ ≤ _ := henergy

 

end SLEExactGauge
end
end

end OAI
