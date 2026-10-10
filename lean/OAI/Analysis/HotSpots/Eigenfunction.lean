import OAI.Analysis.HotSpots.ClosedSolution

namespace OAI

section RadialHelmholtzUniqueness





noncomputable section
open Set
namespace StrictHotSpots.Helmholtz

lemma radial_ode_zero {f g : ℝ → ℂ} {a : ℂ} {R : ℝ}
    (hR : 0 < R) (hsmall : ‖a‖*R^2 < 1)
    (hf : ContinuousOn f (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (hdf : ∀ r ∈ Icc 0 R, HasDerivAt f (g r) r)
    (hprod : ∀ r ∈ Icc 0 R,
      HasDerivAt (fun r : ℝ => (r:ℂ)*g r) (-(r:ℂ)*a*f r) r)
    (hf0 : f 0=0) (hg0 : g 0=0) : ∀ r ∈ Icc 0 R, f r=0 := by
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) R).Nonempty from ⟨0,le_rfl,hR.le⟩) hf.norm
  let M := ‖f x‖
  have hM : 0 ≤ M := norm_nonneg _
  have hbound (t : ℝ) (ht : t ∈ Icc 0 R) : ‖f t‖ ≤ M := hmax ht
  have hgbound (r : ℝ) (hr : r ∈ Icc 0 R) : ‖g r‖ ≤ ‖a‖*R*M := by
    by_cases hr0 : r=0
    · rw [hr0,hg0,norm_zero]
      positivity
    have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hh := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f:=fun t : ℝ => (t:ℂ)*g t) (f':=fun t => -(t:ℂ)*a*f t)
      (C:=‖a‖*r*M) (a:=0) (b:=r)
      ((Complex.continuous_ofReal.continuousOn.mul hg).mono
        (Icc_subset_Icc le_rfl hr.2))
      (fun t ht => (hprod t ⟨ht.1,ht.2.le.trans hr.2⟩).hasDerivWithinAt)
      (fun t ht => by
        rw [norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg ht.1]
        calc
          t*‖a‖*‖f t‖ ≤ r*‖a‖*M := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _))
              (hbound t ⟨ht.1,ht.2.le.trans hr.2⟩) (norm_nonneg _) (by positivity)
          _ = ‖a‖*r*M := by ring)
      r ⟨hrp.le,le_rfl⟩
    simp only [Complex.ofReal_zero,zero_mul,sub_zero,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hrp.le] at hh
    have hgg : ‖g r‖ ≤ ‖a‖*r*M := by nlinarith
    exact hgg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr.2 (norm_nonneg _)) hM)
  have hh := norm_image_sub_le_of_norm_deriv_right_le_segment hf
    (fun t ht => (hdf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hgbound t (Ico_subset_Icc_self ht)) x hx
  rw [hf0,sub_zero,sub_zero] at hh
  have hzero : M=0 := by
    have hm : M ≤ (‖a‖*R^2)*M := by
      calc
        M ≤ (‖a‖*R*M)*x := hh
        _ ≤ (‖a‖*R*M)*R := mul_le_mul_of_nonneg_left hx.2 (by positivity)
        _ = (‖a‖*R^2)*M := by ring
    nlinarith
  intro r hr
  exact norm_eq_zero.mp (le_antisymm ((hbound r hr).trans_eq hzero) (norm_nonneg _))

end StrictHotSpots.Helmholtz
end
end RadialHelmholtzUniqueness

section ActualInteriorEigenSupport



section HelmholtzCircleMeanActualInteriorLayer
noncomputable section
open Set MeasureTheory Metric _root_.Complex _root_.OAI.Complex Filter
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz

lemma radial_regular_global {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (a : ℂ) :
    Continuous (Function.uncurry (radial u a)) ∧
    Continuous (Function.uncurry (radialDeriv u a)) ∧
    Continuous (Function.uncurry (radialSecond u a)) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by decide)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ u)) := h1.continuous_fderiv (by norm_num)
  have hp := continuous_jointCircleMap a
  have hd : Continuous (fun p : ℝ × ℝ => direction p.2) := continuous_direction.comp continuous_snd
  exact ⟨hu.continuous.comp hp,
    ((hu.continuous_fderiv (by simp)).comp hp).clm_apply hd,
    ((h2.comp hp).clm_apply hd).clm_apply hd⟩

lemma hasDerivAt_coeff_global {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (a : ℂ) (n : ℤ) (r : ℝ) :
    HasDerivAt (coeff u a n) (coeffDeriv u a n r) r := by
  have h := radial_regular_global hu a
  exact hasDerivAt_intervalIntegral_of_continuousOn
    (F := fun t θ => weight n θ * radial u a t θ)
    (F' := fun t θ => weight n θ * radialDeriv u a t θ) isOpen_univ (mem_univ _) 0 (2*Real.pi)
    (((continuous_weight n).comp continuous_snd).mul h.1).continuousOn
    (((continuous_weight n).comp continuous_snd).mul h.2.1).continuousOn
    (fun t _ θ => (hasDerivAt_radial (hu.differentiable (by simp) _)).const_mul _)

lemma hasDerivAt_coeffDeriv_global {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (a : ℂ) (n : ℤ) (r : ℝ) :
    HasDerivAt (coeffDeriv u a n) (coeffSecond u a n r) r := by
  have h := radial_regular_global hu a
  exact hasDerivAt_intervalIntegral_of_continuousOn
    (F := fun t θ => weight n θ * radialDeriv u a t θ)
    (F' := fun t θ => weight n θ * radialSecond u a t θ) isOpen_univ (mem_univ _) 0 (2*Real.pi)
    (((continuous_weight n).comp continuous_snd).mul h.2.1).continuousOn
    (((continuous_weight n).comp continuous_snd).mul h.2.2).continuousOn
    (fun t _ θ => (hasDerivAt_radialDeriv
      ((hu.fderiv_right (m:=1) (by decide)).differentiable (by norm_num) _)).const_mul _)

lemma weight_zero (θ : ℝ) : weight 0 θ = 1 := by simp [weight]

lemma coeff_center (u : ℂ → ℂ) (a : ℂ) :
    coeff u a 0 0 = (2*Real.pi) • u a := by
  simp [coeff,weight_zero,radial,circleMap]

lemma integral_direction : (∫ θ in (0:ℝ)..2*Real.pi, direction θ) = 0 := by
  have he : direction = fun θ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ)*I := by
    funext θ
    simp [direction,circleMap,Complex.exp_mul_I]
  rw [he,intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal,integral_cos,integral_sin]
    simp
  · exact (Complex.continuous_ofReal.comp Real.continuous_cos).intervalIntegrable _ _
  · exact ((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const).intervalIntegrable _ _

lemma coeffDeriv_center (u : ℂ → ℂ) (a : ℂ) : coeffDeriv u a 0 0 = 0 := by
  simp only [coeffDeriv,weight_zero,one_mul,radialDeriv,circleMap,Complex.ofReal_zero,
    zero_mul,add_zero]
  rw [(fderiv ℝ u a).intervalIntegral_comp_comm (continuous_direction.intervalIntegrable _ _),
    integral_direction,map_zero]

lemma coeff_radial_ode {u : ℂ → ℂ} {a : ℂ} {R μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hPDE : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    {r : ℝ} (hr : r ∈ Ico 0 R) :
    HasDerivAt (fun r : ℝ => (r:ℂ)*coeffDeriv u a 0 r)
      (-(r:ℂ)*(μ:ℂ)*coeff u a 0 r) r := by
  have h := ((hasDerivAt_id r).ofReal_comp).mul (hasDerivAt_coeffDeriv_global hu a 0 r)
  have he : (1:ℂ)*coeffDeriv u a 0 r + (r:ℂ)*coeffSecond u a 0 r =
      -(r:ℂ)*(μ:ℂ)*coeff u a 0 r := by
    by_cases hr0 : r=0
    · simp [hr0,coeffDeriv_center]
    have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    rw [coeff_ode 0 (fun _ _ => (hu.of_le (by decide : (2:ℕ∞ω) ≤ ∞)).contDiffAt)
      hPDE ⟨hrp,hr.2⟩]
    simp only [Int.cast_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,zero_sub]
    have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hr0
    field_simp
    ring
  simpa only [id_eq,Complex.ofReal_one,he] using! h



lemma circle_mean_comparison {u v : ℂ → ℂ} {a b : ℂ} {R ρ μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hvp : ∀ z ∈ ball b R, (Δ v) z = -μ • v z)
    (hρ : 0 < ρ) (hρR : ρ < R) (hsmall : |μ| * ρ^2 < 1)
    (hc : u a = v b) : ∀ r ∈ Icc 0 ρ, coeff u a 0 r = coeff v b 0 r := by
  let f := fun r => coeff u a 0 r - coeff v b 0 r
  let g := fun r => coeffDeriv u a 0 r - coeffDeriv v b 0 r
  have hdf (r : ℝ) : HasDerivAt f (g r) r :=
    (hasDerivAt_coeff_global hu a 0 r).sub (hasDerivAt_coeff_global hv b 0 r)
  have hdg (r : ℝ) : DifferentiableAt ℝ g r :=
    ((hasDerivAt_coeffDeriv_global hu a 0 r).sub
      (hasDerivAt_coeffDeriv_global hv b 0 r)).differentiableAt
  have hz := radial_ode_zero (a:=(μ:ℂ)) hρ (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hsmall)
    (continuous_iff_continuousAt.mpr (fun r => (hdf r).continuousAt)).continuousOn
    (continuous_iff_continuousAt.mpr (fun r => (hdg r).continuousAt)).continuousOn
    (fun r _ => hdf r) (fun r hr => ?_) (by simp [f,coeff_center,hc])
    (by simp [g,coeffDeriv_center])
  · intro r hr
    exact sub_eq_zero.mp (hz r hr)
  · have hrR : r ∈ Ico 0 R := ⟨hr.1,hr.2.trans_lt hρR⟩
    have h := (coeff_radial_ode hu hup hrR).sub (coeff_radial_ode hv hvp hrR)
    simpa only [f,g,mul_sub,Pi.sub_apply] using! h

end StrictHotSpots.Helmholtz
end
end HelmholtzCircleMeanActualInteriorLayer


section HelmholtzRadialActualInteriorLayer
noncomputable section
open Set MeasureTheory Metric _root_.Complex _root_.OAI.Complex Filter Function Real
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz


def referenceReal (k : ℝ) (z : ℂ) : ℝ := Real.cos (k*z.re)
def referenceSin (k : ℝ) (z : ℂ) : ℝ := Real.sin (k*z.re)
def reference (μ : ℝ) (z : ℂ) : ℂ := referenceReal (Real.sqrt μ) z

lemma referenceReal_smooth (k : ℝ) : ContDiff ℝ ∞ (referenceReal k) :=
  ((k • Complex.reCLM).contDiff).cos
lemma referenceSin_smooth (k : ℝ) : ContDiff ℝ ∞ (referenceSin k) :=
  ((k • Complex.reCLM).contDiff).sin
lemma reference_smooth (μ : ℝ) : ContDiff ℝ ∞ (reference μ) :=
  Complex.ofRealCLM.contDiff.comp (referenceReal_smooth _)

lemma fderiv_referenceReal (k : ℝ) (z : ℂ) :
    fderiv ℝ (referenceReal k) z = (-referenceSin k z) • (k • Complex.reCLM) := by
  exact ((k • Complex.reCLM).hasFDerivAt.cos).fderiv
lemma fderiv_referenceSin (k : ℝ) (z : ℂ) :
    fderiv ℝ (referenceSin k) z = (referenceReal k z) • (k • Complex.reCLM) := by
  exact ((k • Complex.reCLM).hasFDerivAt.sin).fderiv

lemma laplacian_referenceReal (k : ℝ) (z : ℂ) :
    Δ (referenceReal k) z = -(k^2)*referenceReal k z := by
  have hc : fderiv ℝ (referenceReal k) = fun y => (-referenceSin k y) • (k • Complex.reCLM) :=
    funext (fderiv_referenceReal k)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [hc, fderiv_smul_const (c := fun y : ℂ => -(referenceSin k y))
      ((referenceSin_smooth k).differentiable (by simp) z).neg (k • Complex.reCLM),
    fderiv_fun_neg,fderiv_referenceSin]
  simp
  ring

lemma laplacian_reference {μ : ℝ} (hμ : 0 ≤ μ) (z : ℂ) :
    Δ (reference μ) z = -μ • reference μ z := by
  have hh : ContDiffAt ℝ 2 (referenceReal (Real.sqrt μ)) z := ((referenceReal_smooth (Real.sqrt μ)).of_le (show (2:ℕ∞ω) ≤ ∞ by decide)).contDiffAt
  change Δ (Complex.ofRealCLM ∘ referenceReal (Real.sqrt μ)) z = _
  rw [hh.laplacian_CLM_comp_left,Function.comp_apply,laplacian_referenceReal,Real.sq_sqrt hμ]
  simp [reference,real_smul]

lemma reference_zero (μ : ℝ) : reference μ 0 = 1 := by
  simp [reference,referenceReal]

lemma coeff_zero_eq_average (f : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    coeff f a 0 r = (2*Real.pi) • circleAverage f a r := by
  simp only [coeff,weight_zero,one_mul,radial,circleAverage_def,smul_smul,
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),one_smul]

lemma mean_eq_reference {u : ℂ → ℂ} {a : ℂ} {R ρ μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hμ : 0 ≤ μ)
    (hup : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hρ : 0 < ρ) (hρR : ρ < R) (hsmall : |μ| * ρ^2 < 1)
    {r : ℝ} (hr : r ∈ Icc 0 ρ) :
    circleAverage u a r = u a * circleAverage (reference μ) 0 r := by
  have hv : ContDiff ℝ ∞ (fun z => u a * reference μ z) := contDiff_const.mul (reference_smooth μ)
  have hvp (z : ℂ) (_hz : z ∈ ball (0:ℂ) R) :
      Δ (fun z => u a * reference μ z) z = -μ • (u a * reference μ z) := by
    change Δ (u a • reference μ) z = _
    rw [InnerProductSpace.laplacian_smul _ ((reference_smooth μ).of_le
      (show (2:ℕ∞ω) ≤ ∞ by decide)).contDiffAt,laplacian_reference hμ]
    simp only [smul_eq_mul,real_smul,Complex.ofReal_neg]
    ring
  have he := circle_mean_comparison hu hv hup hvp hρ hρR hsmall
    (by simp only [reference_zero,mul_one]) r hr
  have hcoeff : coeff (fun z => u a * reference μ z) 0 0 r = u a * coeff (reference μ) 0 0 r := by
    simp only [coeff,weight_zero,one_mul,radial,intervalIntegral.integral_const_mul]
  rw [hcoeff,coeff_zero_eq_average,coeff_zero_eq_average,real_smul,real_smul] at he
  have hpi : ((2*Real.pi : ℝ):ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  apply mul_left_cancel₀ hpi
  linear_combination he

open StrictHotSpots.Weyl



lemma radial_average_helmholtz {u : ℂ → ℂ} {a : ℂ} {R ρ μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hμ : 0 ≤ μ)
    (hup : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hρ : 0 < ρ) (hρR : ρ < R) (hsmall : |μ| * ρ^2 < 1) :
    (∫ z, radialBump ρ z • u (a-z)) =
      u a * (∫ z, radialBump ρ z • reference μ (-z)) := by
  rw [← integral_const_mul]
  rw [← Complex.integral_comp_polarCoord_symm,← Complex.integral_comp_polarCoord_symm]
  change (∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (radialBump ρ (Complex.polarCoord.symm p) • u (a-Complex.polarCoord.symm p))) =
    ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • (u a * (radialBump ρ (Complex.polarCoord.symm p) • reference μ (-Complex.polarCoord.symm p)))
  have hi₂ := (polar_bump_integrable hρ (reference_smooth μ).continuous (0:ℂ)).const_mul (u a)
  have hi₂' : IntegrableOn (fun p : ℝ × ℝ => p.1 •
      (u a * (radialBump ρ (Complex.polarCoord.symm p) • reference μ (-Complex.polarCoord.symm p))))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
    simpa only [zero_sub,mul_smul_comm] using! hi₂
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using polar_bump_integrable hρ hu.continuous a),
    setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using hi₂')]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hpol : ∀ θ, -Complex.polarCoord.symm (r,θ) = circleMap 0 (-r) θ := by
    intro θ
    simpa only [zero_sub] using polar_circle 0 r θ
  simp_rw [radialBump_polar,polar_circle,hpol,integral_smul,integral_const_mul]
  simp_rw [integral_smul]
  by_cases hrρ : r < ρ
  · rw [angle_integral,angle_integral,circleAverage_neg_radius,circleAverage_neg_radius,
      mean_eq_reference hu hμ hup hρ hρR hsmall ⟨hr.le,hrρ.le⟩]
    simp only [mul_smul_comm]
  · have hzero : expNegInvGlue (ρ^2-r^2) = 0 := by
      apply expNegInvGlue.zero_of_nonpos
      have hr' : ρ ≤ r := le_of_not_gt hrρ
      nlinarith
    simp only [hzero,zero_smul,smul_zero,mul_zero]

end StrictHotSpots.Helmholtz
end
end HelmholtzRadialActualInteriorLayer


section HelmholtzRegularityActualInteriorLayer
noncomputable section
open Set MeasureTheory Metric _root_.Complex _root_.OAI.Complex Function Filter ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Helmholtz
open StrictHotSpots.Weyl

lemma regularizing_coefficient_pos {μ ρ : ℝ} (hρ : 0 < ρ)
    (hpos : ∀ z ∈ ball (0:ℂ) ρ, 0 < referenceReal (Real.sqrt μ) (-z)) :
    0 < ∫ z, radialBump ρ z * referenceReal (Real.sqrt μ) (-z) := by
  have hc : Continuous (fun z => radialBump ρ z * referenceReal (Real.sqrt μ) (-z)) :=
    (radialBump_contDiff ρ).continuous.mul ((referenceReal_smooth _).continuous.comp continuous_neg)
  have hcomp : HasCompactSupport (fun z => radialBump ρ z * referenceReal (Real.sqrt μ) (-z)) :=
    (radialBump_compact hρ.le).mul_right
  have hn (z : ℂ) : 0 ≤ radialBump ρ z * referenceReal (Real.sqrt μ) (-z) := by
    by_cases hz : z ∈ ball (0:ℂ) ρ
    · exact mul_nonneg (expNegInvGlue.nonneg _) (hpos z hz).le
    · have hz' : ρ ≤ ‖z‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hz
      rw [radialBump_zero hρ.le hz',zero_mul]
  apply (integral_pos_iff_support_of_nonneg hn (hc.integrable_of_hasCompactSupport hcomp)).mpr
  apply (measure_ball_pos volume (0:ℂ) hρ).trans_le
  apply measure_mono
  intro z hz
  apply ne_of_gt
  apply mul_pos _ (hpos z hz)
  apply expNegInvGlue.pos_of_pos
  have hz' : ‖z‖ < ρ := by simpa only [mem_ball,dist_zero_right] using hz
  nlinarith [norm_nonneg z]

lemma exists_regularizing_radius (μ : ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ |μ| * ρ^2 < 1 ∧
      0 < ∫ z, radialBump ρ z * referenceReal (Real.sqrt μ) (-z) := by
  have hw : ∀ᶠ z : ℂ in 𝓝 0, 0 < referenceReal (Real.sqrt μ) (-z) := by
    apply ((referenceReal_smooth _).continuous.comp continuous_neg).continuousAt.eventually
      (eventually_gt_nhds (show (0:ℝ) < referenceReal (Real.sqrt μ) (-(0:ℂ)) by
        simp [referenceReal]))
  obtain ⟨r,hr,hrw⟩ := Metric.eventually_nhds_iff.mp hw
  have he : ∀ᶠ s : ℝ in 𝓝 0, |μ| * s^2 < 1 := by
    have hc : Continuous (fun s : ℝ => |μ| * s^2) := by fun_prop
    exact hc.continuousAt.eventually (eventually_lt_nhds (by simp))
  obtain ⟨ε,hε,hεw⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨ρ,hρ,hρmin⟩ := exists_between (lt_min hR (lt_min hr hε))
  have hρR := hρmin.trans_le (min_le_left _ _)
  have hρr := hρmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρε := hρmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hρ,hρR,hεw (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hρ] using hρε),?_⟩
  apply regularizing_coefficient_pos hρ
  intro z hz
  apply hrw
  exact (mem_ball.mp hz).trans hρr

lemma regularizing_coefficient_eq (μ ρ : ℝ) :
    (∫ z, radialBump ρ z • reference μ (-z)) =
      ((∫ z, radialBump ρ z * referenceReal (Real.sqrt μ) (-z) : ℝ) : ℂ) := by
  simp only [reference,real_smul,← Complex.ofReal_mul,integral_complex_ofReal]



theorem local_representative {u : ℂ → ℂ} {a : ℂ} {R μ : ℝ}
    (hu : LocallyIntegrable u volume) (hR : 0 < R) (hμ : 0 ≤ μ)
    (hpde : WeakEquation (ball a R) μ u) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      ∀ᵐ x ∂volume, x ∈ ball a (R/4) → f x = u x := by
  obtain ⟨ρ,hρ,hρR,hsmall,hc⟩ := exists_regularizing_radius μ (show 0 < R/4 by positivity)
  let φ := radialBump ρ
  let c : ℝ := ∫ z, φ z * referenceReal (Real.sqrt μ) (-z)
  have hc' : 0 < c := hc
  have hφ : ContDiff ℝ ∞ φ := radialBump_contDiff _
  have hcφ : HasCompactSupport φ := radialBump_compact hρ.le
  let v := u ⋆[smulFlip] φ
  have hv : ContDiff ℝ ∞ v := hcφ.contDiff_convolution_right _ hu hφ
  refine ⟨fun x => c⁻¹ • v x,?_,?_⟩
  · simpa only [Pi.smul_apply] using! (contDiff_const (c := c⁻¹)).smul hv
  filter_upwards [smoothen_tendsto hu,smoothen_tendsto hv.continuous.locallyIntegrable] with x hx hxv
  intro hxa
  have he : ∀ᶠ n in atTop, smoothen v n x = c • smoothen u n x := by
    filter_upwards [(tendsto_order.1 mollifier_radius_tendsto).2 (R/2) (by positivity)] with n hn
    have hh : ∀ z ∈ ball x (R/4), Δ (smoothen u n) z = -μ • smoothen u n z := by
      intro z hz
      apply smoothen_PDE hu hpde n
      rw [mem_ball] at hz hxa ⊢
      have ht := dist_triangle z x a
      linarith
    calc
      smoothen v n x = (smoothen u n ⋆[smulFlip] φ) x :=
        (congrFun (convolution_shuffle hu (mollifier n).continuous_normed
          (mollifier n).hasCompactSupport_normed hφ.continuous hcφ) x).symm
      _ = c • smoothen u n x := by
        rw [← convolution_flip]
        change (∫ z, radialBump ρ z • smoothen u n (x-z)) = _
        rw [radial_average_helmholtz (smoothen_contDiff hu n) hμ hh hρ hρR hsmall,
          regularizing_coefficient_eq]
        exact mul_comm _ _
  have ht : Tendsto (fun n => smoothen v n x) atTop (𝓝 (c • u x)) :=
    (hx.const_smul c).congr' (he.mono (fun _ h => h.symm))
  have hvx : v x = c • u x := tendsto_nhds_unique hxv ht
  rw [hvx,smul_smul,inv_mul_cancel₀ hc'.ne',one_smul]



theorem representative {u : ℂ → ℂ} {Ω : Set ℂ} (ho : IsOpen Ω)
    (hu : LocallyIntegrable u volume) {μ : ℝ} (hμ : 0 ≤ μ) (hpde : WeakEquation Ω μ u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume, x ∈ Ω → f x = u x := by
  classical
  have hball (x : Ω) : ∃ R : ℝ, 0 < R ∧ ball (x:ℂ) R ⊆ Ω :=
    Metric.isOpen_iff.mp ho x x.property
  choose R hR hRΩ using hball
  choose f hf hfu using fun x : Ω => local_representative hu (hR x) hμ (hpde.mono (hRΩ x))
  have hsmall (x : Ω) : ball (x:ℂ) (R x/4) ⊆ Ω :=
    (ball_subset_ball (by linarith [hR x])).trans (hRΩ x)
  have heq (x y : Ω) : EqOn (f x) (f y) (ball (x:ℂ) (R x/4) ∩ ball (y:ℂ) (R y/4)) := by
    apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) _ (isOpen_ball.inter isOpen_ball)
      (hf x).continuous.continuousOn (hf y).continuous.continuousOn
    apply (ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).mpr
    filter_upwards [hfu x,hfu y] with z hx hy
    intro hz
    exact (hx hz.1).trans (hy hz.2).symm
  let g : ℂ → ℂ := fun x => if hx : x ∈ Ω then f ⟨x,hx⟩ x else 0
  have hgf (x : Ω) {z : ℂ} (hz : z ∈ ball (x:ℂ) (R x/4)) : g z = f x z := by
    have hzΩ := hsmall x hz
    dsimp only [g]
    rw [dite_eq_left hzΩ]
    exact heq ⟨z,hzΩ⟩ x ⟨mem_ball_self (by linarith [hR ⟨z,hzΩ⟩]),hz⟩
  refine ⟨g,?_,?_⟩
  · intro x hx
    let x' : Ω := ⟨x,hx⟩
    have he : g =ᶠ[𝓝 x] f x' := by
      filter_upwards [ball_mem_nhds x (by linarith [hR x'] : 0 < R x'/4)] with z hz
      exact hgf x' hz
    exact ((hf x').contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
  · obtain ⟨T,hT,hcover⟩ := (IsLindelof.of_coe (s := Ω)).elim_nhds_subcover'
      (fun x hx => ball x (R ⟨x,hx⟩/4)) (fun x hx => ball_mem_nhds x (by linarith [hR ⟨x,hx⟩]))
    have ha : ∀ᵐ z ∂volume, ∀ x ∈ T, z ∈ ball (x:ℂ) (R x/4) → f x z = u z :=
      (eventually_countable_ball hT).mpr (fun x _ => hfu x)
    filter_upwards [ha] with z hz
    intro hzΩ
    obtain ⟨x,hx,hzB⟩ := mem_iUnion₂.mp (hcover hzΩ)
    exact (hgf x hzB).trans (hz x hx hzB)

end StrictHotSpots.Helmholtz
end
end HelmholtzRegularityActualInteriorLayer

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots.Helmholtz

private def coord : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

private def complexExtension (Ω : Set Plane) (u : Plane → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal (Ω.indicator u (coord z))

private lemma complexExtension_integral (Ω : Set Plane) (hΩ : MeasurableSet Ω)
    (u : Plane → ℝ) (ψ : ℂ → ℝ) :
    (∫ z, ψ z • complexExtension Ω u z) =
      Complex.ofReal (∫ x in Ω, u x * ψ (coord.symm x)) := by
  have he : (fun z => ψ z • complexExtension Ω u z) =
      (fun z => ((Ω.indicator (fun x => u x * ψ (coord.symm x))) (coord z) : ℂ)) := by
    funext z
    by_cases hz : coord z ∈ Ω
    · simp [complexExtension,indicator_of_mem hz,Complex.real_smul,mul_comm]
    · simp [complexExtension,indicator_of_notMem hz]
  rw [he,integral_complex_ofReal,
    coord.measurePreserving.integral_comp coord.toHomeomorph.measurableEmbedding,
    integral_indicator hΩ]

private lemma complexExtension_integrable {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : MeasurableSet Ω) (hu : IntegrableOn u Ω) :
    Integrable (complexExtension Ω u) volume := by
  have hi := (integrable_indicator_iff hΩ).mpr hu
  have hj := coord.measurePreserving.integrable_comp_of_integrable hi
  exact Complex.ofRealCLM.integrable_comp hj

private lemma complexExtension_weak {Ω : Set Plane} {μ : ℝ} {u : Plane → ℝ}
    (hΩ : MeasurableSet Ω) (hp : PlaneWeakEquation Ω μ u) :
    Helmholtz.WeakEquation (coord ⁻¹' Ω) μ (complexExtension Ω u) := by
  intro φ hφ hc hs
  have ht : ContDiff ℝ ∞ (φ ∘ coord.symm) :=
    hφ.comp coord.symm.toContinuousLinearEquiv.contDiff
  have htc : HasCompactSupport (φ ∘ coord.symm) := hc.comp_homeomorph coord.symm.toHomeomorph
  have hts : tsupport (φ ∘ coord.symm) ⊆ Ω := by
    change tsupport (φ ∘ coord.symm.toHomeomorph) ⊆ Ω
    rw [tsupport_comp_eq_preimage φ coord.symm.toHomeomorph]
    intro x hx
    have h : coord (coord.symm x) ∈ Ω := hs hx
    simpa only [coord.apply_symm_apply] using h
  have h := hp _ ht htc hts
  simp only [laplacian_comp_linearIsometryEquiv,Function.comp_apply] at h
  rw [complexExtension_integral Ω hΩ u (Δ φ),complexExtension_integral Ω hΩ u φ,h]
  simp



theorem plane_representative {Ω : Set Plane} {u : Plane → ℝ} {μ : ℝ}
    (ho : IsOpen Ω) (hu : IntegrableOn u Ω) (hμ : 0 ≤ μ) (hp : PlaneWeakEquation Ω μ u) :
    ∃ f : Plane → ℝ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume.restrict Ω, f x = u x := by
  obtain ⟨f,hf,hfu⟩ := representative (ho.preimage coord.continuous)
    (complexExtension_integrable ho.measurableSet hu).locallyIntegrable hμ
    (complexExtension_weak ho.measurableSet hp)
  refine ⟨fun x => (f (coord.symm x)).re,?_,?_⟩
  · exact Complex.reCLM.contDiff.comp_contDiffOn (hf.comp
      coord.symm.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun x hx => by simpa only [mem_preimage,coord.apply_symm_apply] using hx))
  · apply (ae_restrict_iff' ho.measurableSet).mpr
    filter_upwards [coord.symm.measurePreserving.quasiMeasurePreserving.ae hfu] with x hx
    intro hxm
    have he := hx (show coord.symm x ∈ coord ⁻¹' Ω by simpa using hxm)
    simpa only [complexExtension,coord.apply_symm_apply,indicator_of_mem hxm,Complex.ofReal_re] using congrArg Complex.re he

end StrictHotSpots.Helmholtz


section WeakEigenRegularityActualInteriorLayer
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace StrictHotSpots



lemma HasH1Gradient.smooth_representative {Ω : Set Plane} {u f : Plane → ℝ} {g : Plane → Plane}
    (ho : IsOpen Ω) (hu : HasH1Gradient Ω u g) (hf : ContDiffOn ℝ ∞ f Ω)
    (he : f =ᵐ[volume.restrict Ω] u) :
    g =ᵐ[volume.restrict Ω] gradient f ∧ HasH1Gradient Ω f (gradient f) := by
  have hfu : HasH1Gradient Ω f g := hu.congr he.symm (EventuallyEq.refl _ _)
  have hd : ContinuousOn (fderiv ℝ f) Ω := hf.continuousOn_fderiv_of_isOpen ho (by simp)
  have hi (e : Plane) : ∀ᵐ x ∂volume.restrict Ω,
      inner ℝ (g x) e - fderiv ℝ f x e = 0 := by
    have hg := (hu.2.1.inner_const (𝕜 := ℝ) e).locallyIntegrable (by norm_num : (1:ENNReal) ≤ 2)
    have hfD : LocallyIntegrableOn (fun x => (fderiv ℝ f x) e) Ω (volume.restrict Ω) :=
      (hd.clm_apply continuousOn_const).locallyIntegrableOn ho.measurableSet
    have ht := ho.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hg.locallyIntegrableOn Ω).sub hfD) (fun φ hφ hc hs => by
        have h1 := hfu.2.2 φ hφ hc hs e
        have h2 := integral_mul_test_fderiv ho hf hφ hc hs e
        have hgi : Integrable (fun x => inner ℝ (g x) e * φ x) (volume.restrict Ω) :=
          (hu.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
        have hdi : Integrable (fun x => fderiv ℝ f x e * φ x) (volume.restrict Ω) :=
          (integrable_mul_test ho (hd.clm_apply continuousOn_const) hφ.continuous hc hs).integrableOn
        simp only [smul_eq_mul,Pi.sub_apply,mul_sub]
        rw [integral_sub (by simpa only [mul_comm] using hgi) (by simpa only [mul_comm] using hdi)]
        simp_rw [mul_comm (φ _)]
        linarith)
    filter_upwards [ht,ae_restrict_mem ho.measurableSet] with x hx hxΩ
    exact hx hxΩ
  have hb : ∀ᵐ x ∂volume.restrict Ω, ∀ i : Fin 2,
      inner ℝ (g x) (EuclideanSpace.basisFun (Fin 2) ℝ i) -
        fderiv ℝ f x (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 :=
    ae_all_iff.mpr fun i => hi _
  have hg : g =ᵐ[volume.restrict Ω] gradient f := by
    filter_upwards [hb] with x hx
    have hz : g x - gradient f x = 0 := by
      ext i
      have hi : inner ℝ (g x - gradient f x) (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 := by
        rw [inner_sub_left,inner_gradient_left]
        exact hx i
      simpa [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_right] using hi
    exact sub_eq_zero.mp hz
  exact ⟨hg,hfu.congr (EventuallyEq.refl _ _) hg⟩




def InInteriorNeumannEigenspace (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u Ω ∧ HasH1Gradient Ω u (gradient u) ∧
    (∫ x in Ω, u x) = 0 ∧
    ∀ (v : Plane → ℝ) (g : Plane → Plane), HasH1Gradient Ω v g →
      (∫ x in Ω, inner ℝ (gradient u x) (g x)) =
        firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x)

lemma InFirstNeumannEigenspace.interior {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) : InInteriorNeumannEigenspace Ω u :=
  ⟨hu.1.mono subset_closure,hu.2⟩



theorem weak_eigenfunction_representative {Ω : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hu : HasH1Gradient Ω u g)
    (hm : (∫ x in Ω, u x) = 0)
    (hp : ∀ v k, HasH1Gradient Ω v k → (∫ x in Ω, inner ℝ (g x) (k x)) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x)) :
    ∃ f : Plane → ℝ, InInteriorNeumannEigenspace Ω f ∧
      f =ᵐ[volume.restrict Ω] u ∧ gradient f =ᵐ[volume.restrict Ω] g := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨f,hf,he⟩ := Helmholtz.plane_representative ho (hu.1.integrable (by norm_num))
    (firstPositiveNeumannValue_nonneg Ω) (planeWeakEquation_of_euler ho hu hp)
  obtain ⟨hg,hH⟩ := hu.smooth_representative ho hf he
  refine ⟨f,⟨hf,hH,(integral_congr_ae he).trans hm,?_⟩,he,hg.symm⟩
  intro v k hv
  calc
    (∫ x in Ω, inner ℝ (gradient f x) (k x)) = ∫ x in Ω, inner ℝ (g x) (k x) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
    _ = firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x) := hp v k hv
    _ = firstPositiveNeumannValue Ω * (∫ x in Ω, f x * v x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]

end StrictHotSpots
end
end WeakEigenRegularityActualInteriorLayer


section HodgeInteriorNullspaceActualInteriorLayer
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots.Hodge





theorem vector_equality_interior {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G)
    (hE : firstPositiveNeumannValue Ω * ‖X‖^2 = ‖F‖^2+‖G‖^2) :
    ∃ v : Plane → ℝ, InInteriorNeumannEigenspace Ω v ∧
      gradient v =ᵐ[volume.restrict Ω] X ∧ G = 0 := by
  obtain ⟨w,hw,hG0,he⟩ := vector_equality ho hne hs hb hμ hl hD X F G hF hG hE
  have heuler : ∀ f g, HasH1Gradient Ω f g →
      (∫ x in Ω, inner ℝ (N1.grad hb w x) (g x)) =
        firstPositiveNeumannValue Ω * (∫ x in Ω, N1.value hb w x * f x) := by
    intro f g hf
    exact minimizer_euler hb
      (ENNReal.toReal_pos (ho.measure_pos volume hne).ne' hb.measure_lt_top.ne)
      (H1.hasH1Gradient w.val) hf (N1.mean_zero hb w)
      (norm_minimizer_integral w.val he)
  obtain ⟨v,hv,_hvw,hvg⟩ := weak_eigenfunction_representative ho hb
    (H1.hasH1Gradient w.val) (N1.mean_zero hb w) heuler
  exact ⟨v,hv,hw ▸ hvg,hG0⟩



theorem vector_equality_interior_pointwise {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G)
    (hE : firstPositiveNeumannValue Ω * ‖X‖^2 = ‖F‖^2+‖G‖^2)
    (Y : Plane → Plane) (hY : ContinuousOn Y Ω) (ha : X =ᵐ[volume.restrict Ω] Y) :
    ∃ v : Plane → ℝ, InInteriorNeumannEigenspace Ω v ∧ EqOn (gradient v) Y Ω := by
  obtain ⟨v,hv,hvg,_⟩ := vector_equality_interior ho hne hs hb hμ hl hD X F G hF hG hE
  refine ⟨v,hv,Measure.eqOn_open_of_ae_eq (hvg.trans ha) ho ?_ hY⟩
  exact (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hv.1.continuousOn_fderiv_of_isOpen ho (by simp))

end StrictHotSpots.Hodge
end
end HodgeInteriorNullspaceActualInteriorLayer
end
end ActualInteriorEigenSupport

section ClosedNullGradient

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include c



theorem lipschitzMultipliedGradient_closed {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) :
    ∃ Y : Plane → Plane, ContinuousOn Y (closure Ω) ∧
      EqOn Y (fun x => b x • closedGradient Ω u x) (frontier Ω) ∧
      (vectorValue (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) : Plane → Plane)
        =ᵐ[volume.restrict Ω] Y := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let w (i : Fin 2) (x : Plane) := fderivWithin ℝ u (closure Ω) x (Hodge.e i)
  have hw (i : Fin 2) : ContDiffOn ℝ ∞ (w i) (closure Ω) :=
    closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)
  let f (i : Fin 2) := c.multiplierTrace hb (w i) (hw i).continuousOn
  obtain ⟨A,hA⟩ : ∃ A : Fin 2 → ℝ, ∀ i s, ‖f i s‖ ≤ A i := by
    have hh (i : Fin 2) : ∃ a : ℝ, ∀ s, ‖f i s‖ ≤ a := by
      obtain ⟨a,_,ha⟩ := boundary_continuous_bound (f i).continuous
      exact ⟨a,ha⟩
    exact Classical.skolem.mp hh
  let S (i : Fin 2) := boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ.le) (f i) (hA i)
  have hSc (i : Fin 2) : ContinuousOn (S i) (closure disk) := by
    obtain ⟨D,hD⟩ := c.multiplierTrace_lipschitz hΩ hb (hw i)
    exact boundaryClosedSolution_continuousOn _ _ (f i) hD (hA i)
  let Y (x : Plane) := S 0 (c.G x) • Hodge.e 0 + S 1 (c.G x) • Hodge.e 1
  have hY : ContinuousOn Y (closure Ω) := by
    exact ((hSc 0).comp c.inverse_lipschitz.continuous.continuousOn c.inverse_maps_closed).smul continuousOn_const |>.add
      (((hSc 1).comp c.inverse_lipschitz.continuous.continuousOn c.inverse_maps_closed).smul continuousOn_const)
  have hae (i : Fin 2) :
      (H1.value (lipschitzMultipliedGradient hΩ hμ hl hD hu hb i) : Plane → ℝ)
        =ᵐ[volume.restrict Ω] (S i) ∘ c.G :=
    c.physical_lipschitzMul_closed_ae hΩ hμ hl hD (hw i) hb (hA i)
  refine ⟨Y,hY,?_,?_⟩
  · intro x hx
    have hxD := c.inverse_maps_boundary hx
    have hnorm : ‖c.G x‖ = 1 := by
      simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
        Metric.mem_sphere,dist_zero_right] using hxD
    let s : Boundary := ⟨c.G x,hnorm⟩
    have he (i : Fin 2) : S i (c.G x) = b x*w i x := by
      change S i s = _
      rw [show S i s = f i s from boundaryClosedSolution_trace _ _ (f i) (hA i) s]
      change b (c.F (c.G x))*w i (c.F (c.G x)) = _
      rw [c.right_inverse x hx.1]
    have hwc (i : Fin 2) : w i x = Hodge.c i (closedGradient Ω u x) := by
      exact InnerProductSpace.toDual_symm_apply.symm
    change S 0 (c.G x) • Hodge.e 0 + S 1 (c.G x) • Hodge.e 1 = _
    rw [he 0,he 1,hwc 0,hwc 1,mul_smul,mul_smul,← smul_add,expand]
  · filter_upwards [vectorValue_ae (lipschitzMultipliedGradient hΩ hμ hl hD hu hb),hae 0,hae 1]
      with x hx h0 h1
    exact hx.trans (congrArg₂ (fun a b : ℝ => a • Hodge.e 0+b • Hodge.e 1) h0 h1)




theorem lipschitzMultipliedGradient_null {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b)
    (hz : vectorForm (firstPositiveNeumannValue Ω)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) = 0) :
    ∃ (v : Plane → ℝ) (Y : Plane → Plane), InInteriorNeumannEigenspace Ω v ∧
      ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧
      EqOn Y (fun x => b x • closedGradient Ω u x) (frontier Ω) := by
  obtain ⟨Y,hY,ht,hae⟩ := c.lipschitzMultipliedGradient_closed hΩ hμ hl hD hu hb
  let X := lipschitzMultipliedGradient hΩ hμ hl hD hu hb
  have hE : firstPositiveNeumannValue Ω * ‖vectorValue X‖^2 =
      ‖divergenceL X‖^2 + ‖curlL X‖^2 := by
    change vectorForm (firstPositiveNeumannValue Ω) X X = 0 at hz
    simp only [vectorForm,real_inner_self_eq_norm_sq] at hz
    linarith
  obtain ⟨v,hv,he⟩ := vector_equality_interior_pointwise hΩ.2.1 hΩ.1 hΩ.2.2.2.1
    hΩ.2.2.1 hμ hl hD (vectorValue X) (divergenceL X) (curlL X)
    (lipschitzMultipliedGradient_tangent hΩ hμ hl hD hu hb)
    (partialL_test_curl hΩ.2.1 X) hE Y (hY.mono subset_closure) hae
  exact ⟨v,Y,hv,hY,he,ht⟩
end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedNullGradient

section ClosedEigenRepresentative

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace Topology NNReal
namespace StrictHotSpots

lemma InInteriorNeumannEigenspace.congr_on {Ω : Set Plane} (ho : IsOpen Ω)
    {u v : Plane → ℝ} (hu : InInteriorNeumannEigenspace Ω u) (he : EqOn u v Ω) :
    InInteriorNeumannEigenspace Ω v := by
  have hg : EqOn (gradient u) (gradient v) Ω := by
    intro x hx
    unfold gradient
    rw [(show u =ᶠ[𝓝 x] v from eventually_of_mem (ho.mem_nhds hx) (fun y hy => he hy)).fderiv_eq]
  have hae : u =ᵐ[volume.restrict Ω] v := (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall he)
  have hgae : gradient u =ᵐ[volume.restrict Ω] gradient v :=
    (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall hg)
  refine ⟨hu.1.congr he.symm,hu.2.1.congr hae hgae,(integral_congr_ae hae).symm.trans hu.2.2.1,?_⟩
  intro f g hf
  calc
    _ = ∫ x in Ω, ⟪gradient u x, g x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [hgae] with x hx
      rw [hx]
    _ = _ := hu.2.2.2 f g hf
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]

namespace Conformal.ClosedDiskChart
open DiskH10
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

include c




theorem exists_lipschitz_potential (hb : Bornology.IsBounded Ω)
    {v : Plane → ℝ} (hv : ContDiffOn ℝ ∞ v Ω) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω) :
    ∃ (V : Plane → ℝ) (A : ℝ≥0), LipschitzWith A V ∧ EqOn v V Ω := by
  obtain ⟨M,hM⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hY
  let A : ℝ≥0 := ⟨c.bound * max M 0,mul_nonneg c.bound_pos.le (le_max_right _ _)⟩
  have hd : ∀ x ∈ disk, DifferentiableAt ℝ (c.pullDatum v) x := fun x hx =>
    ((c.pullDatum_smooth hv).differentiableOn (by simp) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  have hbound (x : Plane) (hx : x ∈ disk) : ‖fderiv ℝ (c.pullDatum v) x‖₊ ≤ A := by
    change ‖fderiv ℝ (c.pullDatum v) x‖ ≤ c.bound * max M 0
    have hn : ‖gradient (c.pullDatum v) x‖ = ‖fderiv ℝ (c.pullDatum v) x‖ := by
      simp only [gradient,LinearIsometryEquiv.norm_map]
    rw [← hn,c.pullDatum_grad_norm (hv.differentiableOn (by simp)) hx,
      he (c.diskMap.map_source hx)]
    exact mul_le_mul (c.bounded_deriv x (c.source_eq.symm ▸ hx))
      ((hM _ (subset_closure (c.diskMap.map_source hx))).trans (le_max_left _ _))
      (norm_nonneg _) c.bound_pos.le
  have hLip : LipschitzOnWith A (c.pullDatum v) disk :=
    (convex_ball (0:Plane) 1).lipschitzOnWith_of_nnnorm_fderiv_le hd hbound
  obtain ⟨f,hf,hef⟩ := hLip.extend_real
  refine ⟨f ∘ c.G,A*c.InvLip,hf.comp c.inverse_lipschitz,?_⟩
  intro x hx
  have hG : c.G x ∈ disk := by
    rw [← c.diskMap_inverse_agrees hx]
    exact c.diskMap.map_target hx
  have hh := hef hG
  change v (c.F (c.G x)) = f (c.G x) at hh
  exact (congrArg v (c.right_inverse x (subset_closure hx))).symm.trans hh



theorem null_eigenfunction_lipschitz (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω) :
    ∃ (V : Plane → ℝ) (A : ℝ≥0), LipschitzWith A V ∧
      InInteriorNeumannEigenspace Ω V ∧ EqOn (gradient V) Y Ω := by
  obtain ⟨V,A,hV,hvV⟩ := c.exists_lipschitz_potential hb hv.1 hY he
  refine ⟨V,A,hV,hv.congr_on ho hvV,?_⟩
  intro x hx
  have hg : gradient V x = gradient v x := by
    unfold gradient
    rw [(show V =ᶠ[𝓝 x] v from eventually_of_mem (ho.mem_nhds hx) (fun y hy => (hvV hy).symm)).fderiv_eq]
  exact hg.trans (he hx)
end Conformal.ClosedDiskChart
end StrictHotSpots
end
end ClosedEigenRepresentative

section PhysicalCoordinateNull

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10 Hodge HilbertMultipliers
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)




theorem coordinate_null_trace (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
    (p : disk) (hz : gradient u (c.F p) = 0) [IsFiniteMeasure c.potential]
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Countable ι]
    (e : HilbertBasis ι ℝ H) {b : Boundary → H} {B : ℝ≥0} (hb : LipschitzWith B b)
    (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel c.densityBound_ne_top
      (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) p s t) :
    ∀ i, ∃ (v : Plane → ℝ) (Y : Plane → Plane), InInteriorNeumannEigenspace Ω v ∧
      ContinuousOn v (closure Ω) ∧ ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧
      ∀ s : Boundary, Y (c.F s) = inner ℝ (e i) (b s) • closedGradient Ω u (c.F s) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hμ := firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne
  obtain ⟨L,_hL,hl,hD⟩ := H10.subcritical hΩ.2.1 hΩ.1 hΩ.2.2.1
  have hext (i : ι) := c.boundary_scalar_extension (coordinate_lipschitz e hb i)
  choose f A hf ht using hext
  let X (i : ι) := lipschitzMultipliedGradient hΩ hμ hl hD hu (hf i)
  let E (i : ι) := vectorForm (firstPositiveNeumannValue Ω) (X i) (X i)
  have hE (i : ι) : E i = (1/2:ℝ)*∫ z : Boundary × Boundary,
      fullBoundaryN c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2 *
      (inner ℝ (e i) (b z.1-b z.2))^2 *
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
    rw [show E i = _ from c.lipschitz_multiplier_kernel hΩ hu hμ hl hD (hf i)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [fullBoundaryN_eq,inner_sub_right,ht]
  have hsum := full_embedding_coordinate_sum c.densityBound_ne_top (c.density_bound hμ.le) e p
    (c.operator_norm_lt_one hΩ.2.2.1 hΩ.1 hμ) hb.continuous hid (c.closedGradient_trace_continuous hΩ hu)
  have hzero := c.boundary_gradient_integral_zero hΩ hu hne p hz
  rw [hzero,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hsum
  have hs : HasSum E 0 := by
    convert hsum using 1
    exact funext hE
  have hzE (i : ι) : E i = 0 := nonnegative_coordinate_energy_zero hs
    (fun i => lipschitzMultipliedGradient_nonneg hΩ hu hμ hl hD (hf i)) i
  intro i
  obtain ⟨v,Y,hv,hY,hvY,hYt⟩ := c.lipschitzMultipliedGradient_null hΩ hμ hl hD hu (hf i) (hzE i)
  obtain ⟨V,D,hV,hVE,hVY⟩ := c.null_eigenfunction_lipschitz hΩ.2.1 hΩ.2.2.1 hv hY hvY
  refine ⟨V,Y,hVE,hV.continuous.continuousOn,hY,hVY,?_⟩
  intro s
  rw [hYt (c.maps_boundary (by simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_sphere_zero_iff_norm] using s.property))]
  simp only [ht]
end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalCoordinateNull

section ClosedEigenAlgebra

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace StrictHotSpots

lemma InInteriorNeumannEigenspace.differentiableAt {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (ho : IsOpen Ω) {x : Plane} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x :=
  ((hu.1 x hx).contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)

lemma gradient_add_at {u v : Plane → ℝ} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    gradient (u+v) x = gradient u x + gradient v x := by
  simp only [gradient,(hu.hasFDerivAt.add hv.hasFDerivAt).fderiv,map_add]

lemma gradient_smul_at {u : Plane → ℝ} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (a : ℝ) : gradient (a • u) x = a • gradient u x := by
  simp only [gradient,(hu.hasFDerivAt.const_smul a).fderiv,map_smul]

lemma InInteriorNeumannEigenspace.add {Ω : Set Plane} {u v : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (hv : InInteriorNeumannEigenspace Ω v)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) : InInteriorNeumannEigenspace Ω (u+v) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hgrad : (gradient u+gradient v) =ᵐ[volume.restrict Ω] gradient (u+v) :=
    (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall fun x hx =>
      (gradient_add_at (hu.differentiableAt ho hx) (hv.differentiableAt ho hx)).symm)
  refine ⟨hu.1.add hv.1,(hu.2.1.add hv.2.1).congr (EventuallyEq.refl _ _) hgrad,?_,?_⟩
  · simp only [Pi.add_apply]
    rw [integral_add]
    · rw [hu.2.2.1,hv.2.2.1,add_zero]
    · exact hu.2.1.1.integrable (by norm_num)
    · exact hv.2.1.1.integrable (by norm_num)
  · intro w g hw
    calc
      (∫ x in Ω, inner ℝ (gradient (u+v) x) (g x)) =
          ∫ x in Ω, inner ℝ (gradient u x + gradient v x) (g x) := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        rw [← hx]
        rfl
      _ = (∫ x in Ω, inner ℝ (gradient u x) (g x)) +
          (∫ x in Ω, inner ℝ (gradient v x) (g x)) := by
        simp only [inner_add_left]
        exact integral_add (integrable_inner_of_memLp hu.2.1.2.1 hw.2.1)
          (integrable_inner_of_memLp hv.2.1.2.1 hw.2.1)
      _ = firstPositiveNeumannValue Ω * (∫ x in Ω, u x*w x) +
          firstPositiveNeumannValue Ω * (∫ x in Ω, v x*w x) := by
        rw [hu.2.2.2 w g hw,hv.2.2.2 w g hw]
      _ = firstPositiveNeumannValue Ω * (∫ x in Ω, (u+v) x*w x) := by
        simp only [Pi.add_apply,add_mul]
        have hiu : Integrable (fun x => u x*w x) (volume.restrict Ω) := hu.2.1.1.integrable_mul hw.1
        have hiv : Integrable (fun x => v x*w x) (volume.restrict Ω) := hv.2.1.1.integrable_mul hw.1
        rw [integral_add hiu hiv,mul_add]

lemma InInteriorNeumannEigenspace.smul {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (ho : IsOpen Ω) (a : ℝ) :
    InInteriorNeumannEigenspace Ω (a • u) := by
  have hgrad : (a • gradient u) =ᵐ[volume.restrict Ω] gradient (a • u) :=
    (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall fun x hx =>
      (gradient_smul_at (hu.differentiableAt ho hx) a).symm)
  refine ⟨hu.1.const_smul a,(hu.2.1.smul a).congr (EventuallyEq.refl _ _) hgrad,?_,?_⟩
  · simp only [Pi.smul_apply,smul_eq_mul,integral_const_mul,hu.2.2.1,mul_zero]
  · intro w g hw
    calc
      (∫ x in Ω, inner ℝ (gradient (a • u) x) (g x)) =
          ∫ x in Ω, inner ℝ (a • gradient u x) (g x) := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        rw [← hx]
        rfl
      _ = a * (∫ x in Ω, inner ℝ (gradient u x) (g x)) := by
        simp only [real_inner_smul_left,integral_const_mul]
      _ = firstPositiveNeumannValue Ω * (∫ x in Ω, (a • u) x*w x) := by
        rw [hu.2.2.2 w g hw]
        simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
        ring

lemma InInteriorNeumannEigenspace.zero (Ω : Set Plane) : InInteriorNeumannEigenspace Ω 0 := by
  have hg : gradient (0 : Plane → ℝ) = 0 := by
    ext x
    simp [gradient]
  refine ⟨contDiffOn_const,?_,by simp,?_⟩
  · rw [hg]
    refine ⟨MemLp.zero,MemLp.zero,?_⟩
    intro φ _ _ _ e
    simp
  · intro w g hw
    simp only [hg,Pi.zero_apply,inner_zero_left,zero_mul,integral_zero,mul_zero]




abbrev ClosedEigenJet (Ω : Set Plane) := ((closure Ω) → ℝ) × ((closure Ω) → Plane)

def closedEigenJet (Ω : Set Plane) (v : Plane → ℝ) (Y : Plane → Plane) : ClosedEigenJet Ω :=
  (fun x => v x, fun x => Y x)




def closedEigenSpace (Ω : Set Plane) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    Submodule ℝ (ClosedEigenJet Ω) where
  carrier := {J | ∃ v Y, InInteriorNeumannEigenspace Ω v ∧ ContinuousOn v (closure Ω) ∧
    ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧ closedEigenJet Ω v Y = J}
  zero_mem' := by
    refine ⟨0,0,InInteriorNeumannEigenspace.zero Ω,continuousOn_const,continuousOn_const,?_,rfl⟩
    intro x hx
    simp [gradient]
  add_mem' := by
    rintro J K ⟨u,Y,hu,huc,hY,huY,rfl⟩ ⟨v,Z,hv,hvc,hZ,hvZ,rfl⟩
    refine ⟨u+v,Y+Z,hu.add hv ho hb,huc.add hvc,hY.add hZ,?_,rfl⟩
    intro x hx
    rw [gradient_add_at (hu.differentiableAt ho hx) (hv.differentiableAt ho hx),huY hx,hvZ hx]
    rfl
  smul_mem' := by
    rintro a J ⟨u,Y,hu,huc,hY,huY,rfl⟩
    refine ⟨a • u,a • Y,hu.smul ho a,huc.const_smul a,hY.const_smul a,?_,rfl⟩
    intro x hx
    rw [gradient_smul_at (hu.differentiableAt ho hx) a,huY hx]
    rfl

lemma closedEigenJet_eq_zero_of_eqOn {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {Y : Plane → Plane} (hv : ContinuousOn v (closure Ω))
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    (hz : EqOn v 0 Ω) : closedEigenJet Ω v Y = 0 := by
  have hzc := hz.of_subset_closure hv continuousOn_const subset_closure (Subset.refl _)
  have hgz : EqOn Y 0 Ω := by
    intro x hx
    rw [← he hx]
    unfold gradient
    rw [(show v =ᶠ[𝓝 x] 0 from eventually_of_mem (ho.mem_nhds hx) (fun y hy => hz hy)).fderiv_eq]
    simp
  have hgc := hgz.of_subset_closure hY continuousOn_const subset_closure (Subset.refl _)
  exact Prod.ext (funext fun x => hzc x.property) (funext fun x => hgc x.property)


lemma closedEigenJet_nonzero_interior {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {Y : Plane → Plane} (hv : ContinuousOn v (closure Ω))
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    (hn : closedEigenJet Ω v Y ≠ 0) : ∃ x ∈ Ω, v x ≠ 0 := by
  by_contra! h
  exact hn (closedEigenJet_eq_zero_of_eqOn ho hv hY he h)

end StrictHotSpots
end
end ClosedEigenAlgebra

end OAI
