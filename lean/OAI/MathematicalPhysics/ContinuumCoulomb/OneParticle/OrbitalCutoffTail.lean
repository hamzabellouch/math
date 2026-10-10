import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalCutoff
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedGradientMoments

namespace OAI

/-! Quantitative Sobolev tails of the localized orbitals. The 24th
moments give a twelfth-power decay in the H1 norm of the removed tail. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem orbitalCutoff_fderiv_zero {R : ℝ} (hR : 0 < R) (u : PlanarPosition)
    {x : Position} (hx : ‖x-planarCenter u‖ < R) : fderiv ℝ (orbitalCutoff R u) x = 0 := by
  have he : orbitalCutoff R u =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (planarCenter u) R from hx)] with y hy
    exact orbitalCutoff_eq_one hR u hy.le
  rw [he.fderiv_eq]
  exact fderiv_const_apply 1

theorem localized_weighted_coefficient_tail {R A : ℝ} (hR : 0 < R) (_hA : 0 ≤ A)
    (c : Position) {a f : Position → ℝ} (ha : Continuous a) (hf : Continuous f)
    (hbound : ∀ x, |a x| ≤ A) (hzero : ∀ x, ‖x-c‖ < R → a x = 0)
    (hm : Integrable (fun x => ‖x-c‖^24*f x^2)) :
    Integrable (fun x => (a x*f x)^2) ∧
      (∫ x, (a x*f x)^2) ≤ A^2/R^24*(∫ x, ‖x-c‖^24*f x^2) := by
  have hp (x : Position) : (a x*f x)^2 ≤ A^2/R^24*(‖x-c‖^24*f x^2) := by
    by_cases hx : ‖x-c‖ < R
    · rw [hzero x hx,zero_mul,pow_two,zero_mul]
      positivity
    have hd : R ≤ ‖x-c‖ := le_of_not_gt hx
    have hs : (a x)^2 ≤ A^2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (a x)) (hbound x) 2
      simpa only [sq_abs] using h
    have hr : 1 ≤ ‖x-c‖^24/R^24 :=
      (le_div_iff₀ (pow_pos hR 24)).mpr (by simpa only [one_mul] using pow_le_pow_left₀ hR.le hd 24)
    calc
      _ ≤ A^2*f x^2 := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ ≤ (A^2*f x^2)*(‖x-c‖^24/R^24) := le_mul_of_one_le_right (by positivity) hr
      _ = _ := by ring
  have hi : Integrable (fun x => (a x*f x)^2) := by
    apply (hm.const_mul (A^2/R^24)).mono' ((ha.mul hf).pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖(a x*f x)^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hp x
  refine ⟨hi,?_⟩
  have h := integral_mono hi (hm.const_mul (A^2/R^24)) hp
  simpa only [integral_const_mul] using h

theorem continuumLocalizedMode_centered_twentyFourth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x-planarCenter u‖^24*continuumLocalizedMode freq u x^2) := by
  have hi := (localizedDensity_twentyFourth_moment_integrable hfreq).comp_sub_right (planarCenter u)
  simpa only [localizedDensity,continuumLocalizedMode_translate freq u] using hi

private theorem centered_deriv_moment {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) (e : Position) :
    Integrable (fun x : Position => ‖x-planarCenter u‖^24*(fderiv ℝ (continuumLocalizedMode freq u) x e)^2) := by
  have hi := (continuumLocalizedMode_deriv_twentyFourth_moment_integrable hfreq e).comp_sub_right (planarCenter u)
  simpa only [continuumLocalizedMode_deriv_translate freq u] using hi

theorem orbitalCutoff_value_tail {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R) (u : PlanarPosition) :
    Integrable (fun x => ((1-orbitalCutoff R u x)*continuumLocalizedMode freq u x)^2) ∧
      (∫ x, ((1-orbitalCutoff R u x)*continuumLocalizedMode freq u x)^2) ≤
        (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^24 := by
  have h := localized_weighted_coefficient_tail (a := fun x => 1-orbitalCutoff R u x) hR (show (0:ℝ) ≤ 1 by norm_num) (planarCenter u)
    (continuous_const.sub (orbitalCutoff_smooth R u).continuous) (continuumLocalizedMode_C7 freq u).continuous
    (fun x => by rw [abs_of_nonneg (sub_nonneg.mpr (orbitalCutoff_le_one R u x))]; linarith [orbitalCutoff_nonnegative R u x])
    (fun x hx => by rw [orbitalCutoff_eq_one hR u hx.le,sub_self]) (continuumLocalizedMode_centered_twentyFourth_moment_integrable hfreq u)
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_translate freq u]
  rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => ‖x‖^24*continuumLocalizedMode freq 0 x^2) (planarCenter u)]
  ring

theorem orbitalCutoff_deriv_tail {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ (u : PlanarPosition) (e : Position),
      Integrable (fun x => (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2) ∧
      (∫ x, (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2) ≤
        (B*‖e‖)^2/R^24*(∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) := by
  obtain ⟨B,hB,hb⟩ := orbitalCutoff_jets_bounded
  refine ⟨B,hB,?_⟩
  intro R hR u e
  have hR0 : 0 < R := by linarith
  have hbound (x : Position) : |fderiv ℝ (orbitalCutoff R u) x e| ≤ B*‖e‖ := by
    have hd := hb R hR u 1 (by norm_num) x
    rw [norm_iteratedFDeriv_one] at hd
    exact ((fderiv ℝ (orbitalCutoff R u) x).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg e))
  have h := localized_weighted_coefficient_tail hR0 (show 0 ≤ B*‖e‖ by positivity) (planarCenter u)
    (((orbitalCutoff_smooth R u).continuous_fderiv (by simp)).clm_apply continuous_const)
    (continuumLocalizedMode_C7 freq u).continuous hbound
    (fun x hx => by rw [orbitalCutoff_fderiv_zero hR0 u hx]; rfl) (continuumLocalizedMode_centered_twentyFourth_moment_integrable hfreq u)
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_translate freq u]
  rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => ‖x‖^24*continuumLocalizedMode freq 0 x^2) (planarCenter u)]

theorem orbitalCutoff_deriv_remainder_tail {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) (e : Position) :
    Integrable (fun x => ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2) ∧
      (∫ x, ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2) ≤
        (∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2)/R^24 := by
  have h := localized_weighted_coefficient_tail (a := fun x => 1-orbitalCutoff R u x) hR (show (0:ℝ) ≤ 1 by norm_num) (planarCenter u)
    (continuous_const.sub (orbitalCutoff_smooth R u).continuous)
    (((continuumLocalizedMode_C7 freq u).continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (fun x => by rw [abs_of_nonneg (sub_nonneg.mpr (orbitalCutoff_le_one R u x))]; linarith [orbitalCutoff_nonnegative R u x])
    (fun x hx => by rw [orbitalCutoff_eq_one hR u hx.le,sub_self]) (centered_deriv_moment hfreq u e)
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_deriv_translate freq u]
  rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2) (planarCenter u)]
  ring

def orbitalRemainder (freq R : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  (1-orbitalCutoff R u x)*continuumLocalizedMode freq u x

theorem orbitalRemainder_C1 (freq R : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 1 (orbitalRemainder freq R u) :=
  (contDiff_const.sub ((orbitalCutoff_smooth R u).of_le (by simp))).mul
    ((continuumLocalizedMode_C7 freq u).of_le (by norm_num))

theorem orbitalRemainder_deriv (freq R : ℝ) (u : PlanarPosition) (x e : Position) :
    fderiv ℝ (orbitalRemainder freq R u) x e =
      -(fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)+
        (1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e := by
  have hc := ((orbitalCutoff_smooth R u).differentiable (by simp) x).hasFDerivAt
  have hu := ((continuumLocalizedMode_C7 freq u).differentiable (by norm_num) x).hasFDerivAt
  have h := congrArg (fun L : Position →L[ℝ] ℝ => L e)
    (((hasFDerivAt_const (1:ℝ) x).sub hc).mul hu).fderiv
  change fderiv ℝ (orbitalRemainder freq R u) x e = _ at h
  convert h using 1
  simp only [add_apply,smul_apply,sub_apply,zero_apply,smul_eq_mul,Pi.sub_apply]
  ring

theorem orbitalRemainder_deriv_tail {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ (u : PlanarPosition) (e : Position),
      Integrable (fun x => (fderiv ℝ (orbitalRemainder freq R u) x e)^2) ∧
      (∫ x, (fderiv ℝ (orbitalRemainder freq R u) x e)^2) ≤
        2*((B*‖e‖)^2*(∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)+
          (∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2))/R^24 := by
  obtain ⟨B,hB,hb⟩ := orbitalCutoff_deriv_tail hfreq
  refine ⟨B,hB,?_⟩
  intro R hR u e
  obtain ⟨hi1,h1⟩ := hb R hR u e
  obtain ⟨hi2,h2⟩ := orbitalCutoff_deriv_remainder_tail (R := R) hfreq (by linarith) u e
  have hpoint (x : Position) : (fderiv ℝ (orbitalRemainder freq R u) x e)^2 ≤
      2*((fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2+
        ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2) := by
    rw [orbitalRemainder_deriv]
    nlinarith [sq_nonneg (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x+
      (1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)]
  have hi : Integrable (fun x => (fderiv ℝ (orbitalRemainder freq R u) x e)^2) := by
    apply ((hi1.add hi2).const_mul 2).mono' (by
      exact (((orbitalRemainder_C1 freq R u).continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2 |>.aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hi,?_⟩
  have h := integral_mono hi ((hi1.add hi2).const_mul 2) hpoint
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hi1 hi2] at h
  calc
    _ ≤ 2*((∫ x, (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2)+
        (∫ x, ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2)) := h
    _ ≤ 2*((B*‖e‖)^2/R^24*(∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)+
        (∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2)/R^24) := by linarith
    _ = _ := by ring

theorem orbitalRemainder_memLp {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R) (u : PlanarPosition) :
    MemLp (orbitalRemainder freq R u) 2 := by
  apply (memLp_two_iff_integrable_sq (orbitalRemainder_C1 freq R u).continuous.aestronglyMeasurable).mpr
  exact (orbitalCutoff_value_tail hfreq hR u).1

theorem orbitalRemainder_deriv_memLp {freq R : ℝ} (hfreq : 0 < freq) (hR : 1 ≤ R)
    (u : PlanarPosition) (e : Position) :
    MemLp (fun x => fderiv ℝ (orbitalRemainder freq R u) x e) 2 := by
  apply (memLp_two_iff_integrable_sq
    (((orbitalRemainder_C1 freq R u).continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable).mpr
  obtain ⟨B,_,hb⟩ := orbitalRemainder_deriv_tail hfreq
  exact (hb R hR u e).1

end ContinuumCoulomb

end

end OAI
