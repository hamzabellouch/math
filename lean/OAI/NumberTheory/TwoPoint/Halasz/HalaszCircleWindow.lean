import OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusBessel
import Mathlib.MeasureTheory.Group.AddCircle

namespace OAI

/-! A compact circle window with a lower bound for its small Fourier
coefficients. This supplies the localizer for the double moment estimate. -/
namespace TwoPointCorrelations

open MeasureTheory Metric Set
open scoped ComplexConjugate

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

noncomputable def halaszCircleWindow (δ : ℝ) (x : AddCircle (1:ℝ)) : ℂ :=
  (closedBall 0 δ).indicator (fun _ => 1) x

lemma halasz_circle_window_memLp (δ : ℝ) :
    MemLp (halaszCircleWindow δ) 2 AddCircle.haarAddCircle :=
  (memLp_const (1:ℂ)).indicator measurableSet_closedBall

lemma halasz_circle_window_volume {δ : ℝ} (hδ : 0≤δ) (hδhalf : δ≤1/2) :
    AddCircle.haarAddCircle.real (closedBall (0:AddCircle (1:ℝ)) δ)=2*δ := by
  have hμ : (volume : Measure (AddCircle (1:ℝ)))=AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ)))
  rw [← hμ,measureReal_def,AddCircle.volume_closedBall,
    min_eq_right (by linarith : 2*δ≤1),ENNReal.toReal_ofReal (by positivity)]

lemma halasz_circle_character_re {δ : ℝ} {n : ℤ}
    (hphase : 2*Real.pi*|(n:ℝ)| * δ≤1) (x : AddCircle (1:ℝ)) (hx : x∈closedBall 0 δ) :
    (1/2:ℝ)≤(fourier n x).re := by
  let y := AddCircle.equivIoc (1:ℝ) (-(1/2:ℝ)) x
  have hy : -(1/2:ℝ)<(y:ℝ) ∧ (y:ℝ)≤1/2 := by
    have hh := y.property
    change -(1/2:ℝ)<(y:ℝ) ∧ (y:ℝ)≤-(1/2:ℝ)+1 at hh
    constructor <;> linarith [hh.1,hh.2]
  have hyx : ((y:ℝ):AddCircle (1:ℝ))=x := AddCircle.coe_equivIoc
  have hn : ‖x‖=|(y:ℝ)| := by
    rw [← hyx]
    exact (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num)).mpr
      (by simpa using abs_le.mpr ⟨hy.1.le,hy.2⟩)
  have hyδ : |(y:ℝ)|≤δ := by
    simpa only [mem_closedBall,dist_zero_right,hn] using hx
  have ha : |2*Real.pi*(n:ℝ)*(y:ℝ)|≤1 := by
    rw [abs_mul,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
    exact (mul_le_mul_of_nonneg_left hyδ (by positivity)).trans hphase
  have hs : (2*Real.pi*(n:ℝ)*(y:ℝ))^2≤1 := by
    nlinarith [(abs_le.mp ha).1,(abs_le.mp ha).2]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*(n:ℝ)*(y:ℝ))
  rw [← hyx,fourier_coe_apply]
  have he : (Complex.exp (2*↑Real.pi*Complex.I*(n:ℂ)*(y:ℂ)/(1:ℂ))).re =
      Real.cos (2*Real.pi*(n:ℝ)*(y:ℝ)) := by
    rw [show 2*↑Real.pi*Complex.I*(n:ℂ)*(y:ℂ)/(1:ℂ)=
      ((2*Real.pi*(n:ℝ)*(y:ℝ):ℝ):ℂ)*Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  norm_num only [Complex.ofReal_one] at *
  rw [he]
  linarith

/-- The small Fourier coefficients of the indicator window cannot cancel. -/
theorem halasz_circle_window_coefficient {δ : ℝ} {n : ℤ}
    (hδ : 0≤δ) (hδhalf : δ≤1/2) (hphase : 2*Real.pi*|(n:ℝ)| * δ≤1) :
    δ≤‖∫ x : AddCircle (1:ℝ), conj (fourier n x)*halaszCircleWindow δ x
      ∂AddCircle.haarAddCircle‖ := by
  have hi : IntegrableOn (fun x : AddCircle (1:ℝ) => conj (fourier n x))
      (closedBall 0 δ) AddCircle.haarAddCircle := by
    exact ((Complex.continuous_conj.comp (fourier n).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have heq : (∫ x : AddCircle (1:ℝ), conj (fourier n x)*halaszCircleWindow δ x
      ∂AddCircle.haarAddCircle) =
      ∫ x in closedBall (0:AddCircle (1:ℝ)) δ, conj (fourier n x)
        ∂AddCircle.haarAddCircle := by
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈closedBall (0:AddCircle (1:ℝ)) δ <;>
      simp [halaszCircleWindow,hx]
  rw [heq]
  apply le_trans _ (Complex.re_le_norm _)
  change δ≤RCLike.re (∫ x in closedBall (0:AddCircle (1:ℝ)) δ,
    conj (fourier n x) ∂AddCircle.haarAddCircle)
  rw [← integral_re hi]
  have hh := setIntegral_mono_on (integrableOn_const (C := (1/2:ℝ))) hi.re
    measurableSet_closedBall (fun x hx => by
      change (1/2:ℝ)≤(conj (fourier n x)).re
      simpa only [Complex.conj_re] using halasz_circle_character_re hphase x hx)
  rw [setIntegral_const,smul_eq_mul,halasz_circle_window_volume hδ hδhalf] at hh
  linarith

end TwoPointCorrelations

end OAI
