import OAI.NumberTheory.CubicMoment.Estimates.ThetaHeatKernelBound

namespace OAI

/-! The normalized theta series whose Mellin transform has the angular
Gamma shift. Its defining sum runs over all nonzero ideals. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

def idealHeatTheta (A κ : ℝ) (χ : EisensteinIdealExponent → ℂ) (t : ℝ) : ℂ :=
  ∑' ν, χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)

lemma idealHeatTheta_term_bound {A κ C t : ℝ} (hA : 0 < A) (ht : 0 < t)
    (hkernel : ∀ x : ℝ, 0 ≤ x → x^κ*Real.exp (-x) ≤ C*Real.exp (-x/2))
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (ν : EisensteinIdealExponent) :
    ‖χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)‖ ≤
      C*Real.exp (-idealExponentNorm ν*t/(2*A)) := by
  have hn := idealExponentNorm_pos ν
  have hx : 0 ≤ idealExponentNorm ν*t/A := by positivity
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx κ) (Real.exp_pos _).le)]
  calc
    _ ≤ (idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A) :=
      mul_le_of_le_one_left (by positivity) (hχ ν)
    _ = (idealExponentNorm ν*t/A)^κ*Real.exp (-(idealExponentNorm ν*t/A)) := by congr 2; ring
    _ ≤ C*Real.exp (-(idealExponentNorm ν*t/A)/2) := hkernel _ hx
    _ = _ := by congr 2; ring

lemma idealHeatTheta_summable {A κ t : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (ht : 0 < t)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    Summable (fun ν => χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)) := by
  obtain ⟨C,hC,hkernel⟩ := rpow_exp_half_bound hκ
  have hs := (summable_ideal_exponential (show 0 < t/(2*A) by positivity)).mul_left C
  apply hs.of_norm_bounded
  intro ν
  convert idealHeatTheta_term_bound hA ht hkernel χ hχ ν using 1
  congr 2
  ring

lemma idealHeatTheta_continuousOn_ray {A κ δ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (hδ : 0 < δ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealHeatTheta A κ χ) (Set.Ici δ) := by
  obtain ⟨C,hC,hkernel⟩ := rpow_exp_half_bound hκ
  have hc (ν : EisensteinIdealExponent) : Continuous (fun t : ℝ =>
      (idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A)) :=
    (((continuous_const.mul continuous_id).div_const A).rpow_const (fun _ => Or.inr hκ)).mul
      (by fun_prop)
  apply continuousOn_tsum (fun ν =>
    (continuous_const.mul (Complex.continuous_ofReal.comp (hc ν))).continuousOn)
    ((summable_ideal_exponential (show 0 < δ/(2*A) by positivity)).mul_left C)
  intro ν t ht
  have ht0 : 0 < t := lt_of_lt_of_le hδ ht
  apply (idealHeatTheta_term_bound hA ht0 hkernel χ hχ ν).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.exp_le_exp.mpr
  have hn := idealExponentNorm_pos ν
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ idealExponentNorm ν/(2*A) by positivity)
  convert neg_le_neg hm using 1 <;> ring

lemma idealHeatTheta_continuousOn {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealHeatTheta A κ χ) (Set.Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hr := idealHeatTheta_continuousOn_ray hA hκ (show 0 < t/2 by exact half_pos ht) χ hχ
  exact (hr.continuousAt (Ici_mem_nhds (show t/2 < t by linarith))).continuousWithinAt

lemma idealHeatTheta_norm_bound {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖idealHeatTheta A κ χ t‖ ≤ C*Real.exp (-t/(4*A)) := by
  obtain ⟨C,hC,hkernel⟩ := rpow_exp_half_bound hκ
  let D := ∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(4*A))
  have hD : 0 ≤ D := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨C*D,by positivity,?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hs := idealHeatTheta_summable hA hκ ht0 χ hχ
  have he := (summable_ideal_exponential (show 0 < 1/(4*A) by positivity)).mul_left C
  have hg : Summable (fun ν : EisensteinIdealExponent =>
      C*Real.exp (-idealExponentNorm ν/(4*A))*Real.exp (-t/(4*A))) := by
    convert he.mul_right (Real.exp (-t/(4*A))) using 1
    ext ν
    congr 3
    ring
  calc
    _ ≤ ∑' ν, ‖χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' ν : EisensteinIdealExponent,
        C*Real.exp (-idealExponentNorm ν/(4*A))*Real.exp (-t/(4*A)) := by
      apply hs.norm.tsum_le_tsum _ hg
      intro ν
      apply (idealHeatTheta_term_bound hA ht0 hkernel χ hχ ν).trans
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn := idealExponentNorm_ge_one ν
      have hp := mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr ht)
      have hh : -2*(idealExponentNorm ν*t) ≤ -idealExponentNorm ν-t := by nlinarith
      convert div_le_div_of_nonneg_right hh (show 0 ≤ 4*A by positivity) using 1 <;> field_simp <;> ring
    _ = _ := by rw [tsum_mul_right,tsum_mul_left]

lemma idealHeatTheta_isBigO_rpow {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (r : ℝ) :
    idealHeatTheta A κ χ =O[atTop] (fun t : ℝ => t^r) := by
  obtain ⟨C,hC,hbound⟩ := idealHeatTheta_norm_bound hA hκ χ hχ
  have he : idealHeatTheta A κ χ =O[atTop] (fun t : ℝ => Real.exp (-(1/(4*A))*t)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have hx : -(1/(4*A))*t = -t/(4*A) := by ring
    simpa only [hx,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hbound t ht
  exact he.trans (isLittleO_exp_neg_mul_rpow_atTop (show 0 < 1/(4*A) by positivity) r).isBigO

end CubicFirstMoment

end

end OAI
