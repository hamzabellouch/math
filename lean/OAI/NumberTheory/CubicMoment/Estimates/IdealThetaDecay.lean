import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGaussianRows
import OAI.NumberTheory.CubicMoment.Estimates.IdealMellinSeries

namespace OAI

/-! Convergence and exponential decay of the actual ideal theta series. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace CubicFirstMoment

def idealTheta (A : ℝ) (χ : EisensteinIdealExponent → ℂ) (t : ℝ) : ℂ :=
  ∑' ν, χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)

lemma summable_ideal_exponential {c : ℝ} (hc : 0 < c) :
    Summable (fun ν : EisensteinIdealExponent => Real.exp (-c*idealExponentNorm ν)) := by
  have hs := (huxleyPeriodizedGaussian_summable hc 0).comp_injective idealExponentGenerator_injective
  convert hs using 1
  ext ν
  simp only [Function.comp_apply,sub_zero,idealExponentNorm,normNat_cast,norm,
    Complex.normSq_eq_norm_sq]

lemma idealTheta_summable {A t : ℝ} (hA : 0 < A) (ht : 0 < t)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    Summable (fun ν => χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)) := by
  apply (summable_ideal_exponential (div_pos ht hA)).of_norm_bounded
  intro ν
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : -idealExponentNorm ν*t/A = -(t/A)*idealExponentNorm ν := by ring
  rw [he]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (hχ ν)

lemma idealTheta_norm_bound {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖idealTheta A χ t‖ ≤
      (∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(2*A)))*
        Real.exp (-t/(2*A)) := by
  have ht0 : 0 < t := by linarith
  have hs := idealTheta_summable hA ht0 χ hχ
  have he := summable_ideal_exponential (show 0 < 1/(2*A) by positivity)
  have hg : Summable (fun ν : EisensteinIdealExponent =>
      Real.exp (-idealExponentNorm ν/(2*A))*Real.exp (-t/(2*A))) := by
    convert he.mul_right (Real.exp (-t/(2*A))) using 1
    ext ν
    congr 2
    ring
  unfold idealTheta
  calc
    _ ≤ ∑' ν, ‖χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' ν : EisensteinIdealExponent,
        Real.exp (-idealExponentNorm ν/(2*A))*Real.exp (-t/(2*A)) := by
      apply hs.norm.tsum_le_tsum _ hg
      intro ν
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply (mul_le_of_le_one_left (Real.exp_pos _).le (hχ ν)).trans
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn := idealExponentNorm_ge_one ν
      have hprod := mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr ht)
      have hh : -2*(idealExponentNorm ν*t) ≤ -idealExponentNorm ν-t := by nlinarith
      have hh' := div_le_div_of_nonneg_right hh (show 0 ≤ 2*A by positivity)
      convert hh' using 1 <;> field_simp
      all_goals ring
    _ = _ := tsum_mul_right

lemma idealTheta_continuousOn_ray {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealTheta A χ) (Set.Ici δ) := by
  apply continuousOn_tsum (fun ν => by fun_prop)
    (summable_ideal_exponential (div_pos hδ hA))
  intro ν t ht
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_of_le_one_left (Real.exp_pos _).le (hχ ν)).trans
  apply Real.exp_le_exp.mpr
  have hn := idealExponentNorm_pos ν
  have hd := div_pos hn hA
  have hm := mul_le_mul_of_nonneg_left ht hd.le
  have hh := neg_le_neg hm
  convert hh using 1 <;> ring

lemma idealTheta_continuousOn {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealTheta A χ) (Set.Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hr := idealTheta_continuousOn_ray hA (show 0 < t/2 by linarith) χ hχ
  exact (hr.continuousAt (Ici_mem_nhds (show t/2 < t by linarith))).continuousWithinAt

lemma idealTheta_isBigO_exp {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    idealTheta A χ =O[atTop] (fun t : ℝ => Real.exp (-(1/(2*A))*t)) := by
  apply Asymptotics.IsBigO.of_bound
    (∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(2*A)))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  have he : -(1/(2*A))*t = -t/(2*A) := by ring
  simpa only [he,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    idealTheta_norm_bound hA χ hχ ht

lemma idealTheta_isBigO_rpow {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (r : ℝ) :
    idealTheta A χ =O[atTop] (fun t : ℝ => t^r) :=
  (idealTheta_isBigO_exp hA χ hχ).trans
    (isLittleO_exp_neg_mul_rpow_atTop (show 0 < 1/(2*A) by positivity) r).isBigO

end CubicFirstMoment

end

end OAI
