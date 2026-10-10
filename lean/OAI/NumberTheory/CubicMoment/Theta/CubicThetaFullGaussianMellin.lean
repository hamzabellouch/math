import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullGaussian
import OAI.NumberTheory.CubicMoment.Estimates.RieszHeatKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Absolute Mellin interchange for the literal affine row heat kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance : Countable CubicThetaFullRow := cubicThetaFullRowEquiv.symm.injective.countable

def cubicThetaFullGaussianMellinTerm (p : ℂ × ℝ) (s : ℝ)
    (r : CubicThetaFullRow) (t : ℝ) : ℝ := t^(s-1)*Real.exp (-t*r.quadratic p)

lemma cubicThetaFullGaussianMellinTerm_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0<s) (r : CubicThetaFullRow) :
    IntegrableOn (cubicThetaFullGaussianMellinTerm p s r) (Ioi 0) := by
  convert integrable_laplace_rpow hs (r.quadratic_pos hp) using 1
  ext t
  unfold cubicThetaFullGaussianMellinTerm
  rw [show -t*r.quadratic p= -r.quadratic p*t by ring]

lemma cubicThetaFullGaussianMellinTerm_integral {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0<s) (r : CubicThetaFullRow) :
    (∫ t in Ioi (0:ℝ),cubicThetaFullGaussianMellinTerm p s r t)=
      Real.Gamma s*r.height p^s := by
  unfold cubicThetaFullGaussianMellinTerm
  simp_rw [show ∀ t : ℝ,-t*r.quadratic p= -r.quadratic p*t from fun t => by ring]
  rw [laplace_rpow hs (r.quadratic_pos hp),r.height_eq_inv,
    Real.inv_rpow (r.quadratic_pos hp).le,Real.rpow_neg (r.quadratic_pos hp).le]

lemma cubicThetaFullGaussianMellinTerm_mass {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0<s) (r : CubicThetaFullRow) :
    (∫ t in Ioi (0:ℝ),‖cubicThetaFullGaussianMellinTerm p s r t‖)=
      Real.Gamma s*r.height p^s := by
  rw [←cubicThetaFullGaussianMellinTerm_integral hp hs r]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)

lemma cubicThetaFullGaussianMellin_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    Summable (fun r : CubicThetaFullRow =>
      ∫ t in Ioi (0:ℝ),‖cubicThetaFullGaussianMellinTerm p s r t‖) := by
  simp_rw [cubicThetaFullGaussianMellinTerm_mass hp (lt_trans (by norm_num) hs)]
  exact (cubicThetaFullHeightMass_summable hp hs).mul_left _

theorem cubicThetaFullGaussian_mellin {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    (∫ t in Ioi (0:ℝ),t^(s-1)*cubicThetaFullGaussian p t)=
      Real.Gamma s*cubicThetaFullHeightMass p s := by
  have hs0 : 0<s := lt_trans (by norm_num) hs
  calc
    _ = ∫ t in Ioi (0:ℝ),∑' r : CubicThetaFullRow,cubicThetaFullGaussianMellinTerm p s r t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [cubicThetaFullGaussian,←tsum_mul_left]
      rfl
    _ = ∑' r : CubicThetaFullRow,∫ t in Ioi (0:ℝ),cubicThetaFullGaussianMellinTerm p s r t :=
      (integral_tsum_of_summable_integral_norm
        (fun r => cubicThetaFullGaussianMellinTerm_integrable hp hs0 r)
        (cubicThetaFullGaussianMellin_summable hp hs)).symm
    _ = _ := by
      simp_rw [cubicThetaFullGaussianMellinTerm_integral hp hs0]
      rw [tsum_mul_left]
      rfl

lemma cubicThetaFullGaussian_mellin_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaFullGaussian p t) (Ioi 0) := by
  have hm := cubicThetaFullGaussian_mellin hp hs
  have hs0 : 0<s := lt_trans (by norm_num) hs
  have hmass : 0<cubicThetaFullHeightMass p s := by
    let r := cubicThetaFullRowCoordinates 0 0
    have hp' : 0<r.height p := by rw [r.height_eq_inv]; exact inv_pos.mpr (r.quadratic_pos hp)
    have hq (q : CubicThetaFullRow) : 0≤q.height p := by
      rw [q.height_eq_inv]
      exact inv_nonneg.mpr (q.quadratic_pos hp).le
    exact (Real.rpow_pos_of_pos hp' s).trans_le
      ((cubicThetaFullHeightMass_summable hp hs).le_tsum r
        (fun q _ => Real.rpow_nonneg (hq q) s))
  by_contra hn
  rw [integral_undef hn] at hm
  exact (ne_of_gt (mul_pos (Real.Gamma_pos_of_pos hs0) hmass)) hm.symm

lemma cubicThetaFullGaussian_measurable (p : ℂ × ℝ) :
    Measurable (cubicThetaFullGaussian p) := by
  apply Measurable.tsum
  intro r
  fun_prop

end CubicFirstMoment

end

end OAI
