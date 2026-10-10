import OAI.NumberTheory.Jacobsthal.Estimates.ScalarTailRecurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem omissionForce_le_one (i : Side) (r b : ℝ) : omissionForce i r b ≤ 1 := by
  cases i with
  | even => norm_num [omissionForce]
  | odd =>
    have hc : (upperCutoff .odd r b)⁻¹ ≤ (1:ℝ) :=
      (inv_le_one₀ ((by norm_num : (0:ℝ)<1).trans_le (upperCutoff_bounds .odd r b).1)).mpr
        (upperCutoff_bounds .odd r b).1
    have hb : 0 ≤ survivorBaseline b := inv_nonneg.mpr (zero_le_one.trans (baseCutoff_bounds b).1)
    change (upperCutoff .odd r b)⁻¹-survivorBaseline b ≤ 1
    linarith

noncomputable def secondKernel (p : ℝ×ℝ) : ℝ :=
  (2*(p.1^2-1)/(max 1 p.2))*omissionForce .odd (2*p.1+2-p.2) p.2

theorem secondKernel_continuous : Continuous secondKernel := by
  have hf : Continuous (fun p : ℝ×ℝ => omissionForce .odd (2*p.1+2-p.2) p.2) :=
    (omissionForce_continuous .odd).comp
      (((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_snd).prodMk continuous_snd)
  have hp : Continuous (fun p : ℝ×ℝ => 2*(p.1^2-1)/(max 1 p.2)) :=
    (continuous_const.mul ((continuous_fst.pow 2).sub continuous_const)).div
      (continuous_const.max continuous_snd) (fun p => ne_of_gt
        ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 p.2)))
  exact hp.mul hf

theorem secondKernel_bound {y x : ℝ} (hy : y ∈ Icc (1:ℝ) 3) (hx : x ∈ Icc (1:ℝ) 2) :
    |secondKernel (y,x)| ≤ 16 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hpoly : 0 ≤ y^2-1 := by nlinarith [hy.1]
  have hpoly8 : y^2-1 ≤ 8 := by nlinarith [hy.1,hy.2]
  have hp0 : 0 ≤ 2*(y^2-1)/x := div_nonneg (mul_nonneg (by norm_num) hpoly) hx0.le
  have hp16 : 2*(y^2-1)/x ≤ 16 := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith [hx.1]
  unfold secondKernel
  dsimp only
  rw [max_eq_right hx.1,abs_of_nonneg (mul_nonneg hp0 (omissionForce_nonnegative .odd _ _))]
  calc
    _ ≤ (2*(y^2-1)/x)*1 := mul_le_mul_of_nonneg_left (omissionForce_le_one .odd _ _) hp0
    _ ≤ 16 := by simpa only [mul_one] using hp16

theorem second_density_kernel (y : ℝ) :
    omissionDensity 1 .even y=∫ x : ℝ in 1..2,secondKernel (y,x) := by
  change 2*(y^2-1)*(∫ x : ℝ in 1..upperCutoff .even (2*y+2) 2,
    omissionForce .odd (2*y+2-x) x/(max 1 x))=_
  have hc : upperCutoff .even (2*y+2) 2=2 := by norm_num [upperCutoff]
  rw [hc,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [secondKernel]
  ring

end ErdosOmissionBindings

end

end Erdos970

end OAI
