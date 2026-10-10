import Mathlib

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosContinuousBoundary

theorem integral_upper_difference_bound
    (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G)
    (a b D : ℝ) (ha : a ∈ Icc 1 2) (hD : 0 ≤ D)
    (hFG : ∀ x, |F x-G x| ≤ D) (hGb : ∀ x, |G x| ≤ 1) :
    |(∫ x in (1:ℝ)..a,F x)-(∫ x in (1:ℝ)..b,G x)| ≤ D+|a-b| := by
  have hs := intervalIntegral.integral_sub (hF.intervalIntegrable (μ:=volume) 1 a) (hG.intervalIntegrable (μ:=volume) 1 a)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ:=volume) 1 b) (hG.intervalIntegrable (μ:=volume) b a)
  have he : (∫ x in (1:ℝ)..a,F x)-(∫ x in (1:ℝ)..b,G x) =
      (∫ x in (1:ℝ)..a,F x-G x)+(∫ x in b..a,G x) := by
    rw [hs]
    linarith
  have hfirst := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=a)
    (f:=fun x => F x-G x) (C:=D) (fun x _ => by simpa only [Real.norm_eq_abs] using hFG x)
  have hsecond := intervalIntegral.norm_integral_le_of_norm_le_const (a:=b) (b:=a)
    (f:=G) (C:=1) (fun x _ => by simpa only [Real.norm_eq_abs] using hGb x)
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [ha.1] : 0 ≤ a-1)] at hfirst
  rw [Real.norm_eq_abs,one_mul] at hsecond
  have hfirst' : |∫ x in (1:ℝ)..a,F x-G x| ≤ D := by
    apply hfirst.trans
    nlinarith [ha.2]
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hfirst' hsecond)

end ErdosContinuousBoundary

end

end Erdos970

end OAI
