import Mathlib
import OAI.Probability.SKBarriers.Coverage.UniformCoverage

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem sqrt_div_positive {a L : ℝ} (hL : 0 < L) :
    Real.sqrt a/L = Real.sqrt (a/L^2) := by
  rw [Real.sqrt_div' a (sq_nonneg L),Real.sqrt_sq_eq_abs,abs_of_pos hL]

theorem freshCoverageGain_div {n : ℕ} (hn : 0 < n) (b q L : ℝ) (hL : 0 < L) :
    freshCoverageGain n b q/L =
      (b^2*(n:ℝ)/L)*(1-1/(n:ℝ))/4-Real.log 2/L-
      Real.sqrt (Real.pi^2*(b^2*(n:ℝ)/L)*((b^2*(n:ℝ)/L)*q^2/2+Real.log 8/L)/4)-
      Real.sqrt (Real.pi^2*(b^2*(n:ℝ)/L)*(Real.log 2/L)/4) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold freshCoverageGain
  rw [sub_div,sub_div,sub_div,sqrt_div_positive hL,sqrt_div_positive hL]
  have hterm : b^2*((n:ℝ)-1)/4/L = (b^2*(n:ℝ)/L)*(1-1/(n:ℝ))/4 := by
    field_simp
  rw [hterm]
  change _-Real.sqrt ((2*(Real.pi^2*b^2*(n:ℝ)/8)*(b^2*(n:ℝ)*q^2/2+Real.log 8))/L^2)-
    Real.sqrt ((2*(Real.pi^2*b^2*(n:ℝ)/8)*Real.log 2)/L^2) = _
  congr 2 <;> field_simp <;> ring_nf

theorem freshCoverageGain_div_tendsto (L b : ℕ → ℝ) {v q : ℝ}
    (hL : Tendsto L atTop atTop)
    (hV : Tendsto (fun n => (b n)^2*(n:ℝ)/L n) atTop (𝓝 v)) :
    Tendsto (fun n => freshCoverageGain n (b n) q/L n) atTop
      (𝓝 (v/4-Real.sqrt (Real.pi^2*v^2*q^2/8))) := by
  have hLi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp hL
  have hN : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun n => Real.log 2/L n) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,div_eq_mul_inv] using hLi.const_mul (Real.log 2)
  have h8 : Tendsto (fun n => Real.log 8/L n) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,div_eq_mul_inv] using hLi.const_mul (Real.log 8)
  have H := (((hV.mul ((tendsto_const_nhds (x := (1:ℝ))).sub hN)).div_const 4).sub h2).sub
    ((hV.const_mul (Real.pi^2) |>.mul ((hV.mul_const (q^2) |>.div_const 2).add h8)).div_const 4).sqrt
  have H' := H.sub ((hV.const_mul (Real.pi^2) |>.mul h2).div_const 4).sqrt
  have HH : Tendsto (fun n =>
      ((b n)^2*(n:ℝ)/L n)*(1-1/(n:ℝ))/4-Real.log 2/L n-
      Real.sqrt (Real.pi^2*((b n)^2*(n:ℝ)/L n)*(((b n)^2*(n:ℝ)/L n)*q^2/2+Real.log 8/L n)/4)-
      Real.sqrt (Real.pi^2*((b n)^2*(n:ℝ)/L n)*(Real.log 2/L n)/4)) atTop
      (𝓝 (v/4-Real.sqrt (Real.pi^2*v^2*q^2/8))) := by
    convert H' using 1 <;> simp only [one_div,sub_zero,mul_one,mul_zero,zero_div,Real.sqrt_zero,add_zero]
    congr 2
    ring_nf
  apply HH.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (0:ℕ)] with n hLn hn
  exact (freshCoverageGain_div hn (b n) q (L n) hLn).symm

end SK.Analytic

end
end

end

end OAI
