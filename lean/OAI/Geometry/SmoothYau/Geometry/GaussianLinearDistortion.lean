import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
namespace YauCounterexamples

lemma gaussian_linear_distortion {κ A t : ℝ} (hκ : 0 < κ) :
    A*t-κ*t^2 ≤ t-κ/2*t^2 + (A-1)^2/(2*κ) := by
  have hc : 2*κ*((A-1)^2/(2*κ)) = (A-1)^2 := by field_simp
  nlinarith [sq_nonneg (κ*t-(A-1))]

lemma gaussian_phase_coordinate_shift {n κ A q s φ : ℝ}
    (hn : 0 < n) (hκ : 0 < κ)
    (hphase : n*(s-φ) ≤ A*Real.sqrt n*q-κ*n*q^2) :
    n*(s-(φ+(A-1)^2/(2*κ)/n)) ≤
      Real.sqrt n*q-(κ/2)*n*q^2 := by
  have hs := gaussian_linear_distortion (A := A) (t := Real.sqrt n*q) hκ
  rw [mul_pow,Real.sq_sqrt hn.le] at hs
  have he : n*((A-1)^2/(2*κ)/n) = (A-1)^2/(2*κ) := by field_simp
  nlinarith

lemma gaussian_phase_shift_exp {n κ A φ : ℝ} (hn : n ≠ 0) :
    Real.exp (n*(φ+(A-1)^2/(2*κ)/n)) =
      Real.exp ((A-1)^2/(2*κ))*Real.exp (n*φ) := by
  have he : n*(φ+(A-1)^2/(2*κ)/n) = (A-1)^2/(2*κ)+n*φ := by field_simp; ring
  rw [he,Real.exp_add]
end YauCounterexamples

end

end OAI
