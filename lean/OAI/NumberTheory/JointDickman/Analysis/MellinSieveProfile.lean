import OAI.NumberTheory.TwoPointCorrelations.MRTMeanSquareKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! # A positive smooth weight for sparse prime sampling

The weight is at least 1/8 on `[N,2N]` and its Mellin transform has
quadratic decay. This provides the majorant used by the finite sieve.
-/
namespace JointDickman
open MeasureTheory TwoPointCorrelations

noncomputable def mellinSieveWeight (N x : ℝ) : ℝ :=
  (N/x)*Real.exp (-2*|Real.log x-Real.log N|)

noncomputable def mellinSieveAtom (N t x : ℝ) : ℂ :=
  (mellinSieveWeight N x : ℂ)*
    Complex.exp (((-t*(Real.log x-Real.log N) : ℝ) : ℂ)*Complex.I)

lemma mellinSieveWeight_nonneg {N x : ℝ} (hN : 0 ≤ N) (hx : 0 ≤ x) :
    0 ≤ mellinSieveWeight N x := by
  unfold mellinSieveWeight
  positivity

lemma mellinSieveWeight_left {N x : ℝ} (hN : 0 < N) (hx : 0 < x) (hxN : x ≤ N) :
    mellinSieveWeight N x = x/N := by
  have hl := Real.log_le_log hx hxN
  have he : Real.exp (2*(Real.log x-Real.log N)) = (x/N)^2 := by
    rw [← Real.log_div hx.ne' hN.ne', show Real.exp (2*Real.log (x/N)) = (Real.exp (Real.log (x/N)))^2 by simpa using Real.exp_nat_mul (Real.log (x/N)) 2, Real.exp_log (div_pos hx hN)]
  unfold mellinSieveWeight
  rw [abs_of_nonpos (sub_nonpos.mpr hl), show -2* -(Real.log x-Real.log N) =
    2*(Real.log x-Real.log N) by ring, he]
  field_simp

lemma mellinSieveWeight_right {N x : ℝ} (hN : 0 < N) (hxN : N ≤ x) :
    mellinSieveWeight N x = (N/x)^3 := by
  have hx : 0 < x := hN.trans_le hxN
  have hl := Real.log_le_log hN hxN
  have he : Real.exp (-2*(Real.log x-Real.log N)) = (N/x)^2 := by
    rw [show -2*(Real.log x-Real.log N) = 2*(Real.log N-Real.log x) by ring,
      ← Real.log_div hN.ne' hx.ne', show Real.exp (2*Real.log (N/x)) = (Real.exp (Real.log (N/x)))^2 by simpa using Real.exp_nat_mul (Real.log (N/x)) 2, Real.exp_log (div_pos hN hx)]
  unfold mellinSieveWeight
  rw [abs_of_nonneg (sub_nonneg.mpr hl), he]
  ring

lemma mellinSieveWeight_interval {N x : ℝ} (hN : 0 < N) (hx : N ≤ x) (hx2 : x ≤ 2*N) :
    (1/8 : ℝ) ≤ mellinSieveWeight N x := by
  rw [mellinSieveWeight_right hN hx]
  have hxp : 0 < x := hN.trans_le hx
  have hr : (1/2 : ℝ) ≤ N/x := (le_div_iff₀ hxp).mpr (by linarith)
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hr 3
  norm_num at hh ⊢
  exact hh

lemma mellinSieveAtom_log (N t x : ℝ) :
    mellinSieveAtom N t x = x⁻¹ •
      ((N : ℂ)*mrtMeanSquareKernel (1/2) (-t) (Real.log x-Real.log N)) := by
  change _ = ((x⁻¹ : ℝ) : ℂ)*_
  unfold mellinSieveAtom mellinSieveWeight mrtMeanSquareKernel
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
  norm_num
  ring_nf

/-- The positive weight has an exact quadratic-decay Mellin transform. -/
theorem integral_mellinSieveAtom (N t : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), mellinSieveAtom N t x) =
      ((4*N/(4+t^2) : ℝ) : ℂ) := by
  simp_rw [mellinSieveAtom_log]
  rw [integral_comp_log_Ioi_zero (fun v =>
    (N : ℂ)*mrtMeanSquareKernel (1/2) (-t) (v-Real.log N)), integral_const_mul]
  have he := integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => mrtMeanSquareKernel (1/2) (-t) v) (-Real.log N)
  change (∫ v : ℝ, mrtMeanSquareKernel (1/2) (-t) (v-Real.log N)) = _ at he
  rw [he, integral_mrtMeanSquareKernel (by norm_num : (0:ℝ) < 1/2)]
  push_cast
  field_simp
  ring

end JointDickman

end OAI
