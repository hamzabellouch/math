import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! # Gronwall's inequality with only interior differentiation -/

open Set
namespace RegularPointCoordinates

theorem affine_growth_on_interval {F : ℝ → ℝ} {b c : ℝ} (hb : 0 ≤ b)
    (hF : ContinuousOn F (Icc 0 b))
    (hd : ∀ t ∈ Ioo 0 b, DifferentiableAt ℝ F t ∧ deriv F t ≤ c*(F t+1))
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    F t+1 ≤ Real.exp (c*t)*(F 0+1) := by
  have hmono : AntitoneOn (fun s => Real.exp (-c*s)*(F s+1)) (Icc 0 b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 b)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
        (hF.add continuousOn_const))
      (fun s hs => ((((hasDerivAt_id s).const_mul (-c)).exp).mul
        (((hd s (by simpa only [interior_Icc] using hs)).1.hasDerivAt).add_const 1)).hasDerivWithinAt)
    intro s hs
    have hs' : s ∈ Ioo 0 b := by simpa only [interior_Icc] using hs
    have hh := mul_le_mul_of_nonneg_left (hd s hs').2 (Real.exp_pos (-c*s)).le
    simp only [id_eq,mul_one]
    nlinarith only [hh]
  have hh := hmono (show (0:ℝ) ∈ Icc 0 b from ⟨le_rfl,hb⟩) ht ht.1
  simp only [mul_zero,Real.exp_zero,one_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_pos (c*t)).le
  have hcancel : Real.exp (c*t)*Real.exp (-c*t) = 1 := by
    rw [← Real.exp_add,show c*t+ -c*t = 0 by ring,Real.exp_zero]
  simpa only [← mul_assoc,hcancel,one_mul] using hmul

end RegularPointCoordinates

end OAI
