import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDerivativeInterpolation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Differentiating a rapidly decaying remainder using only a coarse second derivative. -/

open Set
namespace DefocusingNLS

theorem radial_derivative_exp_interpolation (f : ℝ → ℂ) (T A B C N t : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (ht : T ≤ t) (ht0 : 0 ≤ t)
    (hf : ∀ s, T ≤ s → DifferentiableAt ℝ f s)
    (hdf : ∀ s, T ≤ s → DifferentiableAt ℝ (deriv f) s)
    (hb0 : ∀ s, T ≤ s → ‖f s‖ ≤ A*Real.exp (-(2*N+C)*s))
    (hb2 : ∀ s, T ≤ s → ‖deriv (deriv f) s‖ ≤ B*Real.exp (C*s)) :
    ‖deriv f t‖ ≤ (2*A+B*Real.exp C)*Real.exp (-N*t) := by
  let h := Real.exp (-(N+C)*t)
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hb0' : ∀ s ∈ Icc t (t+h), ‖f s‖ ≤ A*Real.exp (-(2*N+C)*t) := by
    intro s hs
    apply (hb0 s (ht.trans hs.1)).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    nlinarith [hs.1]
  have hb2' : ∀ s ∈ Icc t (t+h), ‖deriv (deriv f) s‖ ≤ B*Real.exp (C*(t+1)) := by
    intro s hs
    apply (hb2 s (ht.trans hs.1)).trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.exp_le_exp.mpr
    nlinarith [hs.2]
  have hd := radial_derivative_interpolation f t h
    (A*Real.exp (-(2*N+C)*t)) (B*Real.exp (C*(t+1))) hh (by positivity)
    (fun s hs => hf s (ht.trans hs.1)) (fun s hs => hdf s (ht.trans hs.1)) hb0' hb2'
  have he1 : Real.exp (-(2*N+C)*t)/h=Real.exp (-N*t) := by
    dsimp only [h]
    rw [← Real.exp_sub]
    congr 1
    ring
  have he2 : Real.exp (C*(t+1))*h=Real.exp C*Real.exp (-N*t) := by
    dsimp only [h]
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  apply hd.trans_eq
  calc
    2*(A*Real.exp (-(2*N+C)*t))/h+B*Real.exp (C*(t+1))*h =
        2*A*(Real.exp (-(2*N+C)*t)/h)+B*(Real.exp (C*(t+1))*h) := by ring
    _ = _ := by rw [he1,he2]; ring

end DefocusingNLS

end OAI
