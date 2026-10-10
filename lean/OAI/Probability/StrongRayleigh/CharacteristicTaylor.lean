import Mathlib

namespace OAI

universe u_1

noncomputable section

open MeasureTheory
open scoped BigOperators Interval Topology

namespace Problem336AdditiveD139.CharacteristicTaylor

theorem norm_sub_zero_le_of_deriv_bound {E : Type u_1} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E}
    (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    (C : ℝ) (n : ℕ) (hb : ∀ t, ‖f' t‖ ≤ C * |t| ^ n) (x : ℝ) :
    ‖f x - f 0‖ ≤ C * |x| ^ (n + 1) / (n + 1) := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 x)]
  calc
    ‖∫ t in 0..x, f' t‖ ≤ ∫ t in Ι 0 x, ‖f' t‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t in Ι 0 x, C * |t| ^ n := by
      apply integral_mono
      · exact hc.norm.integrableOn_Icc.mono_set Set.uIoc_subset_uIcc
      · exact (continuous_const.mul (continuous_abs.pow n)).integrableOn_Icc.mono_set
          Set.uIoc_subset_uIcc
      · exact hb
    _ = C * |x| ^ (n + 1) / (n + 1) := by
      rw [integral_const_mul]
      have h := integral_pow_abs_sub_uIoc (a := (0 : ℝ)) (b := x) (n := n)
      simp only [sub_zero] at h
      rw [h]
      ring

theorem norm_exp_I_mul_sub_one_sub_linear (x : ℝ) :
    ‖Complex.exp (Complex.I * x) - 1 - Complex.I * x‖ ≤ |x| ^ 2 / 2 := by
  let f : ℝ → ℂ := fun t => Complex.exp (Complex.I * t) - 1 - Complex.I * t
  let f' : ℝ → ℂ := fun t => Complex.I * (Complex.exp (Complex.I * t) - 1)
  have hd : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hlin := (hasDerivAt_id (t : ℂ)).const_mul Complex.I
    have h := ((hlin.cexp.sub_const 1).sub hlin).comp_ofReal
    convert h using 1 <;> dsimp [f, f']
    ring
  have hc : Continuous f' := by dsimp [f']; fun_prop
  have hb : ∀ t, ‖f' t‖ ≤ 1 * |t| ^ 1 := by
    intro t
    simpa [f', norm_mul, Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t))
  have h := norm_sub_zero_le_of_deriv_bound hd hc 1 1 hb x
  norm_num [f] at h ⊢
  exact h

theorem norm_exp_I_mul_sub_quadratic (x : ℝ) :
    ‖Complex.exp (Complex.I * x) - 1 - Complex.I * x + (x : ℂ) ^ 2 / 2‖ ≤
      |x| ^ 3 / 6 := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (Complex.I * t) - 1 - Complex.I * t + (t : ℂ) ^ 2 / 2
  let f' : ℝ → ℂ := fun t =>
    Complex.I * (Complex.exp (Complex.I * t) - 1 - Complex.I * t)
  have hd : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hlin := (hasDerivAt_id (t : ℂ)).const_mul Complex.I
    have h := (((hlin.cexp.sub_const 1).sub hlin).add
      (((hasDerivAt_id (t : ℂ)).pow 2).div_const 2)).comp_ofReal
    convert h using 1 <;> dsimp [f, f']
    ring_nf
    simp [Complex.I_sq]
  have hc : Continuous f' := by dsimp [f']; fun_prop
  have hb : ∀ t, ‖f' t‖ ≤ (1 / 2 : ℝ) * |t| ^ 2 := by
    intro t
    simpa [f', norm_mul, div_eq_mul_inv, mul_comm] using
      norm_exp_I_mul_sub_one_sub_linear t
  have h := norm_sub_zero_le_of_deriv_bound hd hc (1 / 2) 2 hb x
  norm_num [f] at h
  convert h using 1
  ring

end Problem336AdditiveD139.CharacteristicTaylor

end

end OAI
