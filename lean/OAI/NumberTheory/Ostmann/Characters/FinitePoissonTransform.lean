import Mathlib.Analysis.Fourier.PoissonSummation
import OAI.NumberTheory.Ostmann.Characters.PrimitiveGaussFourier

namespace OAI

/-! # Poisson summation with a concrete finite periodic weight -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap
open Asymptotics Filter

theorem schwartz_int_norm_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖f (n : ℝ)‖) := by
  have hb := (f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)) hb.norm_left

private theorem fourier_residue {N : ℕ} [NeZero N] (n : ℤ) (a : ZMod N) :
    fourier n (ZMod.toAddCircle a) = ZMod.stdAddChar ((n : ZMod N) * a) := by
  simp only [fourier_apply, ZMod.stdAddChar_apply, ZMod.toCircle,
    AddChar.compAddMonoidHom_apply]
  rw [← map_zsmul]
  congr 2
  simp only [zsmul_eq_mul]
  rfl

private theorem schwartz_fourier_residue_summable {N : ℕ} [NeZero N]
    (f : 𝓢(ℝ, ℂ)) (a : ZMod N) :
    Summable (fun n : ℤ => 𝓕 f (n : ℝ) * ZMod.stdAddChar ((n : ZMod N) * a)) := by
  apply Summable.of_norm_bounded (schwartz_int_norm_summable (𝓕 f))
  intro n
  simp only [Complex.norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one, le_refl]

/-- The lattice spacing has been absorbed into the Schwartz function.
This exact identity retains the finite Fourier coefficient and all signs. -/
theorem finite_poisson_transform {N : ℕ} [NeZero N] (f : 𝓢(ℝ, ℂ)) (F : ZMod N → ℂ) :
    (∑ a : ZMod N, F a * ∑' n : ℤ, f ((a.val : ℝ) / N + n)) =
      (N : ℂ) * ∑' n : ℤ, 𝓕 f (n : ℝ) * additiveFourier F (-(n : ZMod N)) := by
  have hp (a : ZMod N) : (∑' n : ℤ, f ((a.val : ℝ) / N + n)) =
      ∑' n : ℤ, 𝓕 f (n : ℝ) * ZMod.stdAddChar ((n : ZMod N) * a) := by
    rw [f.tsum_eq_tsum_fourier]
    simp_rw [← ZMod.toAddCircle_apply, fourier_residue]
  simp_rw [hp, ← tsum_mul_left]
  have hsum (a : ZMod N) : Summable (fun n : ℤ =>
      F a * (𝓕 f (n : ℝ) * ZMod.stdAddChar ((n : ZMod N) * a))) :=
    (schwartz_fourier_residue_summable f a).mul_left _
  rw [← Summable.tsum_finsetSum (fun a _ => hsum a)]
  apply tsum_congr
  intro n
  rw [additiveFourier_apply]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hc (z : ℂ) : (N : ℂ) * ((N : ℂ)⁻¹ * z) = z := by
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  rw [mul_left_comm (N : ℂ) (𝓕 f (n : ℝ)), hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : -(a * -(n : ZMod N)) = (n : ZMod N) * a := by ring
  rw [ha']
  ring

end Ostmann

end OAI
