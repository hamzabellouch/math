import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylBins
import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylRational
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationDefs

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem normalizedCoefficient_inversion {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) (s : ZMod q) :
    F s = ∑ h : ZMod q, normalizedCoefficient F h * ZMod.stdAddChar (s * h) := by
  have hi := ZMod.invDFT_apply (ZMod.dft F) s
  rw [LinearEquiv.symm_apply_apply] at hi
  rw [hi]
  simp only [normalizedCoefficient, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [mul_comm h s]
  ring

theorem stdAddChar_integer_mul_eq_weyl {q : ℕ} [NeZero q]
    (h : ZMod q) (n : ℤ) :
    ZMod.stdAddChar ((n : ZMod q) * h) = weylPhase ((n : ℝ) * h.val / q) := by
  calc
    _ = ZMod.stdAddChar ((n * (h.val : ℤ) : ℤ) : ZMod q) := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = Complex.exp (2 * Real.pi * Complex.I * (n * (h.val : ℤ) : ℤ) / q) :=
      ZMod.stdAddChar_coe _
    _ = _ := by
      rw [weylPhase, Real.fourierChar_apply]
      push_cast
      congr 1
      ring

theorem shifted_linear_sum_norm (x : ℝ) (a : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, weylPhase (((a : ℝ) + n) * x)‖ =
      ‖∑ n ∈ Finset.range N, weylPhase ((n : ℝ) * x)‖ := by
  simp_rw [add_mul, weylPhase_add]
  rw [← Finset.mul_sum, norm_mul, weylPhase_norm, one_mul]

theorem shifted_residue_grid_spacing {q : ℕ} [NeZero q] (α : ℝ)
    (i j : ZMod q) (hij : i ≠ j) (m : ℤ) :
    1 / (2 * (q : ℝ)) ≤ |(α + i.val / q) - (α + j.val / q) - m| := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have hijv : (i.val : ℤ) ≠ j.val := by
    intro he
    apply hij
    apply ZMod.val_injective
    exact_mod_cast he
  have hshort : |(i.val : ℤ) - j.val| < q := by
    have hi := i.val_lt
    have hj := j.val_lt
    rw [abs_lt]
    constructor <;> omega
  have hh := rational_multiples_spacing 1 q hq (by simp) i.val j.val m hijv hshort
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hone : 1 / (2 * (q : ℝ)) ≤ 1 / q := by
    apply one_div_le_one_div_of_le hqR
    linarith
  apply hone.trans
  convert hh using 1; push_cast; ring_nf

end Ostmann.QuadraticCenter

end

end OAI
