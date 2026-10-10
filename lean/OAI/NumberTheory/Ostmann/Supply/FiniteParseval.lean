import OAI.NumberTheory.Ostmann.Supply.Fourier

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem conj_stdAddChar (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]

theorem conj_dft (f : ZMod p → ℂ) (v : ZMod p) :
    conj (ZMod.dft f v) = ZMod.dft (fun x => conj (f x)) (-v) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, conj_stdAddChar,
    neg_neg, mul_neg]

theorem dft_pairing (f g : ZMod p → ℂ) :
    ∑ v, ZMod.dft f (-v) * g v = ∑ x, f x * ZMod.dft g (-x) := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    mul_neg, neg_neg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_comm v x]
  ring

theorem dft_parseval_complex (f : ZMod p → ℂ) :
    ∑ v, conj (ZMod.dft f v) * ZMod.dft f v =
      (p : ℂ) * ∑ x, conj (f x) * f x := by
  simp_rw [conj_dft]
  rw [dft_pairing]
  simp_rw [ZMod.dft_dft, neg_neg, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem dft_parseval (f : ZMod p → ℂ) :
    ∑ v, ‖ZMod.dft f v‖^2 = (p : ℝ) * ∑ x, ‖f x‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.conj_mul', Complex.ofReal_pow] using dft_parseval_complex f

theorem unitaryDFT_parseval (f : ZMod p → ℂ) :
    ∑ v, ‖unitaryDFT f v‖^2 = ∑ x, ‖f x‖^2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  simp only [unitaryDFT, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt hp.le, ← Finset.sum_div, dft_parseval]
  exact mul_div_cancel_left₀ _ hp.ne'

theorem additiveTransform_parseval (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    ∑ v, ‖additiveTransform S v‖^2 = p := by
  rw [additiveTransform, unitaryDFT_parseval]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [ZMod.card] using sum_normalizedIndicator_sq S hpos hlt

theorem unitaryDFT_real_neg (f : ZMod p → ℝ) (v : ZMod p) :
    unitaryDFT (fun x => (f x : ℂ)) (-v) =
      conj (unitaryDFT (fun x => (f x : ℂ)) v) := by
  simp only [unitaryDFT, map_div₀, Complex.conj_ofReal, conj_dft]

theorem additiveTransform_neg (S : Finset (ZMod p)) (v : ZMod p) :
    additiveTransform S (-v) = conj (additiveTransform S v) :=
  unitaryDFT_real_neg _ _

end Ostmann.Supply

end

end OAI
