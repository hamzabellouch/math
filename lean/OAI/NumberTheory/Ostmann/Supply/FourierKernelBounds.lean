import OAI.NumberTheory.Ostmann.Supply.FiniteConvolution
import OAI.NumberTheory.Ostmann.Supply.FourierKernel

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem fourierKernel_eq_dft (E : Finset (ZMod p)) (x : ZMod p) :
    fourierKernel E x = (p : ℂ)⁻¹ *
      ZMod.dft (fun h => if h ∈ E then (1 : ℂ) else 0) (-x) := by
  simp only [fourierKernel, ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

theorem fourierKernel_energy (E : Finset (ZMod p)) :
    ∑ x, ‖fourierKernel E x‖^2 = (E.card : ℝ)/p := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp_rw [fourierKernel_eq_dft, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum]
  have hn : (∑ x : ZMod p,
      ‖ZMod.dft (fun h => if h ∈ E then (1 : ℂ) else 0) (-x)‖^2) =
      ∑ x, ‖ZMod.dft (fun h => if h ∈ E then (1 : ℂ) else 0) x‖^2 := by
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  rw [hn, dft_parseval]
  simp only [apply_ite, norm_one, norm_zero, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  field_simp

theorem fourierKernel_norm_le (E : Finset (ZMod p)) (x : ZMod p) :
    ‖fourierKernel E x‖ ≤ (E.card : ℝ)/p := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  simp only [fourierKernel, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (p:ℝ)⁻¹ * ‖∑ h ∈ E, ZMod.stdAddChar (h*x)‖ ≤
        (p:ℝ)⁻¹ * ∑ h ∈ E, ‖ZMod.stdAddChar (h*x)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hp)
    _ = (E.card:ℝ)/p := by simp [AddChar.norm_apply, div_eq_mul_inv, mul_comm]

theorem convolution_fourierKernel (E : Finset (ZMod p)) :
    convolutionOperator (fourierKernel E) = spectralProjection E := by
  ext f x
  rw [convolutionOperator_matrix, spectralProjection_apply]

theorem squareKernel_norm_le (E : Finset (ZMod p)) (t : ℝ) :
    ‖convolutionOperator (fun x => ((t : ℂ)*fourierKernel E x)^2)‖ ≤
      t^2 * ((E.card : ℝ)/p) := by
  calc
    _ ≤ ∑ x, ‖((t : ℂ)*fourierKernel E x)^2‖ := convolutionOperator_norm_le _
    _ = t^2 * ∑ x, ‖fourierKernel E x‖^2 := by
      simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs, Finset.mul_sum]
    _ = _ := by rw [fourierKernel_energy]

end Ostmann.Supply

end

end OAI
