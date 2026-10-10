import OAI.NumberTheory.Ostmann.Supply.FiniteParseval
import OAI.NumberTheory.Ostmann.Tree.Fourier

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem fourier_parseval (f : ZMod p → ℂ) :
    ∑ a, ‖fourier f a‖ ^ 2 = l2Sq f := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [fourier, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum, Supply.dft_parseval]
  dsimp [l2Sq]
  field_simp

@[simp] theorem conj_fourier (f : ZMod p → ℂ) (a : ZMod p) :
    conj (fourier f a) = fourier (fun x => conj (f x)) (-a) := by
  simp only [fourier, map_mul, map_inv₀, map_natCast, Supply.conj_dft]

end
end Ostmann.FiniteField

end OAI
