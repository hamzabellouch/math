import OAI.NumberTheory.Ostmann.Supply.ResidueVectorNorm
import OAI.NumberTheory.Ostmann.Preliminaries.SymmetricBlockEnergy

namespace OAI

/-! # Two-by-two control of the actual finite residue blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Cauchy--Schwarz and the vector triangle inequality reduce the finite
kernel block to its scalar matrix of bounds, without a dimension factor. -/
theorem residue_block_energy {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (C : (ZMod p → ℂ) → ZMod p → ℂ)
    (s d r : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hgap : d + 1 / 20 ≤ s)
    (ha : ‖a‖ ≤ s) (hrow : residueVectorNorm row ≤ r)
    (hcol : residueVectorNorm col ≤ r)
    (hC : ∀ f, residueVectorNorm (C f) ≤ d * residueVectorNorm f)
    (z : ℂ) (f : ZMod p → ℂ) :
    ‖a * z + ∑ x, conj (row x) * f x‖ ^ 2 +
      residueVectorNorm (fun x => z * col x + C f x) ^ 2 ≤
      (s + 20 * r ^ 2) ^ 2 * (‖z‖ ^ 2 + residueVectorNorm f ^ 2) := by
  have hleft : ‖a * z + ∑ x, conj (row x) * f x‖ ≤
      s * ‖z‖ + r * residueVectorNorm f := by
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
      ((residueVectorNorm_inner_le row f).trans
        (mul_le_mul_of_nonneg_right hrow (residueVectorNorm_nonneg _)))
  have hright : residueVectorNorm (fun x => z * col x + C f x) ≤
      r * ‖z‖ + d * residueVectorNorm f := by
    apply (residueVectorNorm_add_le _ _).trans
    rw [residueVectorNorm_smul]
    exact add_le_add (by nlinarith only [mul_le_mul_of_nonneg_left hcol (norm_nonneg z)]) (hC f)
  apply (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hleft 2)
    (pow_le_pow_left₀ (residueVectorNorm_nonneg _) hright 2)).trans
  exact symmetric_block_energy s d r ‖z‖ (residueVectorNorm f) hs hd hgap

end Ostmann

end OAI
