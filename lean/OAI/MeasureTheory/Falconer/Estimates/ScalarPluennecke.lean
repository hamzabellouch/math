import OAI.MeasureTheory.Falconer.Estimates.ScalarRepeatedSums
import Mathlib.Data.Rat.Cast.Order

namespace OAI

/-! The application form of Pluennecke's inequality for scalar covering
numbers. Its only rounding loss is linear in the number of summands. -/
namespace Falconer
open scoped Pointwise

theorem scalar_pluennecke (δ : ℝ) (A B : Finset ℝ) (hA : A.Nonempty)
    {K : ℝ}
    (hsmall : ((scalarCells δ (A+B)).card : ℝ) ≤ K*(scalarCells δ A).card)
    (m n : ℕ) :
    ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*(2*K)^(m+n)*(scalarCells δ A).card := by
  have hAQ : (scalarCells δ A).Nonempty := Finset.image_nonempty.mpr hA
  have hAc : 0 < ((scalarCells δ A).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hAQ)
  have hR := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hAQ
    (scalarCells δ B) m n
  have hRR : ((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) ≤
      (((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card)^(m+n)*
        (scalarCells δ A).card := by
    have hReal := NNRat.cast_mono (K := ℝ) hR
    push_cast at hReal
    exact hReal
  have hsum : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
      (2*K)*(scalarCells δ A).card := by
    have hc : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
        2*((scalarCells δ (A+B)).card : ℝ) := by exact_mod_cast add_scalarCells_card δ A B
    nlinarith
  have hratio : ((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card ≤
      2*K := (div_le_iff₀ hAc).2 hsum
  have hpow := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hAc.le) hratio (m+n)
  have hbound := hRR.trans (mul_le_mul_of_nonneg_right hpow hAc.le)
  have hcarry : ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) := by
    exact_mod_cast scalar_signed_sum_card δ B m n
  have hmn : (0 : ℝ) ≤ m+n+2 := by positivity
  exact hcarry.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hmn)

end Falconer

end OAI
