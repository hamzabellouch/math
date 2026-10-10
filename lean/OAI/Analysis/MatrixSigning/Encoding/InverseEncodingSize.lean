import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize

namespace OAI

section

namespace KS.W01

theorem inverse_parts_le_two_pow_length (q : ℚ) :
    (q⁻¹).num.natAbs ≤ 2 ^ ratLength q ∧ (q⁻¹).den ≤ 2 ^ ratLength q := by
  obtain ⟨hnum, hden⟩ := rational_parts_le_two_pow_length q
  constructor
  · apply le_trans (b := q.den) _ hden
    rw [Rat.num_inv, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_sign]
    split_ifs <;> simp
  · rw [Rat.den_inv]
    split_ifs
    · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    · exact hnum

theorem ratLength_inv_le (q : ℚ) : ratLength (q⁻¹) ≤ 4 * ratLength q + 7 := by
  obtain ⟨hn, hd⟩ := inverse_parts_le_two_pow_length q
  have h := ratLength_le_of_parts (q⁻¹) _ _ hn hd
  omega

theorem ratLength_div_le (q r : ℚ) :
    ratLength (q / r) ≤ 4 * (ratLength q + ratLength r) + 7 := by
  obtain ⟨hqn, hqd⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrn, hrd⟩ := inverse_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.mul_parts_le_two_pow q (r⁻¹)
    (ratLength q) (ratLength r) hqn hqd hrn hrd
  rw [div_eq_mul_inv]
  have h := ratLength_le_of_parts (q * r⁻¹) _ _ hn hd
  omega

theorem ratLength_normSq_le (z : RationalComplex) :
    ratLength (RationalComplex.normSq z) ≤ 32 * complexLength z + 65 := by
  have hre := ratLength_mul_le z.1 z.1
  have him := ratLength_mul_le z.2 z.2
  have hadd := ratLength_add_le (z.1 * z.1) (z.2 * z.2)
  simp only [complexLength_eq]
  unfold RationalComplex.normSq
  omega

theorem complexLength_inv_le (z : RationalComplex) :
    complexLength (RationalComplex.inv z) ≤ 272 * complexLength z + 562 := by
  have hn := ratLength_normSq_le z
  have hneg := ratLength_neg_le z.2
  have hre := ratLength_div_le z.1 (RationalComplex.normSq z)
  have him := ratLength_div_le (-z.2) (RationalComplex.normSq z)
  simp only [complexLength_eq] at hn ⊢
  simp only [RationalComplex.inv]
  omega

end KS.W01

end

end OAI
