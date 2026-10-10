import OAI.NumberTheory.Catalan.Estimates.PalindromicBlockInverse

namespace OAI


noncomputable section

namespace InternalCatalan

theorem harmonicRat_prime_scaled_reduction {p n : ℕ} [hp : Fact p.Prime]
    (hn : n < p ^ 2) :
    (((p : ℚ) * harmonicRat 1 n).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * harmonicRat 1 n) =
        palindromicRatResidue p (harmonicRat 1 (n / p)) := by
  have hquot : n / p < p := by
    apply (Nat.div_lt_iff_lt_mul hp.out.pos).mpr
    simpa only [pow_two] using hn
  have hb := harmonicRat_small_den_ne_zero (p := p) hquot 1
  have he :
      (((p : ℚ) * harmonicRat 1 n - harmonicRat 1 (n / p)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * harmonicRat 1 n - harmonicRat 1 (n / p)) = 0 := by
    have h := harmonicRat_prime_digit_error_valuation (n := n) hp.out (by decide : 0 < 1)
    simp only [pow_one] at h
    rcases h with hzero | hpos
    · rw [hzero]
      norm_num [palindromicRatResidue]
    · exact rational_residue_zero_of_positive_valuation (by omega)
  have hadd := rational_residue_add he.1 hb
  have hsplit : (p : ℚ) * harmonicRat 1 n =
      ((p : ℚ) * harmonicRat 1 n - harmonicRat 1 (n / p)) + harmonicRat 1 (n / p) := by ring
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hadd.1
  · rw [hsplit, palindromicRatResidue_add he.1 hb, he.2, zero_add]

theorem zetaRat_central_low_reduction {p i j : ℕ} [Fact p.Prime]
    (hi : i < p) (hj : j < p) :
    (((p : ℚ) * zetaRat i j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * zetaRat i j) = 0 := by
  have h := rational_residue_mul (p := p) (a := (p : ℚ)) (by simp)
    (zetaRat_small_den_ne_zero hi hj)
  refine ⟨h.1, ?_⟩
  change (((p : ℚ) * zetaRat i j).num : ZMod p) /
    (((p : ℚ) * zetaRat i j).den : ZMod p) = 0
  rw [h.2]
  simp

theorem zetaRat_central_high_reduction {p ell j : ℕ} [hp : Fact p.Prime]
    (hellj : ell < j) (hj : j < p) :
    (((p : ℚ) * zetaRat (p + ell) j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * zetaRat (p + ell) j) =
        1 / ((ell : ZMod p) - (j : ZMod p)) := by
  have hell : ell < p := hellj.trans hj
  have hi2 : p + ell < p ^ 2 := by nlinarith [hp.out.two_le]
  have hj2 : j < p ^ 2 := by nlinarith [hp.out.two_le]
  have hi := harmonicRat_prime_scaled_reduction (p := p) hi2
  have hjh := harmonicRat_prime_scaled_reduction (p := p) hj2
  have hiquot : (p + ell) / p = 1 := by
    simpa only [Nat.mul_one, Nat.div_eq_of_lt hell, add_zero] using
      (Nat.mul_add_div hp.out.pos 1 ell)
  have hirst : palindromicRatResidue p ((p : ℚ) * harmonicRat 1 (p + ell)) = 1 := by
    rw [hi.2, hiquot]
    norm_num [harmonicRat, palindromicRatResidue]
  have hjrst : palindromicRatResidue p ((p : ℚ) * harmonicRat 1 j) = 0 := by
    rw [hjh.2, Nat.div_eq_of_lt hj]
    norm_num [palindromicRatResidue]
  have hsub := rational_residue_sub hi.1 hjh.1
  have hsubres : palindromicRatResidue p
      ((p : ℚ) * harmonicRat 1 (p + ell) - (p : ℚ) * harmonicRat 1 j) = 1 := by
    rw [palindromicRatResidue_sub hi.1 hjh.1, hirst, hjrst, sub_zero]
  have hdenpos : 0 < p + ell - j := by omega
  have hdenlt : p + ell - j < p := by omega
  have hden : ((p + ell - j : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdenpos hdenlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hf := nat_fraction_reduced_residue (p := p) 1 (p + ell - j) hden
  simp only [Nat.cast_one] at hf
  have hm := rational_residue_mul hsub.1 hf.1
  have hsplit : (p : ℚ) * zetaRat (p + ell) j =
      ((p : ℚ) * harmonicRat 1 (p + ell) - (p : ℚ) * harmonicRat 1 j) *
        (1 / ((p + ell - j : ℕ) : ℚ)) := by
    rw [zetaRat_of_ne (by omega : p + ell ≠ j), Nat.cast_sub (by omega : j ≤ p + ell)]
    ring
  have hdenres : ((p + ell - j : ℕ) : ZMod p) = (ell : ZMod p) - (j : ZMod p) := by
    rw [Nat.cast_sub (by omega : j ≤ p + ell), Nat.cast_add]
    simp
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hm.1
  · rw [hsplit, palindromicRatResidue_mul hsub.1 hf.1, hsubres]
    change 1 * (((1 / ((p + ell - j : ℕ) : ℚ)).num : ZMod p) /
      ((1 / ((p + ell - j : ℕ) : ℚ)).den : ZMod p)) = _
    rw [hf.2, hdenres, one_mul]

end InternalCatalan

end

end OAI
