import OAI.NumberTheory.Ostmann.Arithmetic.SignedRightJacobiCharacter
import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiNonsquare

namespace OAI

namespace Ostmann.Arithmetic

theorem signedRightJacobi_negative_witness {N : ℕ} (hN : 0 < N) :
    (4 * N - 1).Coprime (4 * N) ∧
      signedRightJacobi (-(N : ℤ)) (4 * N - 1) = -1 := by
  let m := 4 * N - 1
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hsucc : m + 1 = 4 * N := by dsimp [m]; omega
  have hm4 : m % 4 = 3 := by omega
  have hodd : Odd m := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hm4)
  have hcop : m.Coprime (4 * N) := by
    rw [← hsucc]
    simp
  refine ⟨hcop, ?_⟩
  change signedRightJacobi (-(N : ℤ)) m = -1
  have hcong : Nat.ModEq m (4 * N) 1 := by
    change (4 * N) % m = 1 % m
    rw [← hsucc, Nat.add_mod]
    simp
  have hjmul : jacobiSym ((4 * N : ℕ) : ℤ) m = 1 := by
    rw [Ostmann.QuadraticSieve.jacobi_nat_modEq hcong]
    simp
  have htwo : (2 : ℤ).gcd (m : ℤ) = 1 := by
    change ((2 : ℕ) : ℤ).gcd (m : ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_two_left.mpr hodd).gcd_eq_one
  have hjfour : jacobiSym 4 m = 1 := by
    simpa using jacobiSym.sq_one' htwo
  have hjN : jacobiSym (N : ℤ) m = 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left, hjfour, one_mul] using hjmul
  simp only [signedRightJacobi, ite_eq_left hodd, jacobiSym.neg _ hodd,
    ZMod.χ₄_nat_three_mod_four hm4, hjN, mul_one]

theorem exists_signedRightJacobi_nonresidue (n : ℤ) (hn : n ≠ 0) (hns : ¬ IsSquare n) :
    ∃ a : ℕ, a.Coprime (4 * n.natAbs) ∧ signedRightJacobi n a = -1 := by
  have hN : 0 < n.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hn)
  by_cases hneg : n < 0
  · have heq : n = -(n.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_neg hneg, neg_neg]
    obtain ⟨hcop, hval⟩ := signedRightJacobi_negative_witness hN
    exact ⟨4 * n.natAbs - 1, hcop, by simpa only [← heq] using hval⟩
  · have heq : n = (n.natAbs : ℤ) := Int.eq_natAbs_of_nonneg (le_of_not_gt hneg)
    have hNns : ¬ IsSquare n.natAbs := by
      intro hs
      apply hns
      rw [heq]
      exact Int.isSquare_natCast_iff.mpr hs
    obtain ⟨a, hac, ha⟩ := Ostmann.QuadraticCenter.exists_nonsquare_right_nonresidue hN hNns
    refine ⟨a, hac, ?_⟩
    rw [heq]
    exact ha

theorem signedRightJacobiCharacter_ne_one (n : ℤ) (hn : n ≠ 0) (hns : ¬ IsSquare n) :
    signedRightJacobiCharacter n hn ≠ 1 := by
  obtain ⟨a, hac, ha⟩ := exists_signedRightJacobi_nonresidue n hn hns
  intro h
  have he := congrArg (fun χ : DirichletCharacter ℂ (4 * n.natAbs) =>
    χ (a : ZMod (4 * n.natAbs))) h
  rw [signedRightJacobiCharacter_natCast, ha,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime a (4 * n.natAbs)).mpr hac)] at he
  norm_num at he

theorem signedRightJacobiCharacter_prime (n : ℤ) (hn : n ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    signedRightJacobiCharacter n hn (p : ZMod (4 * n.natAbs)) = (jacobiSym n p : ℂ) :=
  signedRightJacobiCharacter_natCast_of_odd n hn (hp.odd_of_ne_two hp2)

end Ostmann.Arithmetic

end OAI
