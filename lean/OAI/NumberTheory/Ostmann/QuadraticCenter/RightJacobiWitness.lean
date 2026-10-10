import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveJacobiCharacter

namespace OAI

namespace Ostmann.QuadraticCenter

theorem exists_coprime_lift {d M b : ℕ} (hM : 0 < M) (hd : d ∣ M)
    (hb : b.Coprime d) : ∃ a : ℕ, a.Coprime M ∧ Nat.ModEq d a b := by
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero d := ⟨by intro hz; subst d; exact hM.ne' (by simpa using hd)⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime b hb)
  refine ⟨(u : ZMod M).val, ZMod.val_coe_unit_coprime u, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ d).mp
  have he := congrArg (fun z : (ZMod d)ˣ => (z : ZMod d)) hu
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at he
  simpa only [ZMod.natCast_val] using he

theorem exists_odd_squarefree_right_nonresidue {q : ℕ}
    (hq : Odd q) (hsq : Squarefree q) (hq1 : q ≠ 1) :
    ∃ a : ℕ, a % 8 = 1 ∧ a.Coprime q ∧ jacobiSym (q : ℤ) a = -1 := by
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
  obtain ⟨b, hbmod, hbj⟩ := Ostmann.QuadraticSieve.exists_jacobi_neg_one_congr_one
    hq hsq hp hpq (one_dvd q) (by
      intro h
      exact hp.ne_one (Nat.dvd_one.mp h))
  have hbq : b.Coprime q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h
    have hh : Int.gcd (b : ℤ) (q : ℤ) ≠ 1 := by simpa using h
    have hz := jacobiSym.eq_zero_iff.mpr ⟨hsq.ne_zero, hh⟩
    rw [hbj] at hz
    norm_num at hz
  have h8q : Nat.Coprime 8 q := by
    simpa using (Nat.coprime_two_left.mpr hq).pow_left 3
  obtain ⟨a, ha8, haq⟩ := Nat.chineseRemainder h8q 1 b
  have ha8' : a % 8 = 1 := by simpa only [Nat.ModEq, Nat.one_mod] using ha8
  have haq' : a.Coprime q := by
    change Nat.gcd a q = 1
    rw [haq.gcd_eq]
    exact hbq
  have ha4 : a % 4 = 1 := by
    have hh := ha8.of_dvd (by norm_num : 4 ∣ 8)
    simpa only [Nat.ModEq, Nat.one_mod] using hh
  refine ⟨a, ha8', haq', ?_⟩
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' hq ha4,
    Ostmann.QuadraticSieve.jacobi_nat_modEq haq, hbj]

theorem exists_squarefree_right_nonresidue {q : ℕ}
    (hsq : Squarefree q) (hq1 : q ≠ 1) :
    ∃ a : ℕ, a.Coprime (8 * q) ∧ Odd a ∧ jacobiSym (q : ℤ) a = -1 := by
  by_cases hq : Odd q
  · obtain ⟨a, ha8, haq, haj⟩ := exists_odd_squarefree_right_nonresidue hq hsq hq1
    have ha2 : Odd a := by
      rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd a (by norm_num : 2 ∣ 8), ha8]
    have hac8 : a.Coprime 8 := by
      simpa using (Nat.coprime_two_right.mpr ha2).pow_right 3
    exact ⟨a, Nat.coprime_mul_iff_right.mpr ⟨hac8, haq⟩, ha2, haj⟩
  · have hqe : Even q := Nat.not_odd_iff_even.mp hq
    obtain ⟨v, hv⟩ := even_iff_two_dvd.mp hqe
    subst q
    have hsplit := Nat.squarefree_mul_iff.mp hsq
    have hvodd : Odd v := Nat.coprime_two_left.mp hsplit.1
    by_cases hv1 : v = 1
    · subst v
      refine ⟨5, by norm_num, by decide, ?_⟩
      norm_num
    · obtain ⟨a, ha8, hav, haj⟩ := exists_odd_squarefree_right_nonresidue hvodd hsplit.2.2 hv1
      have ha2 : Odd a := by
        rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd a (by norm_num : 2 ∣ 8), ha8]
      have hac2 : a.Coprime 2 := Nat.coprime_two_right.mpr ha2
      have hac16 : a.Coprime 16 := by simpa using hac2.pow_right 4
      have hac : a.Coprime (8 * (2 * v)) := by
        rw [show 8 * (2 * v) = 16 * v by ring]
        exact Nat.coprime_mul_iff_right.mpr ⟨hac16, hav⟩
      refine ⟨a, hac, ha2, ?_⟩
      rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.at_two ha2, haj,
        ZMod.χ₈_nat_eq_if_mod_eight]
      have haodd := Nat.odd_iff.mp ha2
      simp [haodd, ha8]

end Ostmann.QuadraticCenter

end OAI
