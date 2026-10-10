import OAI.NumberTheory.Jacobsthal.Primes.OddPrimeRoots

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

theorem two_pow_dvd_of_four_not_dvd (s : ℕ) (a b : ℤ) (ha : ¬4 ∣ a)
    (hab : (2 : ℤ)^(s+1) ∣ a*b) : (2 : ℤ)^s ∣ b := by
  have hp : Prime (2 : ℤ) := by norm_num
  by_cases htwo : (2 : ℤ) ∣ a
  · obtain ⟨c, rfl⟩ := htwo
    have hc : ¬(2 : ℤ) ∣ c := by
      rintro ⟨d, rfl⟩
      exact ha ⟨d, by ring⟩
    have hcan : (2 : ℤ)^s ∣ c*b := by
      apply (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp
      simpa only [pow_succ', mul_assoc] using hab
    exact hp.pow_dvd_of_dvd_mul_left s hc hcan
  · exact (pow_dvd_pow (2 : ℤ) (Nat.le_succ s)).trans
      (hp.pow_dvd_of_dvd_mul_left (s+1) htwo hab)

theorem two_power_square_congruence (s : ℕ) (x y : ℤ) (hy : ¬(2 : ℤ) ∣ y)
    (hxy : (2 : ℤ)^(s+1) ∣ x^2-y^2) :
    (2 : ℤ)^s ∣ x-y ∨ (2 : ℤ)^s ∣ x+y := by
  have hproduct : (2 : ℤ)^(s+1) ∣ (x-y)*(x+y) := by
    convert hxy using 1; ring
  by_cases hm : (4 : ℤ) ∣ x-y
  · have hp : ¬(4 : ℤ) ∣ x+y := by
      intro hp
      have h2y : (4 : ℤ) ∣ 2*y := by
        have he : (x+y)-(x-y) = 2*y := by ring
        simpa only [he] using dvd_sub hp hm
      apply hy
      apply (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp
      exact h2y
    exact Or.inl (two_pow_dvd_of_four_not_dvd s (x+y) (x-y) hp
      (by simpa only [mul_comm] using hproduct))
  · exact Or.inr (two_pow_dvd_of_four_not_dvd s (x-y) (x+y) hm hproduct)

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
