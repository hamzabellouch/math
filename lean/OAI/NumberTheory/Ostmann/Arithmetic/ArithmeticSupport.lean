import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination

namespace OAI

/-!
# Arithmetic support at a reversing node

These are the elementary support facts preceding the progression estimate
in Section 8. The numerator is automatically coprime to inherited slots;
the remaining condition at a new prime is exactly nondivisibility by its square.
-/

namespace Ostmann

theorem reversal_numerator_coprime (v w HL HR : ℤ)
    (hLR : IsCoprime HL HR) (hv : IsCoprime v HL) (hw : IsCoprime w HR) :
    IsCoprime (v * HR - w * HL) HL ∧ IsCoprime (v * HR - w * HL) HR := by
  constructor
  · exact IsCoprime.sub_mul_right_left_iff.mpr (hv.mul_left hLR.symm)
  · exact IsCoprime.mul_sub_right_left_iff.mpr (hw.mul_left hLR)

/-- Both the inserted integer and its compensation product inherit all required coprimalities. -/
theorem reversal_inherited_coprime (v w HL HR s u p : ℤ)
    (hLR : IsCoprime HL HR) (hv : IsCoprime v HL) (hw : IsCoprime w HR)
    (hrel : v * HR - w * HL = s * u * p) :
    IsCoprime p (HL * HR) ∧ IsCoprime u (HL * HR) := by
  obtain ⟨hL, hR⟩ := reversal_numerator_coprime v w HL HR hLR hv hw
  have hboth := hL.mul_right hR
  rw [hrel] at hboth
  exact ⟨hboth.of_mul_left_right, hboth.of_mul_left_left.of_mul_left_right⟩

/-- A prime occurring once in `u` occurs once in the numerator exactly when it misses `p`. -/
theorem reversal_square_test (b s u p : ℕ) (hb : b.Prime)
    (hbs : ¬ b ∣ s) (hbu : b ∣ u) (hbu2 : ¬ b ^ 2 ∣ u) :
    (¬ b ^ 2 ∣ s * u * p) ↔ ¬ b ∣ p := by
  obtain ⟨v, rfl⟩ := hbu
  have hbv : ¬ b ∣ v := by
    intro hv
    apply hbu2
    simpa only [pow_two] using mul_dvd_mul_left b hv
  have heq : s * (b * v) * p = b * (s * v * p) := by ring
  rw [heq, pow_two, mul_dvd_mul_iff_left hb.ne_zero]
  simp only [hb.dvd_mul, hbs, hbv, or_self, false_or]

/-- Divisibility by the frequency and all distinct new prime factors gives integer reconstruction. -/
theorem reversal_integral_of_prime_tests (s N : ℤ) (U : Finset ℕ)
    (hprime : ∀ b ∈ U, b.Prime) (hs : s ∣ N)
    (hsu : ∀ b ∈ U, IsCoprime s (b : ℤ))
    (hdiv : ∀ b ∈ U, (b : ℤ) ∣ N) :
    (s * ∏ b ∈ U, (b : ℤ)) ∣ N := by
  classical
  have hpair : (U : Set ℕ).Pairwise (fun b c => IsCoprime (b : ℤ) (c : ℤ)) := by
    intro b hb c hc hbc
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by
      simpa only [Int.gcd_natCast_natCast] using (hprime b hb).coprime_iff_not_dvd.mpr
        (fun h => hbc ((hprime c hc).eq_one_or_self_of_dvd b h |>.resolve_left (hprime b hb).ne_one)))
  have hprod : (∏ b ∈ U, (b : ℤ)) ∣ N := Finset.prod_dvd_of_coprime hpair hdiv
  have hcop : IsCoprime s (∏ b ∈ U, (b : ℤ)) := IsCoprime.prod_right hsu
  exact hcop.mul_dvd hs hprod

end Ostmann

end OAI
