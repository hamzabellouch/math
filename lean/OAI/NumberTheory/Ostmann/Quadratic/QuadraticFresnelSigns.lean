import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussSign
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelMain
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticEulerAtTwo

namespace OAI

/-! # The four signed-square classes in the first Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticFresnelSignSum (q : ℕ) : ℂ :=
  ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
    (jacobiSym a q : ℂ) * quadraticFresnelPhase a /
      (Real.sqrt |(a : ℝ)| : ℂ)

theorem quadratic_fresnel_sign_sum {q : ℕ} (hq : Squarefree q) (ho : Odd q) :
    quadraticGaussMultiplier q * quadraticFresnelSignSum q =
      2 * (1 + quadraticRootCharacter q 2) := by
  have hneg : jacobiSym (-2) q = jacobiSym (-1) q * jacobiSym 2 q := by
    rw [show (-2 : ℤ) = -1 * 2 by norm_num, jacobiSym.mul_left]
  rw [quadraticGaussMultiplier_odd_squarefree hq ho]
  by_cases hq₁ : q % 4 = 1
  · have hn : jacobiSym (-1) q = 1 := by
      rw [jacobiSym.at_neg_one ho, ZMod.χ₄_nat_one_mod_four hq₁]
    simp [quadraticFresnelSignSum, quadraticFresnelPhase, hq₁, hn, hneg,
      quadraticRootCharacter]
    ring
  · have hq₃ : q % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ho) with hh | hh
      · exact (hq₁ hh).elim
      · exact hh
    have hn : jacobiSym (-1) q = -1 := by
      rw [jacobiSym.at_neg_one ho, ZMod.χ₄_nat_three_mod_four hq₃]
    simp [quadraticFresnelSignSum, quadraticFresnelPhase, hq₁, hn, hneg,
      quadraticRootCharacter]
    ring_nf
    simp [Complex.I_sq]

theorem quadratic_root_two_square {q : ℕ} (ho : Odd q) :
    quadraticRootCharacter q 2 ^ 2 = (1 / 2 : ℂ) := by
  have hj : jacobiSym (2 : ℤ) q ^ 2 = 1 :=
    jacobiSym.sq_one (by exact ho.coprime_two_left)
  have hs : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [quadraticRootCharacter, div_pow]
  norm_num only [Nat.cast_ofNat]
  rw [← Int.cast_pow, hj, Int.cast_one, hs]

end Ostmann

end OAI
