import OAI.NumberTheory.TwoPoint.Fourier.ModFiveMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open Finset Complex HurwitzZeta
open scoped BigOperators Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

lemma sum_zmod_five (f : ZMod 5 → ℂ) :
    (∑ a : ZMod 5, f a) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have hu : (univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  rw [hu, sum_insert (by decide : (0 : ZMod 5) ∉ ({1, 2, 3, 4} : Finset (ZMod 5))),
    sum_insert (by decide : (1 : ZMod 5) ∉ ({2, 3, 4} : Finset (ZMod 5))),
    sum_insert (by decide : (2 : ZMod 5) ∉ ({3, 4} : Finset (ZMod 5))),
    sum_insert (by decide : (3 : ZMod 5) ∉ ({4} : Finset (ZMod 5))), sum_singleton]
  ring_nf

lemma modFive_character_four (χ : DirichletCharacter ℂ 5) :
    χ (4 : ZMod 5) = χ (2 : ZMod 5) ^ 2 := by
  rw [← map_pow]
  congr 1

lemma modFive_character_three (χ : DirichletCharacter ℂ 5) :
    χ (3 : ZMod 5) = χ (2 : ZMod 5) ^ 3 := by
  rw [← map_pow]
  congr 1

lemma modFive_character_fourth_pow (χ : DirichletCharacter ℂ 5) :
    χ (2 : ZMod 5) ^ 4 = 1 := by
  rw [← map_pow, show (2 : ZMod 5) ^ 4 = 1 by decide, map_one]

lemma modFive_character_sum_values (χ : DirichletCharacter ℂ 5) :
    (∑ a : ZMod 5, χ a) =
      1 + χ (2 : ZMod 5) + χ (2 : ZMod 5) ^ 3 + χ (2 : ZMod 5) ^ 2 := by
  rw [sum_zmod_five, MulChar.map_zero χ, map_one,
    modFive_character_three, modFive_character_four]
  ring_nf

lemma modFive_nonprincipal_at_two (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    χ (2 : ZMod 5) ≠ 1 := by
  intro heq
  have hzero := χ.sum_eq_zero_of_ne_one hχ
  rw [modFive_character_sum_values, heq] at hzero
  norm_num at hzero

/-- The nonprincipal characters require only these three possible values. -/
theorem modFive_nonprincipal_parameter (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    χ (2 : ZMod 5) = -1 ∨ χ (2 : ZMod 5) = Complex.I ∨
      χ (2 : ZMod 5) = -Complex.I := by
  let z := χ (2 : ZMod 5)
  have hz4 : z ^ 4 = 1 := modFive_character_fourth_pow χ
  have hz2 : (z ^ 2) ^ 2 = (1 : ℂ) ^ 2 := by simpa only [← pow_mul, one_pow] using hz4
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz2 with h | h
  · have hsq : z ^ 2 = (1 : ℂ) ^ 2 := by simpa only [one_pow] using h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact False.elim (modFive_nonprincipal_at_two χ hχ h)
    · exact Or.inl h
  · have hsq : z ^ 2 = Complex.I ^ 2 := by simpa only [Complex.I_sq] using h
    exact Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)

/-- An explicit analytic function for each of the three parameters. -/
noncomputable def modFiveHurwitzCombination (z s : ℂ) : ℂ :=
  (5 : ℂ) ^ (-s) *
    (hurwitzZeta (ZMod.toAddCircle (1 : ZMod 5)) s +
      z * hurwitzZeta (ZMod.toAddCircle (2 : ZMod 5)) s +
      z ^ 3 * hurwitzZeta (ZMod.toAddCircle (3 : ZMod 5)) s +
      z ^ 2 * hurwitzZeta (ZMod.toAddCircle (4 : ZMod 5)) s)

theorem modFive_LFunction_eq (χ : DirichletCharacter ℂ 5) (s : ℂ) :
    DirichletCharacter.LFunction χ s =
      modFiveHurwitzCombination (χ (2 : ZMod 5)) s := by
  unfold DirichletCharacter.LFunction ZMod.LFunction modFiveHurwitzCombination
  rw [sum_zmod_five]
  rw [MulChar.map_zero χ, map_one, modFive_character_three, modFive_character_four]
  ring_nf

/-- The Dirichlet-series coefficients whose partial sums are required. -/
noncomputable def modFiveMangoldtTwist (χ : DirichletCharacter ℂ 5) (n : ℕ) : ℂ :=
  χ (n : ZMod 5) * (ArithmeticFunction.vonMangoldt n : ℂ)

lemma modFiveTwistedPsi_eq (χ : DirichletCharacter ℂ 5) (x : ℝ) :
    modFiveTwistedPsi χ x = ∑ n ∈ Icc 0 ⌊x⌋₊, modFiveMangoldtTwist χ n := by
  unfold modFiveTwistedPsi modFiveMangoldtTwist
  exact sum_congr rfl fun n _ => mul_comm _ _

/-- Identification with existing analytic functions on `re s > 1`. -/
theorem modFive_twisted_LSeries_eq (χ : DirichletCharacter ℂ 5) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (modFiveMangoldtTwist χ) s =
      -deriv (modFiveHurwitzCombination (χ (2 : ZMod 5))) s /
        modFiveHurwitzCombination (χ (2 : ZMod 5)) s := by
  have heq : DirichletCharacter.LFunction χ =
      modFiveHurwitzCombination (χ (2 : ZMod 5)) := funext (modFive_LFunction_eq χ)
  rw [← heq, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_twist_vonMangoldt_eq hs

theorem modFive_nonprincipal_differentiable (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) :
    Differentiable ℂ (modFiveHurwitzCombination (χ (2 : ZMod 5))) := by
  have heq : DirichletCharacter.LFunction χ =
      modFiveHurwitzCombination (χ (2 : ZMod 5)) := funext (modFive_LFunction_eq χ)
  rw [← heq]
  exact DirichletCharacter.differentiable_LFunction hχ

theorem modFive_nonprincipal_nonzero (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    modFiveHurwitzCombination (χ (2 : ZMod 5)) s ≠ 0 := by
  rw [← modFive_LFunction_eq]
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hs

end TwoPointCorrelations

end OAI
