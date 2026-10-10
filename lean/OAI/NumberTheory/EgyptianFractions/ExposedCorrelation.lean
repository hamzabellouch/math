import OAI.NumberTheory.EgyptianFractions.RandomProductFourier
import OAI.NumberTheory.EgyptianFractions.ReducedCharacter

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A constant phase has no effect on the norm of a normalized additive-character
average. The averaging set is an arbitrary finite type. -/
lemma norm_character_average_sub {ι : Type*} [Fintype ι]
    {u : ℕ} [NeZero u] (f : ι → ZMod u) (t : ZMod u) (D : ℂ) :
    ‖(∑ i : ι, ZMod.stdAddChar (f i - t)) / D‖ =
      ‖(∑ i : ι, ZMod.stdAddChar (f i)) / D‖ := by
  simp_rw [AddChar.map_sub_eq_div]
  rw [← Finset.sum_div, div_right_comm, norm_div, AddChar.norm_apply, div_one]

/-- The correlation bound after exposing all but two independent prime products.
The effective modulus is `u / gcd(a,u)`, and no coprimality of `a` and `u` is
assumed. -/
theorem exposed_prime_correlation_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hne : P.Nonempty)
    (s a u : ℕ) (hu : 0 < u) [NeZero u] [NeZero (u / a.gcd u)]
    (hsmall : ∀ w : Fin s → ↥P, (∏ i, (w i : ℕ)) < u / a.gcd u)
    (t : ZMod u) :
    ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
      ZMod.stdAddChar
        (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
        ((P.card : ℂ)^s)^2‖ ≤
      Real.sqrt ((u / a.gcd u : ℕ) : ℝ) *
        ((s.factorial : ℝ) / (P.card : ℝ)^s) := by
  have hshift :
      ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
        ZMod.stdAddChar
          (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
          ((P.card : ℂ)^s)^2‖ =
      ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
        ZMod.stdAddChar
          ((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u)) /
          ((P.card : ℂ)^s)^2‖ := by
    simp_rw [AddChar.map_sub_eq_div, ← Finset.sum_div]
    rw [div_right_comm, norm_div, AddChar.norm_apply, div_one]
  rw [hshift]
  have hp := prime_product_bilinear_average_bound P hP hne s
    (u / a.gcd u) hsmall (reducedFrequency a u hu)
  convert hp using 1
  congr 2
  apply Finset.sum_congr rfl
  intro w₁ _
  apply Finset.sum_congr rfl
  intro w₂ _
  rw [Nat.mul_assoc, stdAddChar_reduced a u _ hu, Nat.cast_mul, mul_assoc]
  simp only [Nat.cast_prod]

/-- Numerically, the square-root loss in the modulus changes an atom bound
`exp(-7 V / 10)` into the correlation bound `exp(-V / 5)`. -/
lemma sqrt_mul_atom_le_exp {q A V : ℝ}
    (hq : q ≤ Real.exp V) (hA : A ≤ Real.exp (-7 * V / 10)) (hA0 : 0 ≤ A) :
    Real.sqrt q * A ≤ Real.exp (-V / 5) := by
  have hsqrt : Real.sqrt q ≤ Real.exp (V / 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have heq : Real.exp (V / 2) ^ 2 = Real.exp V := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [heq]
    exact hq
  calc
    _ ≤ Real.exp (V / 2) * Real.exp (-7 * V / 10) :=
      mul_le_mul hsqrt hA hA0 (Real.exp_pos _).le
    _ = Real.exp (-V / 5) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The good-exposure estimate in the random-product argument. The product
size and atom decay hypotheses are separated from the algebraic cancellation. -/
theorem exposed_prime_correlation_le_exp
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hne : P.Nonempty)
    (s a u : ℕ) (hu : 0 < u) [NeZero u] [NeZero (u / a.gcd u)]
    (hsmall : ∀ w : Fin s → ↥P, (∏ i, (w i : ℕ)) < u / a.gcd u)
    (t : ZMod u) (V : ℝ) (huV : (u : ℝ) ≤ Real.exp V)
    (hatom : (s.factorial : ℝ) / (P.card : ℝ)^s ≤ Real.exp (-7 * V / 10)) :
    ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
      ZMod.stdAddChar
        (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
        ((P.card : ℂ)^s)^2‖ ≤ Real.exp (-V / 5) := by
  apply (exposed_prime_correlation_bound P hP hne s a u hu hsmall t).trans
  apply sqrt_mul_atom_le_exp _ hatom (by positivity)
  have hqu : ((u / a.gcd u : ℕ) : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast Nat.div_le_self u (a.gcd u)
  exact hqu.trans huV

end Problem337

end

end OAI
