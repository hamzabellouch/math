import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPoissonParameters

namespace OAI

/-! # Uniform power-saving coprime Poisson summation

This proves the concrete Schwartz-function form of Heath-Brown (1995),
Lemma 13, needed in the two quadratic-sieve error estimates.
-/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_uniform_coprime_poisson (ψ : 𝓢(ℝ, ℂ)) (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) -
        quadraticPoissonCore q ψ X U V L‖ ≤ C * X / J ^ a := by
  obtain ⟨C, hC, hc⟩ := quadratic_truncated_poisson_bound ψ (a + 2)
  refine ⟨3 * C + 1, by positivity, ?_⟩
  intro q _ hq1 X U V J hX hU hV hJ hUJ hJV L hL
  have hUX : U ≤ X := (le_mul_of_one_le_right hU.le hJ).trans hUJ
  have hXV : X ≤ V := (le_mul_of_one_le_right hX.le hJ).trans hJV
  have hbound := hc q hq1 X U V hX hU (hUX.trans hXV) L
  have hparam := quadratic_poisson_parameter_budget a L hX hU hV hJ hUJ hJV hL
  have hparam' :
      U * (U / X) ^ (a + 2 + 1) + X * (X / V) ^ (a + 2 + 1) +
      V * (V / X) ^ (a + 2 + 1) / ((L : ℝ) + 1) ^ (a + 2) ≤ 3 * X / J ^ a := by
    simpa only [Nat.add_assoc] using hparam
  calc
    _ ≤ C * (U * (U / X) ^ (a + 2 + 1) + X * (X / V) ^ (a + 2 + 1) +
        V * (V / X) ^ (a + 2 + 1) / ((L : ℝ) + 1) ^ (a + 2)) := hbound
    _ ≤ C * (3 * X / J ^ a) := mul_le_mul_of_nonneg_left hparam' hC
    _ ≤ (3 * C + 1) * X / J ^ a := by
      have hj0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
      have hxj : 0 ≤ X / J ^ a := div_nonneg hX.le (pow_nonneg hj0.le _)
      calc
        _ = (3 * C) * (X / J ^ a) := by ring
        _ ≤ (3 * C + 1) * (X / J ^ a) := mul_le_mul_of_nonneg_right (by linarith) hxj
        _ = _ := by ring

end Ostmann

end OAI
