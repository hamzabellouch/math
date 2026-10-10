import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUniformPoisson

namespace OAI

/-! # Recovering the positive half of an even coprime Poisson sum -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_coprime_summable {q : ℕ} [NeZero q]
    (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℤ => (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      ψ ((n : ℝ) / X)) := by
  apply Summable.of_norm_bounded (quadratic_scaled_summable ψ hX)
  intro n
  rw [principal_character_intCast]
  split_ifs <;> simp

theorem quadratic_coprime_positive_half {q : ℕ} [NeZero q] (hq : q ≠ 1)
    (ψ : 𝓢(ℝ, ℂ)) (heven : Function.Even ψ) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      2 * ∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ψ ((n : ℝ) / X) := by
  have hf : Function.Even (fun n : ℤ =>
      (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) := by
    intro n
    change (1 : DirichletCharacter ℂ q) ((-n : ℤ) : ZMod q) *
      ψ (((-n : ℤ) : ℝ) / X) =
        (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)
    rw [principal_character_intCast, principal_character_intCast]
    rw [Int.cast_neg, neg_div, heven ((n : ℝ) / X)]
    congr 2
    simp only [Int.gcd, Int.natAbs_neg]
  have hzero : (1 : DirichletCharacter ℂ q) (0 : ZMod q) = 0 := by
    simpa [hq] using (principal_character_intCast (d := q) (0 : ℤ))
  have hh := tsum_int_eq_zero_add_two_mul_tsum_pnat hf (quadratic_coprime_summable ψ hX)
  simpa [hzero, two_smul, ← two_mul] using hh

theorem quadratic_uniform_positive_poisson (ψ : 𝓢(ℝ, ℂ)) (heven : Function.Even ψ)
    (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) -
        quadraticPoissonCore q ψ X U V L / 2‖ ≤ C * X / J ^ a := by
  obtain ⟨C, hC, hc⟩ := quadratic_uniform_coprime_poisson ψ a
  refine ⟨C, hC, ?_⟩
  intro q _ hq X U V J hX hU hV hJ hUJ hJV L hL
  have hh := hc q hq X U V J hX hU hV hJ hUJ hJV L hL
  rw [quadratic_coprime_positive_half hq ψ heven hX] at hh
  have hid : (∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      ψ ((n : ℝ) / X)) - quadraticPoissonCore q ψ X U V L / 2 =
      (2 * (∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ψ ((n : ℝ) / X)) - quadraticPoissonCore q ψ X U V L) / 2 := by ring
  rw [hid, norm_div]
  norm_num only [Complex.norm_ofNat]
  have hp : 0 ≤ C * X / J ^ a := by positivity
  exact (div_le_div_of_nonneg_right hh (by norm_num)).trans (by linarith)

end Ostmann

end OAI
