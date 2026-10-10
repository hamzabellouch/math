import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstCoprimeTransform
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSignedFiniteCutoff

namespace OAI

/-! # The finite second-Poisson family and its proved first-transform tail -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticFirstFiniteFrequency (ψ : 𝓢(ℝ, ℂ))
    (M : ℝ) (e q K : ℕ) : ℂ :=
  ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
    ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        𝓕 ψ ((a : ℝ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M))

theorem quadratic_first_frequency_cutoff (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ), 0 < M → ∀ e q K : ℕ, 0 < e → 1 < q →
      ‖(∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
        𝓕 ψ ((h : ℝ) * M / ((e : ℝ) * q))) -
          quadraticFirstFiniteFrequency ψ M e q K‖ ≤
        C / ((M / ((e : ℝ) * q)) ^ (A + 2) * ((K : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_kernel_tail (𝓕 ψ) A
  refine ⟨C, hC, ?_⟩
  intro M hM e q K he hq
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  let Y := M / ((e : ℝ) * q)
  have hY : 0 < Y := div_pos hM (mul_pos heR hqR)
  let F : ℤ → ℂ := fun h => (jacobiSym ((e : ℤ) * h) q : ℂ) * 𝓕 ψ ((h : ℝ) * Y)
  have hF : Summable (fun h => ‖F h‖) :=
    (quadratic_jacobi_frequency_summable (𝓕 ψ) hY e q).norm
  have hzero : F 0 = 0 := by
    simp only [F, mul_zero, jacobiSym.zero_left hq, Int.cast_zero, zero_mul]
  have hfinite : (∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
      ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b)) = quadraticFirstFiniteFrequency ψ M e q K := by
    unfold quadraticFirstFiniteFrequency
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [F, Y]
    simp only [← mul_div_assoc]
    exact quadratic_first_square_term (by omega) hM ψ a b
  have hs := quadratic_signed_finite_cutoff F hzero hF K
  rw [hfinite] at hs
  simp only [mul_div_assoc]
  change ‖(∑' h : ℤ, F h) - quadraticFirstFiniteFrequency ψ M e q K‖ ≤ _
  rw [hs, add_sub_cancel_left]
  exact hc Y hY e q K

end Ostmann

end OAI
