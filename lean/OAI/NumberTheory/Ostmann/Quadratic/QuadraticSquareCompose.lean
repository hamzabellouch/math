import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogRootKernel

namespace OAI

/-! # The actual square-composed Schwartz test for the second Poisson step -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

private theorem quadratic_square_proper {a : ℝ} (ha : 1 ≤ |a|) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖a * x ^ 2‖) ^ k := by
  refine ⟨1, 1, ?_⟩
  intro x
  simp only [pow_one, one_mul, Real.norm_eq_abs, abs_mul, abs_pow]
  have hm : |x| ^ 2 ≤ |a| * |x| ^ 2 := le_mul_of_one_le_left (sq_nonneg _) ha
  nlinarith [sq_nonneg (|x| - 1), sq_nonneg |x|]

noncomputable def quadraticSquareCompose (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => a * x ^ 2) (by fun_prop)
    (quadratic_square_proper ha) ρ

 theorem quadraticSquareCompose_apply (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) (x : ℝ) :
    quadraticSquareCompose ρ a ha x = ρ (a * x ^ 2) := rfl

 theorem quadraticSquareCompose_even (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    Function.Even (quadraticSquareCompose ρ a ha) := by
  intro x
  simp only [quadraticSquareCompose_apply, neg_sq]

noncomputable def quadraticFourierSquare (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) : 𝓢(ℝ, ℂ) :=
  quadraticSquareCompose (𝓕 ρ) a ha

 theorem quadraticFourierSquare_apply (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) (x : ℝ) :
    quadraticFourierSquare ρ a ha x = 𝓕 ρ (a * x ^ 2) := rfl

 theorem quadraticFourierSquare_even (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    Function.Even (quadraticFourierSquare ρ a ha) :=
  quadraticSquareCompose_even _ _ _

end Ostmann

end OAI
