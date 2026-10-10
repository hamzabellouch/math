import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import OAI.NumberTheory.Ostmann.Characters.RescaledWeightVariation

namespace OAI

/-! # Concrete variation bounds for the quadratic Schwartz weight -/

namespace Ostmann

open scoped SchwartzMap

theorem schwartz_norm_sub_le (Φ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    ‖Φ x - Φ y‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ * |x - y| := by
  have hd (z : ℝ) : ‖fderiv ℝ Φ z‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ := by
    simpa only [norm_iteratedFDeriv_one] using Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (s := Set.univ) (fun _ _ => Φ.differentiableAt)
    (fun z _ => hd z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

/-- Pullback along the squaring map is still a Schwartz function on the line.
This is the weight appearing after writing a frequency as `s*v*w^2`. -/
noncomputable def quadraticSchwartzWeight (Φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => x ^ 2) (by fun_prop)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow]
      nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]⟩ Φ

theorem quadraticSchwartzWeight_apply (Φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticSchwartzWeight Φ x = Φ (x ^ 2) := rfl

theorem schwartz_rescaled_variation (Φ : 𝓢(ℝ, ℂ)) (ξ Y C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hN : (N : ℝ) ≤ C * Y) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤
      SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ 0 1 Φ * C := by
  have hD : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Φ :=
    (norm_nonneg _).trans (Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 0)
  exact rescaledPhaseWeight_variation_uniform Φ ξ Y _ _ C N hY hD hN
    (Φ.norm_le_seminorm ℝ) (schwartz_norm_sub_le Φ)

theorem quadratic_schwartz_rescaled_variation (Φ : 𝓢(ℝ, ℂ)) (ξ Y C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hN : (N : ℝ) ≤ C * Y) :
    discreteVariation (fun j : ℕ => Φ ((((j : ℝ) + ξ) / Y) ^ 2)) N ≤
      SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) +
        SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * C :=
  schwartz_rescaled_variation (quadraticSchwartzWeight Φ) ξ Y C N hY hN

end Ostmann

end OAI
