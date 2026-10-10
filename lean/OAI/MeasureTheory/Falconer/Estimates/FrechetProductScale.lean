import OAI.MeasureTheory.Falconer.Estimates.FrechetCompositionScale
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frechet_mul_scale_on {U : Set E} (hU : IsOpen U) {f g : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : E} (hx : x ∈ U)
    {C₁ C₂ D₁ D₂ : ℝ} (hC₁ : 0 ≤ C₁) (_ : 0 ≤ C₂)
    (hD₁ : 0 ≤ D₁) (_ : 0 ≤ D₂) (n : ℕ)
    (hb₁ : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ C₁*D₁^j)
    (hb₂ : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ C₂*D₂^j) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ C₁*C₂*(D₁+D₂)^n := by
  have he := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at he
  apply he.trans
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (n.choose j:ℝ) * (C₁*D₁^j) * (C₂*D₂^(n-j)) := by
      gcongr
      · exact hb₁ j hjn
      · exact hb₂ (n-j) (Nat.sub_le _ _)
    _ = _ := by ring

theorem frechet_conj_norm {f : E → ℂ} {x : E} (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => star (f y)) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  exact Complex.conjLIE.norm_iteratedFDeriv_comp_left f x n

end PlanarFalconer

end OAI
