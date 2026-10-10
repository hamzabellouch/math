import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzProfileSampling

namespace OAI

/-! # Uniform sampling from the profile's finite symbol bounds -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffProfile_sampling_of_global_symbol (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L),
      ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
        (cutoffProfileSchwartz L (lt_of_lt_of_le zero_lt_one hL) χ hχ Q hQ))‖ ≤ C := by
  classical
  obtain ⟨N, hN⟩ := exists_cutoffProfile_sampling_bound a k ha ha1 hk χ hχ hχzero
  choose D hD hb using hsymbol
  let B := ∑ j ∈ Finset.range (N + 1), D j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hD j)
  apply hN Q hQ B hB
  intro j hj y hy
  apply (hb j y hy).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Finset.single_le_sum (fun i _ => hD i)
    (Finset.mem_range.mpr (by omega))

end DefocusingNLS

end OAI
