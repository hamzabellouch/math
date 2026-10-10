import OAI.NumberTheory.Ostmann.ZeroDensity.ResiduePsiSmallModulus
import OAI.NumberTheory.Ostmann.ZeroDensity.ResiduePsiLargeModulus

namespace OAI

/-! # Uniform sharp Mangoldt estimate with the canonical Page term -/

namespace Ostmann

open Filter

theorem residuePsi_eventual_bound : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, a.Coprime q →
      |residuePsi q a X - thetaMainTerm q.totient
        (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          C * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, hsmall⟩ := residuePsi_small_modulus_bound
  obtain ⟨D, hD, hlarge⟩ := residuePsi_large_modulus_bound
  let c := min d (1 / 4)
  refine ⟨c, 35 + D, lt_min hd (by norm_num), by positivity, ?_⟩
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with X hs hl hX
  intro q hq a ha
  have hc : 0 ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  have hexp1 : Real.exp (-d * Real.sqrt (Real.log X)) ≤
      Real.exp (-c * Real.sqrt (Real.log X)) :=
    Real.exp_le_exp.mpr (by dsimp [c]; nlinarith [min_le_left d (1 / 4)])
  have hexp2 : Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log X)) ≤
      Real.exp (-c * Real.sqrt (Real.log X)) :=
    Real.exp_le_exp.mpr (by dsimp [c]; nlinarith [min_le_right d (1 / 4)])
  by_cases hqX : (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X) / 2)
  · exact (hs q hq hqX a ha).trans (by
      have hm := mul_le_mul_of_nonneg_left hexp1 (show 0 ≤ 35 * X by positivity)
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith : 0 ≤ X))
          (Real.exp_nonneg _)))
  · exact (hl q (by omega) (le_of_not_ge hqX) a).trans (by
      have hm := mul_le_mul_of_nonneg_left hexp2 (show 0 ≤ D * X by positivity)
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith : 0 ≤ X))
          (Real.exp_nonneg _)))

end Ostmann

end OAI
