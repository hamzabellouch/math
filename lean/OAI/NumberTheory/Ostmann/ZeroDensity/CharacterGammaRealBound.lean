import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedDivergence

namespace OAI

/-! # Uniform archimedean error on the real interval used by the zero argument -/

namespace Ostmann

open Complex Set
open scoped Classical

theorem gammaReal_analyticAt_pos (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gammaℝ z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  apply gammaReal_differentiableAt
  intro n hn
  have hh := congrArg Complex.re hn
  simp only [div_ofNat_re, neg_re, natCast_re] at hh
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem gammaReal_logDeriv_real_bound : ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 1 ≤ t → t ≤ 3 → ‖logDeriv Complex.Gammaℝ (t : ℂ)‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ => logDeriv Complex.Gammaℝ (t : ℂ)) (Icc 1 3) := by
    intro t ht
    have htpos : 0 < (t : ℂ).re := by simp; linarith [ht.1]
    have ha := gammaReal_analyticAt_pos (t : ℂ) htpos
    exact ((ha.deriv.div ha (Complex.Gammaℝ_ne_zero_of_re_pos htpos)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro t ht ht'
  exact (hC t ⟨ht, ht'⟩).trans (by linarith [le_abs_self C])

theorem characterGamma_real_logDeriv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℝ), 1 < s → s ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) (s : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := gammaReal_logDeriv_real_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs'
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs.le (by linarith)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := (s : ℂ))
      (gammaReal_analyticAt_pos ((s : ℂ) + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by linarith) (by linarith)

end Ostmann

end OAI
