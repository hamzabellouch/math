import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaRealBound
import OAI.NumberTheory.Ostmann.ZeroDensity.VonMangoldtPole

namespace OAI

/-! # Uniform Gamma and zeta-pole errors in the low-height rectangle -/

namespace Ostmann

open Complex Set

 theorem gammaReal_logDeriv_rectangle_bound : ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 3 → |z.im| ≤ 2 →
      ‖logDeriv Complex.Gammaℝ z‖ ≤ C := by
  let K : Set ℂ := Icc (1 : ℝ) 3 ×ℂ Icc (-2 : ℝ) 2
  have hc : ContinuousOn (logDeriv Complex.Gammaℝ) K := by
    intro z hz
    have hzpos : 0 < z.re := by have := hz.1.1; linarith
    have ha := gammaReal_analyticAt_pos z hzpos
    exact (ha.deriv.div ha (Complex.Gammaℝ_ne_zero_of_re_pos hzpos)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro z hz hz' hi
  exact (hC z ⟨⟨hz, hz'⟩, abs_le.mp hi⟩).trans (by linarith [le_abs_self C])

theorem characterGamma_low_height_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := gammaReal_logDeriv_rectangle_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs' hi
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs.le (by linarith) hi
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_analyticAt_pos (s + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by simp; linarith) (by simp; linarith) (by simpa using hi)

/-- The pole remainder is uniformly bounded even when the evaluation point
approaches one through the complex low-height rectangle. -/
theorem vonMangoldt_low_height_pole_error : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s - (s - 1)⁻¹‖ ≤ C := by
  let F := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (0 : ZMod 1)
  let K : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Icc (-2 : ℝ) 2
  have hc : ContinuousOn F K :=
    (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (0 : ZMod 1)).mono
      (fun _ hs => hs.1.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro s hs hs' hi
  have hunit : IsUnit (0 : ZMod 1) := by
    rw [Subsingleton.elim (0 : ZMod 1) 1]
    exact isUnit_one
  have he := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux hunit hs
  rw [residue_one_eq_vonMangoldt] at he
  simp only [Nat.totient_one, Nat.cast_one, inv_one, one_div] at he
  change F s = _ at he
  rw [← he]
  exact (hC s ⟨⟨hs.le, hs'⟩, abs_le.mp hi⟩).trans (by linarith [le_abs_self C])

end Ostmann

end OAI
