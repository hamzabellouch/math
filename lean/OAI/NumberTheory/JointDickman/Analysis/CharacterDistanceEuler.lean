import OAI.NumberTheory.JointDickman.Arithmetic.DampedPrimeMass

namespace OAI

/-! # The Euler logarithm lower bound for character distance -/
namespace JointDickman
open Complex

/-- The error is absolute and independent of the modulus, character and
frequency. This bridge uses only Mertens' estimates and absolute Euler tails. -/
theorem characterDistance_ge_log_sub_L : ∃ C : ℝ,
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (X : ℝ), max 2 (Real.exp 1) ≤ X → ∀ t : ℝ,
      Real.log (Real.log X) -
        Real.log ‖χ.LFunction ((1+1/Real.log X:ℝ)+(t:ℂ)*I)‖ - C ≤
        PublishedInputs.primeDistanceSquared (characterArithmetic χ) X t := by
  obtain ⟨K,hK⟩ := dampedPrimeMass_log_bound
  obtain ⟨M,hM⟩ := primeCutoff_mass_lower
  let E : ℝ := 1+(Real.log 4+4)/Real.log 2
  refine ⟨2*M+2*E+K+primeEulerRemainderConstant,?_⟩
  intro q _ χ X hX t
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hs : 1 < 1+1/Real.log X := by linarith [one_div_pos.mpr hlog]
  have hdist := characterDistance_damped_lower χ X t hs
  have hmass := hM X hX2
  have hdamp := primeCutoff_log_scale_damping hX2
  have htotal := hK X hXe
  have hsC : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by simpa using hs
  have hlinear := (abs_le.mp (primeCharacterLinearSum_re_error χ hsC)).2
  dsimp [E]
  linarith

end JointDickman

end OAI
