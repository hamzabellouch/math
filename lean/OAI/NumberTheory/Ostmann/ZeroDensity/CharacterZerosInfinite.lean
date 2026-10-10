import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedFiniteBound
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedDivergence

namespace OAI

/-! # Infinitely many actual nontrivial zeros for every primitive character -/

namespace Ostmann

open Complex Filter Set
open scoped Topology

/-- A finite zero set would force bounded logarithmic derivative, contradicting
its Gamma-factor growth along the positive real axis. -/
theorem PrimitiveComplexCharacter.zeros_infinite (χ : PrimitiveComplexCharacter) :
    (complexCharacterZeros χ).Infinite := by
  intro hfinite
  obtain ⟨R, C, hR, hC, hbound⟩ := completed_logDeriv_bounded_of_finite_zeros χ hfinite
  have hg := (completed_logDeriv_sample_re_tendsto χ).eventually_ge_atTop (C + 1)
  have hr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (max R 2)
  obtain ⟨n, hn, hnR⟩ := (hg.and hr).exists
  have hsample := characterGammaSample_re_lower χ n
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnr : R ≤ (n : ℝ) := (le_max_left R 2).trans hnR
  have hb := hbound (characterGammaSample χ n) (by linarith)
  have hre := (le_abs_self ((logDeriv χ.completed (characterGammaSample χ n)).re)).trans
    (abs_re_le_norm (logDeriv χ.completed (characterGammaSample χ n)))
  linarith

end Ostmann

end OAI
