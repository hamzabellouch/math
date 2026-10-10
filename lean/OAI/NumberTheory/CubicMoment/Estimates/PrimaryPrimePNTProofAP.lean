import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofTheta
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofLogCount

namespace OAI

/-! The natural prime density of the split rational residue class.

The von Mangoldt input is derived from the Wiener--Ikehara theorem and Mathlib's residue-class continuation. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

/-- The class `1 mod 3` has natural prime density one half. -/
theorem rationalProgressionCount_one_limit :
    Tendsto (fun X => rationalProgressionCount 1 X * Real.log X / X)
      atTop (𝓝 (1/2)) := by
  have heq (X : ℝ) : selectedRationalPrimes (fun p => p % 3 = 1) X =
      rationalProgressionPrimes 1 X := by
    ext p
    simp only [selectedRationalPrimes, rationalProgressionPrimes, Finset.mem_filter]
  have htheta : Tendsto (fun X => selectedRationalTheta (fun p => p % 3 = 1) X / X)
      atTop (𝓝 (1/2 : ℝ)) := by
    simpa only [selectedRationalTheta, heq, rationalProgressionTheta] using
      (rationalProgressionTheta_limit (a := 1) (Or.inl rfl))
  have h := selectedRationalCount_limit (fun p => p % 3 = 1)
    (by norm_num : (0 : ℝ) < 1/2)
    htheta
  simpa only [selectedRationalCount, heq, rationalProgressionCount] using h

end CubicFirstMoment

end

end OAI
