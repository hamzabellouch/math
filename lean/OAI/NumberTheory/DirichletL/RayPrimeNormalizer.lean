import OAI.NumberTheory.DirichletL.Hecke.RayPrimes
import OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology ContDiff
namespace SevenEighths.RayPrimeNormalizer
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def normalizer (S : Finset (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted (RayQuotient.identityClass M H) S W x

include hH

theorem asymptotic (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1/6 : ℝ) * normalizer M H S W x)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹ * ∫ y : ℝ, W y * y ^ (-5/6 : ℝ))) :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted_tendsto _ S
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp

theorem eventually_lower_bound (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1/6 : ℝ) / Real.log x ≤ normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_lower_bound _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

theorem eventually_pos (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_pos _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

end SevenEighths.RayPrimeNormalizer

end

end OAI
