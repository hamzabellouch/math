import OAI.Geometry.EinsteinFour.JacobiInverse
import Mathlib.Analysis.Calculus.DSlope

namespace OAI

/-! Removing the zero of the Jacobi matrix at its initial endpoint. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

def normalizedJacobi (J : ℝ → R) : ℝ → R := dslope J 0

theorem normalizedJacobi_zero {J : ℝ → R} (hJ : HasDerivAt J 1 0) :
    normalizedJacobi J 0 = 1 := by
  rw [normalizedJacobi, dslope_same, hJ.deriv]

theorem normalizedJacobi_pos {J : ℝ → R} (hJ0 : J 0 = 0) {s : ℝ} (hs : s ≠ 0) :
    normalizedJacobi J s = s⁻¹ • J s := by
  rw [normalizedJacobi, dslope_of_ne J hs, slope_def_module, hJ0, sub_zero, sub_zero]

theorem normalizedJacobi_continuousOn {J : ℝ → R} {t : ℝ}
    (hc : ContinuousOn J (Set.Icc 0 t)) (hJ : HasDerivAt J 1 0) :
    ContinuousOn (normalizedJacobi J) (Set.Icc 0 t) := by
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    exact (continuousAt_dslope_same.mpr hJ.differentiableAt).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne hs0).mpr (hc s hs)

/-- Preconjugacy gives invertibility of the normalized curve on the
closed interval, including its value one at the initial endpoint. -/
theorem normalizedJacobi_isUnit {J : ℝ → R} {t : ℝ}
    (hJ0 : J 0 = 0) (hJ : HasDerivAt J 1 0)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (J s)) :
    ∀ s ∈ Set.Icc 0 t, IsUnit (normalizedJacobi J s) := by
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    rw [normalizedJacobi_zero hJ]
    exact isUnit_one
  · rw [normalizedJacobi_pos hJ0 hs0, Algebra.smul_def]
    have hscalar : IsUnit (algebraMap ℝ R s⁻¹) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hs0)).map (algebraMap ℝ R)
    exact hscalar.mul (hpre s (lt_of_le_of_ne hs.1 (Ne.symm hs0)) hs.2)

variable [HasSummableGeomSeries R] [Nontrivial R]

/-- Uniform inverse control applies through zero without a lower
time cutoff. The actual Jacobi matrix itself vanishes at zero. -/
theorem normalizedJacobi_inverse_neighborhood {J : ℝ → R} {t : ℝ}
    (hc : ContinuousOn J (Set.Icc 0 t)) (hJ0 : J 0 = 0) (hJ : HasDerivAt J 1 0)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (J s)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Set.Icc 0 t, ∀ A : R,
      ‖A - normalizedJacobi J s‖ ≤ 1 / (2 * K) →
      IsUnit A ∧ ‖Ring.inverse A‖ ≤ 2 * K ∧
        ‖Ring.inverse A - Ring.inverse (normalizedJacobi J s)‖ ≤
          2 * K ^ 2 * ‖A - normalizedJacobi J s‖ :=
  uniform_inverse_neighborhood (normalizedJacobi_continuousOn hc hJ)
    (normalizedJacobi_isUnit hJ0 hJ hpre)

end

end PositiveEinsteinFour.Jacobi

end OAI
