import OAI.MeasureTheory.Falconer.Radial.RadialScaleIntersection

namespace OAI

/-! # The cap estimate at radii above one -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_cap_extension (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) {δ K ell : ℝ} (hK : 1 ≤ K) (hell : 0 ≤ ell)
    (hcap : ∀ x w : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤ ENNReal.ofReal (K*r^ell)) :
    ∀ x w : Space d, ∀ r : ℝ, δ ≤ r →
      μ {z | (x,z) ∈ G ∧ dist (normalize (z-x)) w < r} ≤ ENNReal.ofReal (K*r^ell) := by
  intro x w r hr
  by_cases hr1 : r ≤ 1
  · apply (measure_mono ?_).trans (hcap x w r hr hr1)
    intro z hz
    exact ⟨hz.1,by simpa only [dist_eq_norm] using hz.2.le⟩
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hp : 1 ≤ K*r^ell := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hr1' hell)
    exact (prob_le_one).trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)

end Falconer

end OAI
