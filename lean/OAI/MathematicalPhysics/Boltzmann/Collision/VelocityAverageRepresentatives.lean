import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityAverageDifference
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1

namespace OAI

/-! # Almost-everywhere representatives do not change the velocity average -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem velocityLineAverage_congr_ae {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) (he : r =ᵐ[volume] q) :
    velocityLineAverage r =ᵐ[volume] velocityLineAverage q := by
  have hz : eLpNorm (r-q) 1 volume = 0 := by
    have hzero : r-q =ᵐ[volume] 0 := by
      filter_upwards [he] with p hp
      simp only [Pi.sub_apply,Pi.zero_apply,hp,sub_self]
    rw [eLpNorm_congr_ae hzero,eLpNorm_zero]
  have hb := velocityLineAverage_difference_le hr hq
  rw [hz] at hb
  have ha := (eLpNorm_eq_zero_iff (by norm_num : (1 : ℝ≥0∞) ≠ 0)).mp
    (le_antisymm hb bot_le)
  filter_upwards [ha] with x hx
  exact sub_eq_zero.mp hx

theorem measurable_velocity_representative (r : ℕ → KineticPhase → ℝ)
    (hui : UniformIntegrable r 1 volume) (R : ℝ)
    (hs : ∀ n, ∀ᵐ z ∂volume, R < ‖z.2‖ → r n z = 0) :
    ∃ u : ℕ → KineticPhase → ℝ, (∀ n, Measurable (u n)) ∧
      (∀ n, u n =ᵐ[volume] r n) ∧
      (∀ n z, R < ‖z.2‖ → u n z = 0) := by
  let u n := {z : KineticPhase | ‖z.2‖ ≤ R}.indicator ((hui.aestronglyMeasurable n).mk (r n))
  have hS : MeasurableSet {z : KineticPhase | ‖z.2‖ ≤ R} := by measurability
  refine ⟨u,fun n => (hui.aestronglyMeasurable n).stronglyMeasurable_mk.measurable.indicator hS,?_,?_⟩
  · intro n
    filter_upwards [(hui.aestronglyMeasurable n).ae_eq_mk,hs n] with z hz hs'
    by_cases h : ‖z.2‖ ≤ R
    · simpa [u,h] using hz.symm
    · rw [show u n z = 0 by simp [u,h]]
      exact (hs' (lt_of_not_ge h)).symm
  · intro n z hz
    simp [u,not_le.mpr hz]

end BoltzmannNonuniqueness.Published

end

end OAI
