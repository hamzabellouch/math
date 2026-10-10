import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalMomentIntegrability

namespace OAI

/-! # A fixed positive set of angular pairs reaching the target velocity ball -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def accessAngles (κ ρ : ℝ) : Set (Sphere × Sphere) :=
  twoCollisionMap beamAxis ⁻¹' ball (κ • firstAxis) ρ ∩ firstAngleSet beamAxis

theorem accessAngles_measurable (κ ρ : ℝ) : MeasurableSet (accessAngles κ ρ) :=
  ((twoCollisionMap_measurable beamAxis) measurableSet_ball).inter
    (firstAngleSet_measurable beamAxis)

theorem accessAngles_positive : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧
    ∀ κ ρ : ℝ, 0 < κ → 0 < ρ → κ+ρ ≤ δ →
      0 < (sphereProbability.prod sphereProbability) (accessAngles κ ρ) := by
  obtain ⟨δ,B,hδ,hδsmall,_hB0,_hBt,hvolume⟩ := localTwoCollisionLaw_volume_domination
  refine ⟨δ,hδ,hδsmall,?_⟩
  intro κ ρ hκ hρ hκρ
  have hsub : ball (κ • firstAxis) ρ ⊆ ball (0 : V) δ := by
    intro v hv
    have ht := dist_triangle v (κ • firstAxis) 0
    simp only [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hκ,axis_norms.1,mul_one] at ht
    change dist v 0 < δ
    rw [dist_zero_right]
    have hv' : dist v (κ • firstAxis) < ρ := hv
    linarith
  have hv := hvolume beamAxis (mem_ball_self hδ) (ball (κ • firstAxis) ρ)
  rw [Measure.restrict_apply measurableSet_ball,inter_eq_left.mpr hsub,
    Measure.smul_apply,smul_eq_mul] at hv
  have hp : 0 < volume (ball (κ • firstAxis) ρ) := measure_ball_pos volume _ hρ
  have hl : 0 < localTwoCollisionLaw beamAxis (ball (κ • firstAxis) ρ) := by
    by_contra hz
    have hz' : localTwoCollisionLaw beamAxis (ball (κ • firstAxis) ρ) = 0 :=
      bot_unique (not_lt.mp hz)
    rw [hz',mul_zero] at hv
    exact (not_le_of_gt hp) hv
  simpa only [localTwoCollisionLaw,Measure.map_apply (twoCollisionMap_measurable beamAxis)
    measurableSet_ball,Measure.restrict_apply
      ((twoCollisionMap_measurable beamAxis) measurableSet_ball),accessAngles] using hl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
