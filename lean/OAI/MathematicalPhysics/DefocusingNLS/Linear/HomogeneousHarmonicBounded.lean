import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicWeakLaplacian
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMap

namespace OAI

/-! # Uniformly bounded radial channels from the actual C₀ realization

A smooth angular test is bounded on the unit sphere. Thus the radial
channel of a C₀ physical function is uniformly bounded at every radius.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem harmonicAngularCoefficient_bounded (Y : E → ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) (F : C₀(E, ℂ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, ‖harmonicAngularCoefficient Y F r‖ ≤ M := by
  have hYs : Continuous (fun z : PhysicalUnitSphere => Y z.1) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hn : ‖z.1‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2
    have hz : z.1 ≠ 0 := by
      intro h
      simp [h] at hn
    exact ((hY z.1 hz).continuousAt).comp continuous_subtype_val.continuousAt
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hYs.continuousOn
  refine ⟨(max K 0 * ‖F‖) * physicalSphereMeasure.real univ, by positivity, ?_⟩
  intro r
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with z
  rw [norm_mul]
  exact mul_le_mul ((hK z (mem_univ _)).trans (le_max_left K 0))
    ((BoundedContinuousFunction.norm_coe_le_norm F.toBCF _).trans_eq ZeroAtInftyContinuousMap.norm_toBCF_eq_norm)
    (norm_nonneg _) (le_max_right K 0)

theorem homogeneous_harmonic_channel_bounded (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k)
    (Y : E → ℂ) (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ,
      ‖harmonicAngularCoefficient Y (homogeneousPhysicalCLM a k ha ha1 hk u) r‖ ≤ M :=
  harmonicAngularCoefficient_bounded Y hY (homogeneousPhysicalCLM a k ha ha1 hk u)

end DefocusingNLS

end OAI
