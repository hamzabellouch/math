import OAI.Analysis.CircleDomains.Uniformization.ScalarModelCoefficients
import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan
import OAI.Analysis.CircleDomains.Sobolev.TargetArea

namespace OAI

/-! Properness of the actual inverse projection bounds images of bounded
source sets. Complex change of variables then gives their finite energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem projection_bounded_lifts (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {S : Set ℂ} (hS : IsCompact S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Sphere,
      M.projection p ∈ ((↑) : ℂ → Sphere) '' S → ‖finiteCoord p‖ ≤ K := by
  let C := M.projection ⁻¹' (((↑) : ℂ → Sphere) '' S)
  have hC : IsCompact C :=
    ((hS.image OnePoint.continuous_coe).isClosed.preimage M.projection_continuous).isCompact
  have hno : OnePoint.infty ∉ C := by
    have hi : M.projection OnePoint.infty = OnePoint.infty := by
      simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
    rintro ⟨z, _, hz⟩
    exact OnePoint.coe_ne_infty z (hz.trans hi)
  obtain ⟨K, hK⟩ := (hC.image_of_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty hno)).isBounded.exists_norm_le
  exact ⟨max K 0, le_max_right _ _, fun p hp => (hK _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)⟩

 theorem function_bounded_on_source_ball (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, (z : Sphere) ∈ G → z ∈ ball 0 R → ‖M.function z‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := M.projection_bounded_lifts hinf (isCompact_closedBall (0 : ℂ) R)
  refine ⟨K, hK, fun z hzG hz => ?_⟩
  have hp : M.projection ((M.function z : ℂ) : Sphere) ∈
      ((↑) : ℂ → Sphere) '' closedBall 0 R := by
    have hi := M.projection_inverse (z : Sphere) hzG
    simp only [extendAtInfinity_coe] at hi
    rw [hi]
    exact ⟨z, ball_subset_closedBall hz, rfl⟩
  simpa only [finiteCoord_coe] using hb (M.function z : Sphere) hp

 theorem derivative_energy_on_source_ball (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    Integrable (fun z => ‖deriv M.function z‖^2)
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  let U : Set ℂ := {z | (z : Sphere) ∈ G} ∩ ball 0 R
  have hU : IsOpen U := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  obtain ⟨K, _, hK⟩ := M.function_bounded_on_source_ball hinf R
  have hsub : M.function '' U ⊆ closedBall 0 K := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using hK z hz.1 hz.2
  apply integrable_norm_deriv_sq_of_image_area_finite hU.measurableSet
    (fun z hz => finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1))
    (fun z hz w hw he => ?_)
    (((isBounded_closedBall (x := (0 : ℂ)) (r := K)).subset hsub).measure_lt_top.ne)
  apply OnePoint.coe_injective
  apply M.conformal.bijOn.injOn hz.1 hw.1
  simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
