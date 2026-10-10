import OAI.Geometry.NodalSets.Charts.SphereChartOpenMap
import OAI.Geometry.NodalSets.Charts.SphereSimplicityEnergy
import OAI.Geometry.NodalSets.Elliptic.SimplicityLocalRigidity

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance sphereSimplicityRigidityLocal1 : MeasurableSpace Base := borel Base
local instance sphereSimplicityRigidityLocal2 : BorelSpace Base := ⟨rfl⟩

variable (u v a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)

include hu hv hz hc hzn hlam ha hb

lemma sphere_simplicity_energy_nonneg : 0 ≤ sphereEnergyForm a b lam v v := by
  rw [sphere_simplicity_energy_eq_coordinate u v a b hv zeta lam ha hb]
  exact round_simplicity_energy_nonneg _ _ zeta (spherePullback_smooth u hu seedPoint)
    (spherePullback_smooth v hv seedPoint) hz hc hzn lam hlam

theorem sphere_simplicity_zero_energy_differential
    (he : sphereEnergyForm a b lam v v = 0) :
    ∀ x, 0 < zeta x → sphereCrossDifferential u v (seedSphereFromCoord x) = 0 := by
  have he' := (sphere_simplicity_energy_eq_coordinate u v a b hv zeta lam ha hb).symm.trans he
  have hj := round_simplicity_zero_energy_jet _ _ zeta (spherePullback_smooth u hu seedPoint)
    (spherePullback_smooth v hv seedPoint) hz hc hzn lam hlam he'
  change ∀ x, 0 < zeta x → ∀ i,
    (u ∘ seedSphereFromCoord) x*Yau.coordPartial (v ∘ seedSphereFromCoord) x i =
    (v ∘ seedSphereFromCoord) x*Yau.coordPartial (u ∘ seedSphereFromCoord) x i at hj
  intro x hx
  have hs : roundSimplicitySquare (u ∘ seedSphereFromCoord) (v ∘ seedSphereFromCoord) x = 0 := by
    unfold roundSimplicitySquare
    simp only [hj x hx,sub_self]
    norm_num
  have hid : roundCotangentTensor (seedSphereFromCoord x)
      (sphereCrossDifferential u v (seedSphereFromCoord x))
      (sphereCrossDifferential u v (seedSphereFromCoord x)) = 0 :=
    (sphereCrossDifferential_square_chart u v hu hv seedPoint x).trans hs
  by_contra hn
  exact (roundCotangentTensor_pos _ _ hn).ne' hid

theorem sphere_simplicity_local_ball
    (he : sphereEnergyForm a b lam v v = 0) (x : Yau.Jets.Coord)
    (hxz : 0 < zeta x) (hxu : u (seedSphereFromCoord x) ≠ 0) :
    ∃ (c : ℝ) (U : Set Base), IsOpen U ∧ seedSphereFromCoord x ∈ U ∧
      ∀ p ∈ U, v p = c*u p := by
  have hu' : ContDiff ℝ ∞ (u ∘ seedSphereFromCoord) := spherePullback_smooth u hu seedPoint
  have hv' : ContDiff ℝ ∞ (v ∘ seedSphereFromCoord) := spherePullback_smooth v hv seedPoint
  let W : Set Yau.Jets.Coord := {y | 0 < zeta y ∧ u (seedSphereFromCoord y) ≠ 0}
  have hWo : IsOpen W := (isOpen_lt continuous_const hz.continuous).inter
    (isOpen_ne_fun hu'.continuous continuous_const)
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hWo x ⟨hxz,hxu⟩
  have he' := (sphere_simplicity_energy_eq_coordinate u v a b hv zeta lam ha hb).symm.trans he
  obtain ⟨c,hc⟩ := round_simplicity_local_rigidity _ _ zeta hu' hv' hz hc hzn lam hlam he'
    isOpen_ball (convex_ball x r).isPreconnected
    (fun y hy ↦ (hrW hy).1) (fun y hy ↦ (hrW hy).2)
  refine ⟨c,seedSphereFromCoord '' ball x r,?_,⟨x,mem_ball_self hr,rfl⟩,?_⟩
  · exact sphereChartCoordMap_isOpenMap seedPoint _ isOpen_ball
  · rintro p ⟨y,hy,rfl⟩
    exact hc y hy

end
end Yau.Target

end OAI
