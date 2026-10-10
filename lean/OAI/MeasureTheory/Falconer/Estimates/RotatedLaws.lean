import OAI.MeasureTheory.Falconer.Angular.SphereRotations
import OAI.MeasureTheory.Falconer.Slicing.TransverseFrame

namespace OAI

/-! # Rotation transport of the original point and direction laws -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

theorem sphereMap_distance (e : Space d ≃ₗᵢ[ℝ] Space d) (v w : Sphere d) :
    dist (sphereMap e v) (sphereMap e w) = dist v w := e.dist_map v w

theorem sphereMap_symm_apply (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e (sphereMap e.symm w) = w := by
  apply Subtype.ext
  exact e.apply_symm_apply w

theorem sphereMap_apply_symm (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e.symm (sphereMap e w) = w := by
  apply Subtype.ext
  exact e.symm_apply_apply w

theorem sphereMap_ball_preimage (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    sphereMap e ⁻¹' ball w r = ball (sphereMap e.symm w) r := by
  rw [← sphereMap_symm_apply e w]
  ext v
  simp only [mem_preimage,mem_ball,sphereMap_distance]
  rw [sphereMap_apply_symm e]

theorem rotated_point_ball (μ : Measure (Space d)) (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) (r : ℝ) :
    (Measure.map e μ) (ball x r) = μ (ball (e.symm x) r) := by
  rw [Measure.map_apply e.continuous.measurable measurableSet_ball]
  congr 1
  ext y
  change dist (e y) x < r ↔ dist y (e.symm x) < r
  rw [← e.apply_symm_apply x,e.dist_map,e.symm_apply_apply]

theorem rotated_direction_ball (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) (ball w r) = ν (ball (sphereMap e.symm w) r) := by
  rw [Measure.map_apply (continuous_sphereMap e).measurable measurableSet_ball,
    sphereMap_ball_preimage]

theorem rotated_direction_slab (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) {v : Sphere d | |inner ℝ (w:Space d) (v:Space d)| ≤ r} =
      ν {v : Sphere d | |inner ℝ (sphereMap e.symm w:Space d) (v:Space d)| ≤ r} := by
  have hm : MeasurableSet {v : Sphere d | |inner ℝ (w:Space d) (v:Space d)| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.map_apply (continuous_sphereMap e).measurable hm]
  congr 1
  ext v
  change |inner ℝ (w:Space d) (e (v:Space d))| ≤ r ↔ |inner ℝ (e.symm (w:Space d)) (v:Space d)| ≤ r
  rw [← e.inner_map_map (e.symm (w:Space d)) (v:Space d),e.apply_symm_apply]

theorem rotated_perpendicular_norm (e : Space d ≃ₗᵢ[ℝ] Space d) (w x a : Space d) :
    ‖perpendicularPart (e w) (e x-e a)‖ = ‖perpendicularPart w (x-a)‖ := by
  calc
    _ = ‖e (perpendicularPart w (x-a))‖ := by
      congr 1
      simp only [perpendicularPart,map_sub,map_smul,inner_sub_right,e.inner_map_map]
    _ = _ := e.norm_map _

theorem rotated_incidence (μ : Measure (Space d)) (ν : Measure (Sphere d))
    [SFinite μ] [SFinite ν] (e : Space d ≃ₗᵢ[ℝ] Space d)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    ((Measure.map e μ).prod (Measure.map (sphereMap e) ν))
      ((Prod.map e.symm (sphereMap e.symm)) ⁻¹' E) = (μ.prod ν) E := by
  have he := e.continuous.measurable
  have hw := (continuous_sphereMap e).measurable
  have hE' := hE.preimage (e.symm.continuous.measurable.prodMap
    (continuous_sphereMap e.symm).measurable)
  rw [Measure.map_prod_map μ ν he hw,Measure.map_apply (he.prodMap hw) hE']
  congr 1
  ext p
  change (e.symm (e p.1),sphereMap e.symm (sphereMap e p.2)) ∈ E ↔ p ∈ E
  rw [e.symm_apply_apply,sphereMap_apply_symm]

end Falconer

end OAI
