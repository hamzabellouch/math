import OAI.Geometry.NodalSets.Elliptic.TransverseCylinderVolume
import OAI.Geometry.NodalSets.Hausdorff.PhysicalNodalDisk

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def cylinderProjection (x : Coord) (j : Fin 4) (y : Coord × ℝ) : Coord :=
  Fin.cons y.2 (transverseProjection j (y.1-x))

lemma cylinderProjection_lipschitz (x : Coord) (j : Fin 4) :
    LipschitzWith 1 (cylinderProjection x j) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · change ‖y.2-z.2‖ ≤ dist y z
    rw [Prod.dist_eq]
    exact le_max_right _ _
  · have hh := (norm_le_pi_norm (y.1-z.1) (j.succAbove k)).trans
      (show ‖y.1-z.1‖ ≤ dist y z from by rw [Prod.dist_eq]; exact le_max_left _ _)
    simpa [cylinderProjection,transverseProjection,sub_sub_sub_cancel_right] using hh

lemma physical_sign_cylinder_covers (f : Coord → ℝ) (hf : Continuous f)
    (x : Coord) (j : Fin 4) {R tau r : ℝ} (hR : 0 < R) (ht : 0 ≤ tau) (hr : 0 ≤ r)
    (htr : tau+r ≤ 1)
    (hpos : ∀ y ∈ sourceClosedBall x (r*R), 0 < f y)
    (hneg : ∀ y ∈ sourceClosedBall (x+R • (tau • Pi.single j 1)) (r*R), f y < 0) :
    transverseCylinder (r*R) ⊆ cylinderProjection x j ''
      ((sourceClosedBall x R ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) := by
  intro z hz
  obtain ⟨y,⟨hy,hzero⟩,hproj⟩ := physical_sign_projection_covers f hf x j hR ht hr htr hpos hneg hz.2
  refine ⟨(y,z 0),⟨⟨hy,hz.1⟩,hzero⟩,?_⟩
  change Fin.cons (z 0) (transverseProjection j (y-x)) = z
  dsimp only at hproj
  rw [hproj,Fin.cons_self_tail]

lemma physical_nodal_cylinder_measure (f : Coord → ℝ) (hf : Continuous f)
    (x : Coord) (j : Fin 4) {R tau r : ℝ} (hR : 0 < R) (ht : 0 ≤ tau) (hr : 0 ≤ r)
    (htr : tau+r ≤ 1)
    (hpos : ∀ y ∈ sourceClosedBall x (r*R), 0 < f y)
    (hneg : ∀ y ∈ sourceClosedBall (x+R • (tau • Pi.single j 1)) (r*R), f y < 0) :
    ENNReal.ofReal (2*r^3*R^3) ≤ Measure.hausdorffMeasure (4:ℝ)
      ((sourceClosedBall x R ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) := by
  have hh := (transverseCylinder_measure_lower (mul_nonneg hr hR.le)).trans
    ((measure_mono (physical_sign_cylinder_covers f hf x j hR ht hr htr hpos hneg)).trans
      ((cylinderProjection_lipschitz x j).hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 4) _))
  simpa only [mul_pow,mul_assoc,ENNReal.coe_one,ENNReal.one_rpow,one_mul] using hh

end
end Yau.Geometry

end OAI
