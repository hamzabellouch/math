import OAI.Geometry.NodalSets.Elliptic.CoordinateTransverseDisk

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
noncomputable section

lemma physical_sign_projection_covers (f : Coord → ℝ) (hf : Continuous f)
    (x : Coord) (j : Fin 4) {R tau r : ℝ} (hR : 0 < R) (ht : 0 ≤ tau) (hr : 0 ≤ r)
    (htr : tau+r ≤ 1)
    (hpos : ∀ y ∈ sourceClosedBall x (r*R), 0 < f y)
    (hneg : ∀ y ∈ sourceClosedBall (x+R • (tau • Pi.single j 1)) (r*R), f y < 0) :
    transverseDisk (r*R) ⊆ (fun y ↦ transverseProjection j (y-x)) ''
      (sourceClosedBall x R ∩ {y | f y = 0}) := by
  let a : Coord := R • (tau • Pi.single j 1)
  have hL (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      sourceEuclideanNorm (transverseInclusion j z) ≤ r*R := by
    rw [transverseInclusion_sourceNorm]
    exact hz
  have hn (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      f (x+(a+transverseInclusion j z)) < 0 := by
    apply hneg
    change sourceEuclideanNorm ((x+(a+transverseInclusion j z))-(x+a)) ≤ r*R
    simpa only [add_sub_add_left_eq_sub,add_sub_cancel_left] using hL z hz
  have hp (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      0 < f (x+(0+transverseInclusion j z)) := by
    apply hpos
    change sourceEuclideanNorm ((x+(0+transverseInclusion j z))-x) ≤ r*R
    simpa only [zero_add,add_sub_cancel_left] using hL z hz
  have hseg (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      ∀ t ∈ Icc (0:ℝ) 1, segmentPoint (a+transverseInclusion j z) (0+transverseInclusion j z) t ∈
        {v : Coord | sourceEuclideanNorm v ≤ R} := by
    intro t ht'
    have ha : sourceEuclideanNorm (a+transverseInclusion j z) ≤ R := by
      apply (sourceEuclideanNorm_add_le _ _).trans
      have hna : sourceEuclideanNorm a = R*tau := by
        dsimp [a]
        rw [smul_smul,sourceEuclideanNorm_single,abs_of_nonneg (mul_nonneg hR.le ht)]
      rw [hna]
      nlinarith [hL z hz]
    have hb : sourceEuclideanNorm (0+transverseInclusion j z) ≤ R := by
      rw [zero_add]
      apply (hL z hz).trans
      have hr1 : r ≤ 1 := le_trans (le_add_of_nonneg_left ht) htr
      simpa only [mul_one, mul_comm] using mul_le_mul (le_refl R) hr1 hr hR.le
    exact sourceEuclideanBall_convex R ha hb (by linarith [ht'.2] : 0 ≤ 1-t) ht'.1 (by ring)
  have hc := projection_covers (hf.comp (continuous_const.add continuous_id))
    (transverseProjection j) (transverseInclusion j) (transverseProjection_inclusion j)
    (show transverseProjection j a = 0 by dsimp [a]; rw [smul_smul]; exact transverseProjection_axis j _)
    (map_zero _) hn hp hseg
  intro z hz
  obtain ⟨v,⟨hv,hzero⟩,hproj⟩ := hc hz
  refine ⟨x+v,⟨?_,hzero⟩,?_⟩
  · change sourceEuclideanNorm (x+v-x) ≤ R
    simpa only [mem_ofPred_eq,add_sub_cancel_left] using hv
  · simpa only [add_sub_cancel_left] using hproj

lemma physical_nodal_disk_measure (f : Coord → ℝ) (hf : Continuous f)
    (x : Coord) (j : Fin 4) {R tau r : ℝ} (hR : 0 < R) (ht : 0 ≤ tau) (hr : 0 ≤ r)
    (htr : tau+r ≤ 1)
    (hpos : ∀ y ∈ sourceClosedBall x (r*R), 0 < f y)
    (hneg : ∀ y ∈ sourceClosedBall (x+R • (tau • Pi.single j 1)) (r*R), f y < 0) :
    Measure.hausdorffMeasure (3:ℝ) (transverseDisk (r*R)) ≤
      Measure.hausdorffMeasure (3:ℝ) (sourceClosedBall x R ∩ {y | f y = 0}) := by
  have hLip : LipschitzWith 1 (fun y ↦ transverseProjection j (y-x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [NNReal.coe_one,one_mul,dist_sub_right] using
      (transverseProjection_lipschitz j).dist_le_mul (y-x) (z-x)
  have hh := (measure_mono (physical_sign_projection_covers f hf x j hR ht hr htr hpos hneg)).trans
    (hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 3) _)
  simpa using hh

end
end Yau.Geometry

end OAI
