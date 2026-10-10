import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import OAI.Geometry.NodalSets.Charts.BallGeometry
import OAI.Geometry.NodalSets.Elliptic.FiniteBallPacking

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric MeasureTheory
noncomputable section

def sourceClosedBall (x : Coord) (r : ℝ) : Set Coord :=
  {y | sourceEuclideanNorm (y-x) ≤ r}

lemma sourceClosedBall_preimage (x : Coord) (r : ℝ) :
    sourceClosedBall x r = (WithLp.toLp 2) ⁻¹'
      closedBall (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4)) r := by
  ext y
  simp only [sourceClosedBall,mem_ofPred_eq,mem_preimage,mem_closedBall,dist_eq_norm,
    sourceEuclideanNorm_eq_norm]
  rfl

lemma sourceClosedBall_isCompact (x : Coord) (r : ℝ) : IsCompact (sourceClosedBall x r) := by
  rw [sourceClosedBall_preimage]
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).toHomeomorph.symm
  exact e.isCompact_preimage.mpr (isCompact_closedBall _ _)

lemma sourceClosedBall_volume (x : Coord) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (sourceClosedBall x r) = (Real.pi^2/2)*r^4 := by
  rw [Measure.real,sourceClosedBall_preimage,
    (PiLp.volume_preserving_toLp (Fin 4)).measure_preimage measurableSet_closedBall.nullMeasurableSet,
    InnerProductSpace.volume_closedBall_of_dim_even (k := 2) (by simp)]
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi^2/2 by positivity)]
  ring

lemma source_finite_fivefold_packing {Q : Set Coord} (hQ : IsCompact Q)
    (r : Coord → ℝ) (hr : ∀ x ∈ Q, 0 < r x) :
    ∃ t : Finset Coord, (↑t : Set Coord) ⊆ Q ∧
      (↑t : Set Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x) := by
  classical
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).toHomeomorph.symm
  obtain ⟨t,htQ,htdis,htcov⟩ := finite_fivefold_packing (hQ.image e.continuous)
    (fun x ↦ r (e.symm x)) (by rintro _ ⟨x,hx,rfl⟩; simpa using hr x hx)
  refine ⟨t.image e.symm,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,hzy⟩ := htQ hy
    simpa [← hzy] using hz
  · intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h ↦ hxy (congrArg e.symm h)
    have hd := htdis ha hb hab
    apply Disjoint.preimage e hd |>.mono
    · intro z hz
      change dist (e z) a ≤ r (e.symm a)
      change ‖e z-a‖ ≤ _
      dsimp only at hz
      rw [sourceClosedBall_preimage] at hz
      exact hz
    · intro z hz
      change dist (e z) b ≤ r (e.symm b)
      change ‖e z-b‖ ≤ _
      dsimp only at hz
      rw [sourceClosedBall_preimage] at hz
      exact hz
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (htcov (mem_image_of_mem e hx))
    refine mem_iUnion₂.mpr ⟨e.symm y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
    change sourceEuclideanNorm (x-e.symm y) ≤ _
    rw [sourceEuclideanNorm_eq_norm]
    exact hxy

end
end Yau.Geometry

end OAI
