import OAI.Combinatorics.Crossing.PhysicalCircleAveraging

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem similarity_circleOffset (o u v : Plane) (δ : ℝ) :
    similarityPoint o u (circleOffset v δ)-o =
      Real.sqrt (1-δ^2) • (similarityPoint o u v-o) +
        δ • rotateQuarter (similarityPoint o u v-o) := by
  apply Prod.ext <;> dsimp [similarityPoint,circleOffset,rotateQuarter] <;> ring

theorem rotated_parallel_det_ne_zero (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : det2 d (rotateQuarter w) ≠ 0 := by
  have hp := vector_parallel_of_det_zero d w hd hpar
  have hc : dot2 d w/squaredLength d ≠ 0 := by
    intro h
    rw [h,zero_smul] at hp
    exact hw hp
  have he : det2 d (rotateQuarter w)=(dot2 d w/squaredLength d)*squaredLength d := by
    conv_lhs => rw [hp]
    dsimp [det2,rotateQuarter,squaredLength]
    ring
  rw [he]
  exact mul_ne_zero hc (ne_of_gt (squaredLength_pos d hd))

def circleTrackScale (d w : Plane) : ℝ := (det2 d (rotateQuarter w))⁻¹

theorem circleTrackScale_ne_zero (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : circleTrackScale d w ≠ 0 :=
  inv_ne_zero (rotated_parallel_det_ne_zero d w hd hw hpar)

theorem circleOffset_track_level (o u v d : Plane) (hd : d ≠ 0)
    (hw : similarityPoint o u v-o ≠ 0)
    (hpar : det2 d (similarityPoint o u v-o)=0) (ε : ℝ) :
    det2 d (similarityPoint o u (circleOffset v (circleTrackScale d (similarityPoint o u v-o)*ε))-
      similarityPoint o u v)=ε := by
  let w := similarityPoint o u v-o
  let δ := circleTrackScale d w*ε
  have he : similarityPoint o u (circleOffset v δ)-similarityPoint o u v =
      (Real.sqrt (1-δ^2)-1) • w+δ • rotateQuarter w := by
    have hh := similarity_circleOffset o u v δ
    calc
      _ = (similarityPoint o u (circleOffset v δ)-o)-(similarityPoint o u v-o) := by abel
      _ = Real.sqrt (1-δ^2) • w+δ • rotateQuarter w-w := by rw [hh]
      _ = _ := by rw [sub_smul,one_smul]; abel
  change det2 d (similarityPoint o u (circleOffset v δ)-similarityPoint o u v)=ε
  rw [he,det2_add_right,det2_smul_right,det2_smul_right,hpar,mul_zero,zero_add]
  have hn := rotated_parallel_det_ne_zero d w hd hw hpar
  dsimp [δ,circleTrackScale]
  field_simp

end Zarankiewicz

end

end OAI
