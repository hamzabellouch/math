import OAI.Combinatorics.Crossing.CircleOffsetLine
import OAI.Combinatorics.Crossing.CircleConnectors

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem det2_rotateQuarter_self (d : Plane) : det2 d (rotateQuarter d)=squaredLength d := by
  dsimp [det2,rotateQuarter,squaredLength]
  ring

theorem normalShift_eq_circleTrackScale (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : normalShift d=circleTrackScale d w • rotateQuarter w := by
  let c := dot2 d w/squaredLength d
  have hp : w=c • d := vector_parallel_of_det_zero d w hd hpar
  have hc : c ≠ 0 := by
    intro h
    rw [h,zero_smul] at hp
    exact hw hp
  have hrot : rotateQuarter w=c • rotateQuarter d := by
    rw [hp]
    apply Prod.ext
    · dsimp [rotateQuarter]
      ring
    · rfl
  have hL := ne_of_gt (squaredLength_pos d hd)
  unfold normalShift circleTrackScale
  rw [hrot,det2_smul_right,det2_rotateQuarter_self,smul_smul]
  congr 1
  field_simp

theorem similarity_circleTangentOffset (o u v : Plane) (δ : ℝ) :
    similarityPoint o u (circleTangentOffset v δ)=
      similarityPoint o u v+δ • rotateQuarter (similarityPoint o u v-o) := by
  apply Prod.ext <;> dsimp [similarityPoint,circleTangentOffset,rotateQuarter] <;> ring

theorem tangentOffset_eq_normalShift (o u v d : Plane) (hd : d ≠ 0)
    (hw : similarityPoint o u v-o ≠ 0) (hpar : det2 d (similarityPoint o u v-o)=0)
    (ε : ℝ) :
    similarityPoint o u (circleTangentOffset v (circleTrackScale d (similarityPoint o u v-o)*ε))=
      similarityPoint o u v+ε • normalShift d := by
  rw [similarity_circleTangentOffset,normalShift_eq_circleTrackScale d _ hd hw hpar,smul_smul]
  congr 2
  ring

theorem similarityPoint_squaredLength (o u x : Plane) :
    squaredLength (similarityPoint o u x-o)=squaredLength u*squaredLength x := by
  dsimp [similarityPoint,squaredLength]
  ring

theorem physical_circleConnector_strictly_outside (o u v : Plane) (hu : u ≠ 0)
    (hv : squaredLength v=1) (δ : ℝ) (hδ : |δ|<1) (hne : δ ≠ 0)
    (t : ℝ) (ht : 0<t) :
    squaredLength u < squaredLength
      (segmentPoint (similarityPoint o u (circleOffset v δ))
        (similarityPoint o u (circleTangentOffset v δ)) t-o) := by
  rw [← similarityPoint_segment,similarityPoint_squaredLength]
  have hh := circleConnector_strictly_outside v hv δ hδ hne t ht
  nlinarith [squaredLength_pos u hu]

end Zarankiewicz

end

end OAI
