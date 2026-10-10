import OAI.Combinatorics.Crossing.TangentTrackIdentity
import OAI.Combinatorics.Crossing.RadialExterior

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem dot2_rotateQuarter_self (d : Plane) : dot2 (rotateQuarter d) d=0 := by
  dsimp [dot2,rotateQuarter]
  ring

theorem squaredLength_normal_offset (w d : Plane) (hd : d ≠ 0) (hpar : det2 d w=0) (ε : ℝ) :
    squaredLength (w+ε • normalShift d)=squaredLength w+ε^2/squaredLength d := by
  have hL := ne_of_gt (squaredLength_pos d hd)
  have hcross : dot2 w (rotateQuarter d)=0 := by
    dsimp [dot2,rotateQuarter,det2] at *
    linarith
  have hrot : squaredLength (rotateQuarter d)=squaredLength d := by
    dsimp [squaredLength,rotateQuarter]
    ring
  unfold normalShift
  rw [smul_smul,squaredLength_add_smul,hrot,hcross]
  field_simp
  ring

theorem normal_offset_radial_exterior (o p d : Plane) (r ε ℓ : ℝ)
    (hd : d ≠ 0) (hp : squaredLength (p-o)=r^2)
    (hpar : det2 d (p-o)=0) (hout : 0 ≤ dot2 (p-o) d) (hε : ε ≠ 0) (hℓ : 0 ≤ ℓ) :
    segment ℝ (p+ε • normalShift d) (p+ε • normalShift d+ℓ • d) ⊆
      {x | r^2 < squaredLength (x-o)} := by
  apply exterior_segment_of_dot
  · have he : p+ε • normalShift d-o=(p-o)+ε • normalShift d := by abel
    rw [he,squaredLength_normal_offset _ d hd hpar,hp]
    exact lt_add_of_pos_right _ (div_pos (sq_pos_of_ne_zero hε) (squaredLength_pos d hd))
  · have he : dot2 (p+ε • normalShift d-o) ((p+ε • normalShift d+ℓ • d)-(p+ε • normalShift d))=
        ℓ*dot2 (p-o) d := by
      dsimp [dot2,normalShift,rotateQuarter]
      ring
    rw [he]
    exact mul_nonneg hℓ hout

theorem normal_offset_segment_exterior (o p d q : Plane) (r ε ℓ : ℝ)
    (hd : d ≠ 0) (hp : squaredLength (p-o)=r^2)
    (hpar : det2 d (p-o)=0) (hout : 0 ≤ ℓ*dot2 (p-o) d) (hε : ε ≠ 0)
    (hq : q-(p+ε • normalShift d)=ℓ • d) :
    segment ℝ (p+ε • normalShift d) q ⊆ {x | r^2 < squaredLength (x-o)} := by
  apply exterior_segment_of_dot
  · have he : p+ε • normalShift d-o=(p-o)+ε • normalShift d := by abel
    rw [he,squaredLength_normal_offset _ d hd hpar,hp]
    exact lt_add_of_pos_right _ (div_pos (sq_pos_of_ne_zero hε) (squaredLength_pos d hd))
  · rw [hq]
    have he : dot2 (p+ε • normalShift d-o) (ℓ • d)=ℓ*dot2 (p-o) d := by
      dsimp [dot2,normalShift,rotateQuarter]
      ring
    rwa [he]

end Zarankiewicz

end

end OAI
