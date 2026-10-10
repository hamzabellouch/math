import OAI.Combinatorics.Crossing.RadialExterior
import OAI.Combinatorics.Crossing.ChordTransversality

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem round_circle_line_two_points (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b)
    (hd : det2 (b-a) (c-a)=0) : c=a ∨ c=b := by
  have hlen := squaredLength_pos (b-a) (sub_ne_zero.mpr (Ne.symm hab))
  let t := dot2 (b-a) (c-a)/squaredLength (b-a)
  have hp : c-a=t • (b-a) := vector_parallel_of_det_zero (b-a) (c-a)
    (sub_ne_zero.mpr (Ne.symm hab)) hd
  have hba : (a-z)+(b-a)=b-z := by abel
  have hca : c-z=(a-z)+t • (b-a) := by rw [← hp]; abel
  have h₁ := squaredLength_add_smul (a-z) (b-a) 1
  simp only [one_smul,hba,ha,hb,one_pow,one_mul] at h₁
  rw [hca,squaredLength_add_smul,ha] at hc
  have hh : t*(t-1)*squaredLength (b-a)=0 := by linear_combination hc+t*h₁
  have ht := (mul_eq_zero.mp hh).resolve_right (ne_of_gt hlen)
  rcases mul_eq_zero.mp ht with ht | ht
  · left
    rw [ht,zero_smul] at hp
    exact sub_eq_zero.mp hp
  · right
    have ht1 : t=1 := sub_eq_zero.mp ht
    rw [ht1,one_smul] at hp
    exact sub_left_injective hp

theorem round_circle_orient_ne_zero (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient2 a b c ≠ 0 := by
  intro hd
  exact (round_circle_line_two_points z a b c r ha hb hc hab hd).elim
    (fun h => hac h.symm) (fun h => hbc h.symm)

theorem round_circle_chords_transverse (z a b c d : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hd : squaredLength (d-z)=r^2)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    SegmentPairTransverse a b c d := by
  exact segmentPairTransverse_of_noncollinear_endpoints a b c d
    (round_circle_orient_ne_zero z c d a r hc hd ha hcd hac.symm had.symm)
    (round_circle_orient_ne_zero z c d b r hc hd hb hcd hbc.symm hbd.symm)
    (round_circle_orient_ne_zero z a b c r ha hb hc hab hac hbc)
    (round_circle_orient_ne_zero z a b d r ha hb hd hab had hbd)

theorem round_chord_in_open_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hab : a ≠ b) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) < r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hp := mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2))
    (squaredLength_pos (b-a) (sub_ne_zero.mpr hab.symm))
  rw [he,ha,hb]
  linarith

end Zarankiewicz

end

end OAI
