import OAI.Combinatorics.Crossing.OffsetVectors
import OAI.Combinatorics.Crossing.SegmentSides

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem offset_segment_parameterization (a b qa qb : Plane) (ε t : ℝ) :
    segmentPoint (a+ε • qa) (b+ε • qb) t =
      segmentPoint a b t+ε • segmentPoint qa qb t := by
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

theorem offset_segment_side (a b qa qb : Plane) (ε t : ℝ)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    orient2 a b (segmentPoint (a+ε • qa) (b+ε • qb) t) = ε := by
  dsimp [orient2,det2,segmentPoint] at *
  linear_combination ε*(1-t)*ha+ε*t*hb

theorem offset_segment_no_contact (a b qa qb : Plane) (ε : ℝ) (hε : ε ≠ 0)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) (s t : ℝ) :
    segmentPoint a b s ≠ segmentPoint (a+ε • qa) (b+ε • qb) t := by
  intro he
  have hh := congrArg (orient2 a b) he
  rw [orient2_self_segment,offset_segment_side a b qa qb ε t ha hb] at hh
  exact hε hh.symm

theorem offset_bend_no_contact (u v q : Plane) (ε : ℝ) (hε : ε ≠ 0)
    (hu : det2 u q=ε) (hv : det2 v q=ε)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    q+α • v+β • u ≠ 0 := by
  intro he
  have h₁ := congrArg (det2 u) he
  have h₂ := congrArg (det2 v) he
  simp only [det2_add_right,det2_smul_right,det2_self,det2_zero_right,hu,hv,
    mul_zero,add_zero] at h₁ h₂
  rw [det2_swap u v] at h₂
  have hprod : (α+β)*det2 u v=0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hz | hz
  · have hα0 : α=0 := by linarith
    rw [hα0,zero_mul,add_zero] at h₁
    exact hε h₁
  · rw [hz,mul_zero,add_zero] at h₁
    exact hε h₁

end Zarankiewicz

end

end OAI
