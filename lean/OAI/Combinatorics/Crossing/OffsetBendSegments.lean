import OAI.Combinatorics.Crossing.OffsetSegments
import OAI.Combinatorics.Crossing.SegmentAffineForms
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem offset_bend_no_reverse_contact (u v q : Plane) (ε : ℝ) (hε : ε ≠ 0)
    (hu : det2 u q=ε) (hv : det2 v q=ε)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) : q-α • u-β • v ≠ 0 := by
  intro he
  have h₁ := congrArg (det2 u) he
  have h₂ := congrArg (det2 v) he
  simp only [det2_sub_right,det2_smul_right,det2_self,det2_zero_right,hu,hv,
    mul_zero,sub_zero] at h₁ h₂
  rw [det2_swap u v] at h₂
  have hprod : (α+β)*det2 u v=0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hz | hz
  · have hα0 : α=0 := by linarith
    rw [hα0,zero_mul,sub_zero] at h₂
    exact hε h₂
  · rw [hz,mul_zero,sub_zero] at h₁
    exact hε h₁

theorem incoming_shifted_outgoing_disjoint (a b c qb qc : Plane) (ε r : ℝ)
    (hε : ε ≠ 0) (hr : 0 < r)
    (hu : det2 (b-a) qb=1) (hv : det2 (c-b) qb=1)
    (hdir : (c+ε • qc)-(b+ε • qb)=r • (c-b))
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segmentPoint a b s ≠ segmentPoint (b+ε • qb) (c+ε • qc) t := by
  intro he
  rw [segmentPoint_end_form a b s,segmentPoint_start_form,hdir,smul_smul] at he
  have hno := offset_bend_no_contact (b-a) (c-b) (ε • qb) ε hε
    (by rw [det2_smul_right,hu,mul_one]) (by rw [det2_smul_right,hv,mul_one])
    (t*r) (1-s) (mul_nonneg ht.1 hr.le) (by linarith [hs.2])
  apply hno
  calc
    ε • qb+(t*r) • (c-b)+(1-s) • (b-a) =
        ((b+ε • qb)+(t*r) • (c-b))-(b-(1-s) • (b-a)) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

theorem outgoing_shifted_incoming_disjoint (a b c qa qb : Plane) (ε r : ℝ)
    (hε : ε ≠ 0) (hr : 0 < r)
    (hu : det2 (b-a) qb=1) (hv : det2 (c-b) qb=1)
    (hdir : (b+ε • qb)-(a+ε • qa)=r • (b-a))
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segmentPoint b c s ≠ segmentPoint (a+ε • qa) (b+ε • qb) t := by
  intro he
  rw [segmentPoint_start_form b c s,segmentPoint_end_form,hdir,smul_smul] at he
  have hno := offset_bend_no_reverse_contact (b-a) (c-b) (ε • qb) ε hε
    (by rw [det2_smul_right,hu,mul_one]) (by rw [det2_smul_right,hv,mul_one])
    ((1-t)*r) s (mul_nonneg (by linarith [ht.2]) hr.le) hs.1
  apply hno
  calc
    ε • qb-((1-t)*r) • (b-a)-s • (c-b) =
        ((b+ε • qb)-((1-t)*r) • (b-a))-(b+s • (c-b)) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

end Zarankiewicz

end

end OAI
