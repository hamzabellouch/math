import OAI.Combinatorics.Crossing.RoundCircleChords
import OAI.Combinatorics.Crossing.FiniteLineAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem spokes_meet_only_at_center (v a b : Plane) (hd : det2 (a-v) (b-v) ≠ 0)
    {x : Plane} (ha : x ∈ segment ℝ v a) (hb : x ∈ segment ℝ v b) : x=v := by
  rw [← Path.range_segment] at ha hb
  obtain ⟨s,hs⟩ := ha
  obtain ⟨t,ht⟩ := hb
  have hs' : segmentPoint v a s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint v b t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hp := segment_intersection_parameters_unique v a v b hd s.val t.val 0 0
    (hs'.trans ht'.symm) (by simp)
  rw [hp.1,segmentPoint_zero] at hs'
  exact hs'.symm

theorem spoke_in_open_disk (z v a : Plane) (r : ℝ)
    (hv : squaredLength (v-z) < r^2) (ha : squaredLength (a-z)=r^2)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    squaredLength (segmentPoint v a t-z) < r^2 := by
  have he : squaredLength (segmentPoint v a t-z)=
      (1-t)*squaredLength (v-z)+t*squaredLength (a-z)-t*(1-t)*squaredLength (a-v) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hpos := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hv)
  have hnon : 0 ≤ t*(1-t)*squaredLength (a-v) := by
    apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2.le))
    dsimp [squaredLength]
    positivity
  rw [he,ha]
  nlinarith

theorem exists_vertex_disk_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Plane) (r : ℝ) (hr : 0 < r) (p : ι → Plane) (hp : Function.Injective p)
    (hcircle : ∀ i, squaredLength (p i-z)=r^2) :
    ∃ v : Plane, squaredLength (v-z) < r^2 ∧
      (∀ i, v ≠ p i) ∧ (∀ i j, i ≠ j → det2 (p i-v) (p j-v) ≠ 0) := by
  classical
  let S := {ij : ι × ι // ij.1 ≠ ij.2}
  obtain ⟨v,hv,havoid⟩ := exists_near_avoiding_lines
    (fun ij : S => p ij.val.1) (fun ij : S => p ij.val.2-p ij.val.1)
    (fun ij => sub_ne_zero.mpr (hp.ne (Ne.symm ij.property))) z (r/3) (by positivity)
  have hinside : squaredLength (v-z) < r^2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff,abs_lt,abs_lt] at hv
    have h₁ := mul_pos (sub_pos.mpr hv.1.2) (show 0 < r/3+(v.1-z.1) by linarith [hv.1.1])
    have h₂ := mul_pos (sub_pos.mpr hv.2.2) (show 0 < r/3+(v.2-z.2) by linarith [hv.2.1])
    change (v.1-z.1)^2+(v.2-z.2)^2 < r^2
    nlinarith [sq_pos_of_pos hr]
  refine ⟨v,hinside,?_,?_⟩
  · intro i he
    rw [he,hcircle i] at hinside
    exact lt_irrefl _ hinside
  · intro i j hij
    have he : det2 (p i-v) (p j-v) = -det2 (v-p i) (p j-p i) := by dsimp [det2]; ring
    rw [he]
    exact neg_ne_zero.mpr (havoid ⟨(i,j),hij⟩)

end Zarankiewicz

end

end OAI
