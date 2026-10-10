import OAI.Analysis.CircleDomains.Topology.CenteredBoundary
import OAI.Analysis.CircleDomains.Topology.TwoArcSimpleLoop

namespace OAI

/-! A positively parametrized boundary arc closes a disk crosscut to a
simple loop. The resulting circle uses only the existing Schoenflies input. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

@[simp] theorem standardCirclePoint_zero : standardCirclePoint 0 = 1 := by
  simp only [standardCirclePoint, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero, Circle.coe_one]

theorem boundary_angle_pos {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    0 < unitCircleCut (normalizedArgument a) := by
  apply lt_of_le_of_ne (unitCircleCut_mem _).1
  intro h
  apply ha1
  rw [← standardCirclePoint_normalizedArgument ha]
  have he : normalizedArgument a = 0 := by
    have hc : (unitCircleCut (normalizedArgument a) : UnitAddCircle) = normalizedArgument a :=
      AddCircle.coe_equivIco
    rw [← h] at hc
    exact hc.symm
  rw [he, standardCirclePoint_zero]

theorem boundary_arc_parameter_mem {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) (t : PathTime) :
    unitCircleCut (normalizedArgument a) * (t : ℝ) ∈ Ico (0 : ℝ) 1 := by
  have hpos := boundary_angle_pos ha ha1
  exact ⟨mul_nonneg hpos.le t.property.1,
    (mul_le_of_le_one_right hpos.le t.property.2).trans_lt (unitCircleCut_mem _).2⟩

def boundaryClosingArc (a : ℂ) (ha : ‖a‖ = 1) : Path 1 a where
  toFun t := standardCirclePoint ((unitCircleCut (normalizedArgument a) * (t : ℝ) : ℝ) : UnitAddCircle)
  continuous_toFun :=
    (continuous_subtype_val.comp (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous).comp
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.mul continuous_subtype_val))
  source' := by
    change standardCirclePoint ((unitCircleCut (normalizedArgument a) * 0 : ℝ) : UnitAddCircle) = 1
    simp only [mul_zero, AddCircle.coe_zero, standardCirclePoint_zero]
  target' := by
    change standardCirclePoint ((unitCircleCut (normalizedArgument a) * 1 : ℝ) : UnitAddCircle) = a
    simp only [mul_one]
    rw [show (unitCircleCut (normalizedArgument a) : UnitAddCircle) = normalizedArgument a from
      AddCircle.coe_equivIco]
    exact standardCirclePoint_normalizedArgument ha

theorem boundaryClosingArc_norm (a : ℂ) (ha : ‖a‖ = 1) (t : PathTime) :
    ‖boundaryClosingArc a ha t‖ = 1 := Circle.norm_coe _

theorem boundaryClosingArc_injective {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    Injective (boundaryClosingArc a ha) := by
  intro s t he
  have hc := standardCirclePoint_injective he
  have hs : unitCircleCut (normalizedArgument a) * (s : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using boundary_arc_parameter_mem ha ha1 s
  have ht : unitCircleCut (normalizedArgument a) * (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using boundary_arc_parameter_mem ha ha1 t
  have hst := (AddCircle.coe_eq_coe_iff_of_mem_Ico hs ht).mp hc
  apply Subtype.ext
  exact mul_left_cancel₀ (ne_of_gt (boundary_angle_pos ha ha1)) hst

theorem crosscut_boundary_intersections {a : ℂ} (p : Path a 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∀ s t : PathTime, p s = boundaryClosingArc a ha t →
      (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1) := by
  intro s t he
  have hi := boundaryClosingArc_injective ha ha1
  by_cases hs0 : s = 0
  · right
    refine ⟨hs0, hi ?_⟩
    simpa only [hs0, p.source, (boundaryClosingArc a ha).target] using he.symm
  by_cases hs1 : s = 1
  · left
    refine ⟨hs1, hi ?_⟩
    simpa only [hs1, p.target, (boundaryClosingArc a ha).source] using he.symm
  have hh := hp s ⟨lt_of_le_of_ne bot_le (Ne.symm hs0), lt_of_le_of_ne le_top hs1⟩
  rw [he, boundaryClosingArc_norm] at hh
  exact (lt_irrefl _ hh).elim

theorem exists_schoenflies_of_disk_crosscut (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a 1) (hi : Injective p)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle,
      H z = circleOfClosedPath (p.trans (boundaryClosingArc a ha))
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z) := by
  apply exists_schoenflies_of_simple_closed_path hsch
  exact two_arc_loop_injective_before_end p (boundaryClosingArc a ha) hi
    (boundaryClosingArc_injective ha ha1) (crosscut_boundary_intersections p hp ha ha1)

end CircleDomainRigidity

end

end OAI
