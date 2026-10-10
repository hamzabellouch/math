import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

def det2 (u v : Plane) : ℝ := u.1*v.2-u.2*v.1

def segmentPoint (a b : Plane) (t : ℝ) : Plane := (1-t) • a+t • b

def openSegmentTrace (a b : Plane) : Set Plane := segmentPoint a b '' Set.Ioo 0 1

def SegmentsCrossProperly (a b c d : Plane) : Prop :=
  det2 (b-a) (d-c) ≠ 0 ∧
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ u ∈ Set.Ioo (0 : ℝ) 1,
      segmentPoint a b t = segmentPoint c d u

def segmentCrossingSign (a b c d : Plane) : ℝ :=
  if SegmentsCrossProperly a b c d then
    (if 0 < det2 (b-a) (d-c) then 1 else -1) else 0

@[simp] theorem segmentPoint_zero (a b : Plane) : segmentPoint a b 0 = a := by
  simp [segmentPoint]

@[simp] theorem segmentPoint_one (a b : Plane) : segmentPoint a b 1 = b := by
  simp [segmentPoint]

theorem segmentPoint_reverse (a b : Plane) (t : ℝ) :
    segmentPoint b a (1-t) = segmentPoint a b t := by
  simp [segmentPoint, add_comm]

theorem det2_swap (u v : Plane) : det2 v u = -det2 u v := by
  simp only [det2]
  ring

theorem det2_neg_left (u v : Plane) : det2 (-u) v = -det2 u v := by
  simp [det2]
  ring

theorem det2_neg_right (u v : Plane) : det2 u (-v) = -det2 u v := by
  simp [det2]
  ring

theorem segment_intersection_parameters_unique (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (t u t' u' : ℝ)
    (h : segmentPoint a b t = segmentPoint c d u)
    (h' : segmentPoint a b t' = segmentPoint c d u') : t = t' ∧ u = u' := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have h₁' := congrArg Prod.fst h'
  have h₂' := congrArg Prod.snd h'
  change (1-t)*a.1+t*b.1 = (1-u)*c.1+u*d.1 at h₁
  change (1-t)*a.2+t*b.2 = (1-u)*c.2+u*d.2 at h₂
  change (1-t')*a.1+t'*b.1 = (1-u')*c.1+u'*d.1 at h₁'
  change (1-t')*a.2+t'*b.2 = (1-u')*c.2+u'*d.2 at h₂'
  have ht : (t-t') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (d.2-c.2)*h₁ - (d.1-c.1)*h₂ - (d.2-c.2)*h₁' + (d.1-c.1)*h₂'
  have hu : (u-u') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (b.2-a.2)*h₁ - (b.1-a.1)*h₂ - (b.2-a.2)*h₁' + (b.1-a.1)*h₂'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hn),
    sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hn)⟩

end Zarankiewicz

end

end OAI
