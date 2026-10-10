import OAI.Combinatorics.Crossing.TriangleEntryExit

namespace OAI

noncomputable section
namespace Zarankiewicz

def TriangleSegmentPosition (a b c d e : Plane) : Prop :=
  (∀ i : Fin 3, det2 (triangleEnd a b c i-triangleStart a b c i) (e-d) ≠ 0) ∧
  (∀ i : Fin 3, orient2 d e (triangleStart a b c i) ≠ 0) ∧
  (∀ i : Fin 3, orient2 (triangleStart a b c i) (triangleEnd a b c i) d ≠ 0 ∧
    orient2 (triangleStart a b c i) (triangleEnd a b c i) e ≠ 0)

theorem triangle_consecutive_roots_ne (a b c d e : Plane)
    (ha : orient2 a b c ≠ 0) (h₀ : det2 (b-a) (e-d) ≠ 0)
    (h₁ : det2 (c-b) (e-d) ≠ 0) (hb : orient2 d e b ≠ 0) :
    secondIntersectionParameter a b d e ≠ secondIntersectionParameter b c d e := by
  intro heq
  have hz : orient2 b c (segmentPoint a b (firstIntersectionParameter a b d e)) = 0 := by
    rw [intersection_parameters_eq a b d e h₀,heq,
      ← intersection_parameters_eq b c d e h₁,orient2_self_segment]
  rw [triangle_side_at_first_edge] at hz
  have ht : firstIntersectionParameter a b d e = 1 := by
    have := (mul_eq_zero.mp hz).resolve_right ha
    linarith
  have hp := intersection_parameters_eq a b d e h₀
  rw [ht,segmentPoint_one] at hp
  apply hb
  rw [hp,orient2_self_segment]

theorem second_parameter_ne_zero (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (hc : orient2 a b c ≠ 0) :
    secondIntersectionParameter a b c d ≠ 0 := by
  intro h
  have hh := affine_side_factor a b c d hn 0
  rw [h,segmentPoint_zero] at hh
  apply hc
  simpa using hh

theorem second_parameter_ne_one (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (hd : orient2 a b d ≠ 0) :
    secondIntersectionParameter a b c d ≠ 1 := by
  intro h
  have hh := affine_side_factor a b c d hn 1
  rw [h,segmentPoint_one] at hh
  apply hd
  simpa using hh

theorem triangle_roots_injective (a b c d e : Plane) (ha : orient2 a b c ≠ 0)
    (h : TriangleSegmentPosition a b c d e) :
    Function.Injective (fun i : Fin 3 =>
      secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e) := by
  have h₀ := triangle_consecutive_roots_ne a b c d e ha (h.1 0) (h.1 1) (h.2.1 1)
  have ha₁ : orient2 b c a ≠ 0 := by rwa [triangle_area_cycle]
  have ha₂ : orient2 c a b ≠ 0 := by rwa [triangle_area_cycle,triangle_area_cycle]
  have h₁ := triangle_consecutive_roots_ne b c a d e ha₁ (h.1 1) (h.1 2) (h.2.1 2)
  have h₂ := triangle_consecutive_roots_ne c a b d e ha₂ (h.1 2) (h.1 0) (h.2.1 0)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [triangleStart,triangleEnd]

theorem triangle_segment_entry_exit_of_position (a b c d e : Plane)
    (ha : 0 < orient2 a b c) (h : TriangleSegmentPosition a b c d e) :
    triangleSegmentIntersection a b c d e = triangleIndicator a b c e-triangleIndicator a b c d := by
  exact triangle_segment_entry_exit a b c d e ha h.1
    (triangle_roots_injective a b c d e (ne_of_gt ha) h)
    (fun i => second_parameter_ne_zero _ _ _ _ (h.1 i) (h.2.2 i).1)
    (fun i => second_parameter_ne_one _ _ _ _ (h.1 i) (h.2.2 i).2)

end Zarankiewicz

end

end OAI
