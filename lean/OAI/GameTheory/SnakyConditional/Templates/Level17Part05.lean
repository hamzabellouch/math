import OAI.GameTheory.SnakyConditional.Templates.Level16Part01
import OAI.GameTheory.SnakyConditional.Templates.Level16Part03

namespace OAI

namespace SnakyConditional
def required_472 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_472 : Finset Cell := ⟨(([(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_472 : Fin 2 → Finset Cell := ![(placedSet 5 (1, -4) required_6), (placedSet 0 (2, -1) required_466)]
def childrenD_472 : Fin 2 → Finset Cell := ![(placedSet 5 (1, -4) envelope_6), (placedSet 0 (2, -1) envelope_466)]
theorem common_sub_472 : commonEnvelope childrenD_472 ⊆ insert (0, 0) required_472 := by decide
theorem child_required_sub_472 : ∀ j, childrenC_472 j ⊆ insert (0, 0) required_472 := by decide
theorem child_envelope_sub_472 : ∀ j, childrenD_472 j ⊆ envelope_472 := by decide
theorem pivot_mem_472 : (0, 0) ∈ envelope_472 := by decide
theorem children_work_472 : ∀ j, Template HasSnaky 14 (childrenC_472 j) (childrenD_472 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 5 (1, -4)).mono (by decide)
  · exact (placed_template_map row_works_466 0 (2, -1)).mono (by decide)
theorem row_works_472 : Template HasSnaky 15 required_472 envelope_472 := by
  refine compose HasSnaky 14 childrenC_472 childrenD_472 children_work_472 (0, 0)
    required_472 envelope_472 pivot_mem_472 child_required_sub_472 child_envelope_sub_472 ?_
  intro b hb; exact common_sub_472 (mem_commonEnvelope childrenD_472 b hb)
def required_497 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_497 : Finset Cell := ⟨(([(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_497 : Fin 3 → Finset Cell := ![(placedSet 2 (-1, 0) required_36), (placedSet 0 (3, 0) required_167), (placedSet 0 (3, -1) required_410)]
def childrenD_497 : Fin 3 → Finset Cell := ![(placedSet 2 (-1, 0) envelope_36), (placedSet 0 (3, 0) envelope_167), (placedSet 0 (3, -1) envelope_410)]
theorem common_sub_497 : commonEnvelope childrenD_497 ⊆ insert (0, 0) required_497 := by decide
theorem child_required_sub_497 : ∀ j, childrenC_497 j ⊆ insert (0, 0) required_497 := by decide
theorem child_envelope_sub_497 : ∀ j, childrenD_497 j ⊆ envelope_497 := by decide
theorem pivot_mem_497 : (0, 0) ∈ envelope_497 := by decide
theorem children_work_497 : ∀ j, Template HasSnaky 14 (childrenC_497 j) (childrenD_497 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_36 2 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_167 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_410 0 (3, -1)).mono (by decide)
theorem row_works_497 : Template HasSnaky 15 required_497 envelope_497 := by
  refine compose HasSnaky 14 childrenC_497 childrenD_497 children_work_497 (0, 0)
    required_497 envelope_497 pivot_mem_497 child_required_sub_497 child_envelope_sub_497 ?_
  intro b hb; exact common_sub_497 (mem_commonEnvelope childrenD_497 b hb)
end SnakyConditional

end OAI
