import OAI.GameTheory.SnakyConditional.Templates.Level22Part05
import OAI.GameTheory.SnakyConditional.Templates.Level22Part06

namespace OAI

namespace SnakyConditional
def required_470 : Finset Cell := ⟨(([(0, -1), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_470 : Finset Cell := ⟨(([(-2, 6), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_470 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (0, -2) required_468)]
def childrenD_470 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (0, -2) envelope_468)]
theorem common_sub_470 : commonEnvelope childrenD_470 ⊆ insert (0, 0) required_470 := by decide
theorem child_required_sub_470 : ∀ j, childrenC_470 j ⊆ insert (0, 0) required_470 := by decide
theorem child_envelope_sub_470 : ∀ j, childrenD_470 j ⊆ envelope_470 := by decide
theorem pivot_mem_470 : (0, 0) ∈ envelope_470 := by decide
theorem children_work_470 : ∀ j, Template HasSnaky 20 (childrenC_470 j) (childrenD_470 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_468 0 (0, -2)).mono (by decide)
theorem row_works_470 : Template HasSnaky 21 required_470 envelope_470 := by
  refine compose HasSnaky 20 childrenC_470 childrenD_470 children_work_470 (0, 0)
    required_470 envelope_470 pivot_mem_470 child_required_sub_470 child_envelope_sub_470 ?_
  intro b hb; exact common_sub_470 (mem_commonEnvelope childrenD_470 b hb)
def required_474 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_474 : Finset Cell := ⟨(([(-3, 2), (-3, 4), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_474 : Fin 3 → Finset Cell := ![(placedSet 0 (2, 1) required_463), (placedSet 0 (-1, 1) required_70), (placedSet 1 (1, -1) required_83)]
def childrenD_474 : Fin 3 → Finset Cell := ![(placedSet 0 (2, 1) envelope_463), (placedSet 0 (-1, 1) envelope_70), (placedSet 1 (1, -1) envelope_83)]
theorem common_sub_474 : commonEnvelope childrenD_474 ⊆ insert (0, 0) required_474 := by decide
theorem child_required_sub_474 : ∀ j, childrenC_474 j ⊆ insert (0, 0) required_474 := by decide
theorem child_envelope_sub_474 : ∀ j, childrenD_474 j ⊆ envelope_474 := by decide
theorem pivot_mem_474 : (0, 0) ∈ envelope_474 := by decide
theorem children_work_474 : ∀ j, Template HasSnaky 20 (childrenC_474 j) (childrenD_474 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_463 0 (2, 1)).mono (by decide)
  · exact (placed_template_map row_works_70 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_83 1 (1, -1)).mono (by decide)
theorem row_works_474 : Template HasSnaky 21 required_474 envelope_474 := by
  refine compose HasSnaky 20 childrenC_474 childrenD_474 children_work_474 (0, 0)
    required_474 envelope_474 pivot_mem_474 child_required_sub_474 child_envelope_sub_474 ?_
  intro b hb; exact common_sub_474 (mem_commonEnvelope childrenD_474 b hb)
end SnakyConditional

end OAI
