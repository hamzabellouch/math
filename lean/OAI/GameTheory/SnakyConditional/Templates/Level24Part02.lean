import OAI.GameTheory.SnakyConditional.Templates.Level23Part02
import OAI.GameTheory.SnakyConditional.Templates.Level23Part04

namespace OAI

namespace SnakyConditional
def required_518 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_518 : Finset Cell := ⟨(([(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_518 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_9), (placedSet 0 (3, 0) required_514)]
def childrenD_518 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_9), (placedSet 0 (3, 0) envelope_514)]
theorem common_sub_518 : commonEnvelope childrenD_518 ⊆ insert (0, 0) required_518 := by decide
theorem child_required_sub_518 : ∀ j, childrenC_518 j ⊆ insert (0, 0) required_518 := by decide
theorem child_envelope_sub_518 : ∀ j, childrenD_518 j ⊆ envelope_518 := by decide
theorem pivot_mem_518 : (0, 0) ∈ envelope_518 := by decide
theorem children_work_518 : ∀ j, Template HasSnaky 21 (childrenC_518 j) (childrenD_518 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_9 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_514 0 (3, 0)).mono (by decide)
theorem row_works_518 : Template HasSnaky 22 required_518 envelope_518 := by
  refine compose HasSnaky 21 childrenC_518 childrenD_518 children_work_518 (0, 0)
    required_518 envelope_518 pivot_mem_518 child_required_sub_518 child_envelope_sub_518 ?_
  intro b hb; exact common_sub_518 (mem_commonEnvelope childrenD_518 b hb)
def required_538 : Finset Cell := ⟨(([(1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_538 : Finset Cell := ⟨(([(-2, -1), (-2, 1), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_538 : Fin 4 → Finset Cell := ![(placedSet 3 (-1, -1) required_63), (placedSet 0 (0, 1) required_470), (placedSet 6 (3, 1) required_64), (placedSet 4 (-1, 0) required_55)]
def childrenD_538 : Fin 4 → Finset Cell := ![(placedSet 3 (-1, -1) envelope_63), (placedSet 0 (0, 1) envelope_470), (placedSet 6 (3, 1) envelope_64), (placedSet 4 (-1, 0) envelope_55)]
theorem common_sub_538 : commonEnvelope childrenD_538 ⊆ insert (0, 0) required_538 := by decide
theorem child_required_sub_538 : ∀ j, childrenC_538 j ⊆ insert (0, 0) required_538 := by decide
theorem child_envelope_sub_538 : ∀ j, childrenD_538 j ⊆ envelope_538 := by decide
theorem pivot_mem_538 : (0, 0) ∈ envelope_538 := by decide
theorem children_work_538 : ∀ j, Template HasSnaky 21 (childrenC_538 j) (childrenD_538 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 3 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_470 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_64 6 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 4 (-1, 0)).mono (by decide)
theorem row_works_538 : Template HasSnaky 22 required_538 envelope_538 := by
  refine compose HasSnaky 21 childrenC_538 childrenD_538 children_work_538 (0, 0)
    required_538 envelope_538 pivot_mem_538 child_required_sub_538 child_envelope_sub_538 ?_
  intro b hb; exact common_sub_538 (mem_commonEnvelope childrenD_538 b hb)
end SnakyConditional

end OAI
