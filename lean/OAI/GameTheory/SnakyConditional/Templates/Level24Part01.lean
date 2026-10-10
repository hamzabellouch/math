import OAI.GameTheory.SnakyConditional.Templates.Level17Part04
import OAI.GameTheory.SnakyConditional.Templates.Level23Part02
import OAI.GameTheory.SnakyConditional.Templates.Level23Part03

namespace OAI

namespace SnakyConditional
def required_483 : Finset Cell := ⟨(([(-2, -3), (-2, -2), (-2, -1), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_483 : Finset Cell := ⟨(([(-7, -1), (-6, -2), (-6, -1), (-5, -2), (-5, -1), (-4, -2), (-4, -1), (-3, -2), (-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3), (8, -2), (8, -1), (9, -3), (9, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_483 : Fin 5 → Finset Cell := ![(placedSet 1 (0, 1) required_173), (placedSet 7 (-1, -3) required_292), (placedSet 1 (-1, 1) required_319), (placedSet 6 (0, -3) required_192), (placedSet 1 (0, 1) required_475)]
def childrenD_483 : Fin 5 → Finset Cell := ![(placedSet 1 (0, 1) envelope_173), (placedSet 7 (-1, -3) envelope_292), (placedSet 1 (-1, 1) envelope_319), (placedSet 6 (0, -3) envelope_192), (placedSet 1 (0, 1) envelope_475)]
theorem common_sub_483 : commonEnvelope childrenD_483 ⊆ insert (0, 0) required_483 := by decide
theorem child_required_sub_483 : ∀ j, childrenC_483 j ⊆ insert (0, 0) required_483 := by decide
theorem child_envelope_sub_483 : ∀ j, childrenD_483 j ⊆ envelope_483 := by decide
theorem pivot_mem_483 : (0, 0) ∈ envelope_483 := by decide
theorem children_work_483 : ∀ j, Template HasSnaky 21 (childrenC_483 j) (childrenD_483 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_173 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_292 7 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_319 1 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_192 6 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_475 1 (0, 1)).mono (by decide)
theorem row_works_483 : Template HasSnaky 22 required_483 envelope_483 := by
  refine compose HasSnaky 21 childrenC_483 childrenD_483 children_work_483 (0, 0)
    required_483 envelope_483 pivot_mem_483 child_required_sub_483 child_envelope_sub_483 ?_
  intro b hb; exact common_sub_483 (mem_commonEnvelope childrenD_483 b hb)
def required_490 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_490 : Finset Cell := ⟨(([(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_490 : Fin 4 → Finset Cell := ![(placedSet 1 (-1, -3) required_64), (placedSet 0 (1, -3) required_471), (placedSet 1 (1, -3) required_470), (placedSet 0 (-1, -3) required_111)]
def childrenD_490 : Fin 4 → Finset Cell := ![(placedSet 1 (-1, -3) envelope_64), (placedSet 0 (1, -3) envelope_471), (placedSet 1 (1, -3) envelope_470), (placedSet 0 (-1, -3) envelope_111)]
theorem common_sub_490 : commonEnvelope childrenD_490 ⊆ insert (0, 0) required_490 := by decide
theorem child_required_sub_490 : ∀ j, childrenC_490 j ⊆ insert (0, 0) required_490 := by decide
theorem child_envelope_sub_490 : ∀ j, childrenD_490 j ⊆ envelope_490 := by decide
theorem pivot_mem_490 : (0, 0) ∈ envelope_490 := by decide
theorem children_work_490 : ∀ j, Template HasSnaky 21 (childrenC_490 j) (childrenD_490 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 1 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_471 0 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_470 1 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_111 0 (-1, -3)).mono (by decide)
theorem row_works_490 : Template HasSnaky 22 required_490 envelope_490 := by
  refine compose HasSnaky 21 childrenC_490 childrenD_490 children_work_490 (0, 0)
    required_490 envelope_490 pivot_mem_490 child_required_sub_490 child_envelope_sub_490 ?_
  intro b hb; exact common_sub_490 (mem_commonEnvelope childrenD_490 b hb)
end SnakyConditional

end OAI
