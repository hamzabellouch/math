import OAI.GameTheory.SnakyConditional.Templates.Level14Part05
import OAI.GameTheory.SnakyConditional.Templates.Level14Part07
import OAI.GameTheory.SnakyConditional.Templates.Level19Part01
import OAI.GameTheory.SnakyConditional.Templates.Level19Part02

namespace OAI

namespace SnakyConditional
def required_531 : Finset Cell := ⟨(([(0, -2), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_531 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_531 : Fin 8 → Finset Cell := ![(placedSet 0 (1, 0) required_425), (placedSet 3 (0, -1) required_336), (placedSet 6 (0, -1) required_340), (placedSet 1 (1, 0) required_394), (placedSet 0 (1, 0) required_423), (placedSet 0 (1, 0) required_526), (placedSet 4 (0, -1) required_401), (placedSet 0 (1, 0) required_453)]
def childrenD_531 : Fin 8 → Finset Cell := ![(placedSet 0 (1, 0) envelope_425), (placedSet 3 (0, -1) envelope_336), (placedSet 6 (0, -1) envelope_340), (placedSet 1 (1, 0) envelope_394), (placedSet 0 (1, 0) envelope_423), (placedSet 0 (1, 0) envelope_526), (placedSet 4 (0, -1) envelope_401), (placedSet 0 (1, 0) envelope_453)]
theorem common_sub_531 : commonEnvelope childrenD_531 ⊆ insert (0, 0) required_531 := by decide
theorem child_required_sub_531 : ∀ j, childrenC_531 j ⊆ insert (0, 0) required_531 := by decide
theorem child_envelope_sub_531 : ∀ j, childrenD_531 j ⊆ envelope_531 := by decide
theorem pivot_mem_531 : (0, 0) ∈ envelope_531 := by decide
theorem children_work_531 : ∀ j, Template HasSnaky 17 (childrenC_531 j) (childrenD_531 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_425 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_336 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_340 6 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_394 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_423 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_526 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_401 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_453 0 (1, 0)).mono (by decide)
theorem row_works_531 : Template HasSnaky 18 required_531 envelope_531 := by
  refine compose HasSnaky 17 childrenC_531 childrenD_531 children_work_531 (0, 0)
    required_531 envelope_531 pivot_mem_531 child_required_sub_531 child_envelope_sub_531 ?_
  intro b hb; exact common_sub_531 (mem_commonEnvelope childrenD_531 b hb)
def required_539 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, -3), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_539 : Finset Cell := ⟨(([(-5, -2), (-4, -4), (-4, -2), (-4, -1), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_539 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) required_51), (placedSet 3 (0, -1) required_488), (placedSet 0 (1, 0) required_428), (placedSet 0 (1, 0) required_516)]
def childrenD_539 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) envelope_51), (placedSet 3 (0, -1) envelope_488), (placedSet 0 (1, 0) envelope_428), (placedSet 0 (1, 0) envelope_516)]
theorem common_sub_539 : commonEnvelope childrenD_539 ⊆ insert (0, 0) required_539 := by decide
theorem child_required_sub_539 : ∀ j, childrenC_539 j ⊆ insert (0, 0) required_539 := by decide
theorem child_envelope_sub_539 : ∀ j, childrenD_539 j ⊆ envelope_539 := by decide
theorem pivot_mem_539 : (0, 0) ∈ envelope_539 := by decide
theorem children_work_539 : ∀ j, Template HasSnaky 17 (childrenC_539 j) (childrenD_539 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_51 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_488 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_428 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_516 0 (1, 0)).mono (by decide)
theorem row_works_539 : Template HasSnaky 18 required_539 envelope_539 := by
  refine compose HasSnaky 17 childrenC_539 childrenD_539 children_work_539 (0, 0)
    required_539 envelope_539 pivot_mem_539 child_required_sub_539 child_envelope_sub_539 ?_
  intro b hb; exact common_sub_539 (mem_commonEnvelope childrenD_539 b hb)
end SnakyConditional

end OAI
