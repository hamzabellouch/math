import OAI.GameTheory.SnakyConditional.Templates.Level15Part06
import OAI.GameTheory.SnakyConditional.Templates.Level24Part01

namespace OAI

namespace SnakyConditional
def required_560 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_560 : Finset Cell := ⟨(([(-7, 1), (-6, 0), (-6, 1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (9, -1), (9, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_560 : Fin 5 → Finset Cell := ![(placedSet 5 (1, 0) required_517), (placedSet 5 (0, -1) required_416), (placedSet 5 (-1, 0) required_359), (placedSet 6 (-1, 0) required_356), (placedSet 0 (0, 2) required_483)]
def childrenD_560 : Fin 5 → Finset Cell := ![(placedSet 5 (1, 0) envelope_517), (placedSet 5 (0, -1) envelope_416), (placedSet 5 (-1, 0) envelope_359), (placedSet 6 (-1, 0) envelope_356), (placedSet 0 (0, 2) envelope_483)]
theorem common_sub_560 : commonEnvelope childrenD_560 ⊆ insert (0, 0) required_560 := by decide
theorem child_required_sub_560 : ∀ j, childrenC_560 j ⊆ insert (0, 0) required_560 := by decide
theorem Internal.SnakyRows008.containment_560_0 :
    placedSet 5 (1, 0) envelope_517 ⊆ envelope_560 := by decide
theorem Internal.SnakyRows008.containment_560_1 :
    placedSet 5 (0, -1) envelope_416 ⊆ envelope_560 := by decide
theorem Internal.SnakyRows008.containment_560_2 :
    placedSet 5 (-1, 0) envelope_359 ⊆ envelope_560 := by decide
theorem Internal.SnakyRows008.containment_560_3 :
    placedSet 6 (-1, 0) envelope_356 ⊆ envelope_560 := by decide
theorem Internal.SnakyRows008.containment_560_4 :
    placedSet 0 (0, 2) envelope_483 ⊆ envelope_560 := by decide +kernel
theorem child_envelope_sub_560 : ∀ j, childrenD_560 j ⊆ envelope_560 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_560_0
  · exact Internal.SnakyRows008.containment_560_1
  · exact Internal.SnakyRows008.containment_560_2
  · exact Internal.SnakyRows008.containment_560_3
  · exact Internal.SnakyRows008.containment_560_4
theorem pivot_mem_560 : (0, 0) ∈ envelope_560 := by decide
theorem children_work_560 : ∀ j, Template HasSnaky 22 (childrenC_560 j) (childrenD_560 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_517 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_416 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_359 5 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_356 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_483 0 (0, 2)).mono (by decide)
theorem row_works_560 : Template HasSnaky 23 required_560 envelope_560 := by
  refine compose HasSnaky 22 childrenC_560 childrenD_560 children_work_560 (0, 0)
    required_560 envelope_560 pivot_mem_560 child_required_sub_560 child_envelope_sub_560 ?_
  intro b hb; exact common_sub_560 (mem_commonEnvelope childrenD_560 b hb)
end SnakyConditional

end OAI
