import OAI.GameTheory.SnakyConditional.Templates.Level21Part02

namespace OAI

namespace SnakyConditional
def required_545 : Finset Cell := ⟨(([(-1, -1), (0, -2), (0, -1), (1, -2), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_545 : Finset Cell := ⟨(([(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_545 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) required_256), (placedSet 0 (1, 0) required_448), (placedSet 0 (2, -1) required_153), (placedSet 0 (0, 1) required_343)]
def childrenD_545 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) envelope_256), (placedSet 0 (1, 0) envelope_448), (placedSet 0 (2, -1) envelope_153), (placedSet 0 (0, 1) envelope_343)]
theorem common_sub_545 : commonEnvelope childrenD_545 ⊆ insert (0, 0) required_545 := by decide
theorem child_required_sub_545 : ∀ j, childrenC_545 j ⊆ insert (0, 0) required_545 := by decide
theorem Internal.SnakyRows008C.containment_545_0 :
    placedSet 0 (0, 1) envelope_256 ⊆ envelope_545 := by decide
theorem Internal.SnakyRows008C.containment_545_1 :
    placedSet 0 (1, 0) envelope_448 ⊆ envelope_545 := by decide
theorem Internal.SnakyRows008C.containment_545_2 :
    placedSet 0 (2, -1) envelope_153 ⊆ envelope_545 := by decide
theorem Internal.SnakyRows008C.containment_545_3 :
    placedSet 0 (0, 1) envelope_343 ⊆ envelope_545 := by decide
theorem child_envelope_sub_545 : ∀ j, childrenD_545 j ⊆ envelope_545 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_545_0
  · exact Internal.SnakyRows008C.containment_545_1
  · exact Internal.SnakyRows008C.containment_545_2
  · exact Internal.SnakyRows008C.containment_545_3
theorem pivot_mem_545 : (0, 0) ∈ envelope_545 := by decide
theorem children_work_545 : ∀ j, Template HasSnaky 19 (childrenC_545 j) (childrenD_545 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_256 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_448 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_153 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_343 0 (0, 1)).mono (by decide)
theorem row_works_545 : Template HasSnaky 20 required_545 envelope_545 := by
  refine compose HasSnaky 19 childrenC_545 childrenD_545 children_work_545 (0, 0)
    required_545 envelope_545 pivot_mem_545 child_required_sub_545 child_envelope_sub_545 ?_
  intro b hb; exact common_sub_545 (mem_commonEnvelope childrenD_545 b hb)
end SnakyConditional

end OAI
