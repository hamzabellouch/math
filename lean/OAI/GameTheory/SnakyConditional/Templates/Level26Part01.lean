import OAI.GameTheory.SnakyConditional.Templates.Level25Part01

namespace OAI

namespace SnakyConditional
def required_562 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_562 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_562 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -4) required_6), (placedSet 0 (0, 1) required_559)]
def childrenD_562 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -4) envelope_6), (placedSet 0 (0, 1) envelope_559)]
theorem common_sub_562 : commonEnvelope childrenD_562 ⊆ insert (0, 0) required_562 := by decide
theorem child_required_sub_562 : ∀ j, childrenC_562 j ⊆ insert (0, 0) required_562 := by decide
theorem Internal.SnakyRows008.containment_562_0 :
    placedSet 7 (-1, -4) envelope_6 ⊆ envelope_562 := by decide
theorem Internal.SnakyRows008.containment_562_1 :
    placedSet 0 (0, 1) envelope_559 ⊆ envelope_562 := by decide
theorem child_envelope_sub_562 : ∀ j, childrenD_562 j ⊆ envelope_562 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_562_0
  · exact Internal.SnakyRows008.containment_562_1
theorem pivot_mem_562 : (0, 0) ∈ envelope_562 := by decide
theorem children_work_562 : ∀ j, Template HasSnaky 23 (childrenC_562 j) (childrenD_562 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 7 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_559 0 (0, 1)).mono (by decide)
theorem row_works_562 : Template HasSnaky 24 required_562 envelope_562 := by
  refine compose HasSnaky 23 childrenC_562 childrenD_562 children_work_562 (0, 0)
    required_562 envelope_562 pivot_mem_562 child_required_sub_562 child_envelope_sub_562 ?_
  intro b hb; exact common_sub_562 (mem_commonEnvelope childrenD_562 b hb)
end SnakyConditional

end OAI
