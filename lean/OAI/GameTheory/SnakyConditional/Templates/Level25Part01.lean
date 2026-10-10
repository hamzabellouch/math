import OAI.GameTheory.SnakyConditional.Templates.Level24Part02

namespace OAI

namespace SnakyConditional
def required_559 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_559 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 2), (9, -4), (9, -3), (9, -2), (9, -1), (10, -4), (10, -3), (10, -2), (10, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_559 : Fin 4 → Finset Cell := ![(placedSet 4 (1, -2) required_228), (placedSet 3 (-1, 0) required_7), (placedSet 4 (0, 1) required_155), (placedSet 5 (0, 1) required_538)]
def childrenD_559 : Fin 4 → Finset Cell := ![(placedSet 4 (1, -2) envelope_228), (placedSet 3 (-1, 0) envelope_7), (placedSet 4 (0, 1) envelope_155), (placedSet 5 (0, 1) envelope_538)]
theorem common_sub_559 : commonEnvelope childrenD_559 ⊆ insert (0, 0) required_559 := by decide
theorem child_required_sub_559 : ∀ j, childrenC_559 j ⊆ insert (0, 0) required_559 := by decide
theorem Internal.SnakyRows008C.containment_559_0 :
    placedSet 4 (1, -2) envelope_228 ⊆ envelope_559 := by decide
theorem Internal.SnakyRows008C.containment_559_1 :
    placedSet 3 (-1, 0) envelope_7 ⊆ envelope_559 := by decide
theorem Internal.SnakyRows008C.containment_559_2 :
    placedSet 4 (0, 1) envelope_155 ⊆ envelope_559 := by decide
theorem Internal.SnakyRows008C.containment_559_3 :
    placedSet 5 (0, 1) envelope_538 ⊆ envelope_559 := by decide
theorem child_envelope_sub_559 : ∀ j, childrenD_559 j ⊆ envelope_559 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_559_0
  · exact Internal.SnakyRows008C.containment_559_1
  · exact Internal.SnakyRows008C.containment_559_2
  · exact Internal.SnakyRows008C.containment_559_3
theorem pivot_mem_559 : (0, 0) ∈ envelope_559 := by decide
theorem children_work_559 : ∀ j, Template HasSnaky 22 (childrenC_559 j) (childrenD_559 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_228 4 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_155 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_538 5 (0, 1)).mono (by decide)
theorem row_works_559 : Template HasSnaky 23 required_559 envelope_559 := by
  refine compose HasSnaky 22 childrenC_559 childrenD_559 children_work_559 (0, 0)
    required_559 envelope_559 pivot_mem_559 child_required_sub_559 child_envelope_sub_559 ?_
  intro b hb; exact common_sub_559 (mem_commonEnvelope childrenD_559 b hb)
end SnakyConditional

end OAI
