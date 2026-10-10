import OAI.GameTheory.SnakyConditional.Templates.Level15Part06

namespace OAI

namespace SnakyConditional
def required_551 : Finset Cell := ⟨(([(0, 1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_551 : Finset Cell := ⟨(([(-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_551 : Fin 5 → Finset Cell := ![(placedSet 6 (0, -1) required_300), (placedSet 7 (0, -1) required_172), (placedSet 3 (1, 3) required_319), (placedSet 4 (1, 3) required_527), (placedSet 5 (0, -1) required_176)]
def childrenD_551 : Fin 5 → Finset Cell := ![(placedSet 6 (0, -1) envelope_300), (placedSet 7 (0, -1) envelope_172), (placedSet 3 (1, 3) envelope_319), (placedSet 4 (1, 3) envelope_527), (placedSet 5 (0, -1) envelope_176)]
theorem common_sub_551 : commonEnvelope childrenD_551 ⊆ insert (0, 0) required_551 := by decide
theorem child_required_sub_551 : ∀ j, childrenC_551 j ⊆ insert (0, 0) required_551 := by decide
theorem Internal.SnakyRows008C.containment_551_0 :
    placedSet 6 (0, -1) envelope_300 ⊆ envelope_551 := by decide
theorem Internal.SnakyRows008C.containment_551_1 :
    placedSet 7 (0, -1) envelope_172 ⊆ envelope_551 := by decide
theorem Internal.SnakyRows008C.containment_551_2 :
    placedSet 3 (1, 3) envelope_319 ⊆ envelope_551 := by decide
theorem Internal.SnakyRows008C.containment_551_3 :
    placedSet 4 (1, 3) envelope_527 ⊆ envelope_551 := by decide
theorem Internal.SnakyRows008C.containment_551_4 :
    placedSet 5 (0, -1) envelope_176 ⊆ envelope_551 := by decide
theorem child_envelope_sub_551 : ∀ j, childrenD_551 j ⊆ envelope_551 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_551_0
  · exact Internal.SnakyRows008C.containment_551_1
  · exact Internal.SnakyRows008C.containment_551_2
  · exact Internal.SnakyRows008C.containment_551_3
  · exact Internal.SnakyRows008C.containment_551_4
theorem pivot_mem_551 : (0, 0) ∈ envelope_551 := by decide
theorem children_work_551 : ∀ j, Template HasSnaky 13 (childrenC_551 j) (childrenD_551 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_300 6 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_172 7 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_319 3 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_527 4 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_176 5 (0, -1)).mono (by decide)
theorem row_works_551 : Template HasSnaky 14 required_551 envelope_551 := by
  refine compose HasSnaky 13 childrenC_551 childrenD_551 children_work_551 (0, 0)
    required_551 envelope_551 pivot_mem_551 child_required_sub_551 child_envelope_sub_551 ?_
  intro b hb; exact common_sub_551 (mem_commonEnvelope childrenD_551 b hb)
end SnakyConditional

end OAI
