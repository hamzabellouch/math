import OAI.GameTheory.SnakyConditional.Templates.Level23Part05
import OAI.GameTheory.SnakyConditional.Templates.Level25Part04

namespace OAI

namespace SnakyConditional
def required_568 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_568 : Finset Cell := ⟨(([(-7, 2), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_568 : Fin 5 → Finset Cell := ![(placedSet 4 (2, 0) required_538), (placedSet 0 (-2, 0) required_547), (placedSet 0 (2, 0) required_275), (placedSet 0 (-2, 0) required_565), (placedSet 0 (2, 0) required_330)]
def childrenD_568 : Fin 5 → Finset Cell := ![(placedSet 4 (2, 0) envelope_538), (placedSet 0 (-2, 0) envelope_547), (placedSet 0 (2, 0) envelope_275), (placedSet 0 (-2, 0) envelope_565), (placedSet 0 (2, 0) envelope_330)]
theorem common_sub_568 : commonEnvelope childrenD_568 ⊆ insert (0, 0) required_568 := by decide
theorem child_required_sub_568 : ∀ j, childrenC_568 j ⊆ insert (0, 0) required_568 := by decide
theorem Internal.SnakyRows008.containment_568_0 :
    placedSet 4 (2, 0) envelope_538 ⊆ envelope_568 := by decide
theorem Internal.SnakyRows008.containment_568_1 :
    placedSet 0 (-2, 0) envelope_547 ⊆ envelope_568 := by decide
theorem Internal.SnakyRows008.containment_568_2 :
    placedSet 0 (2, 0) envelope_275 ⊆ envelope_568 := by decide
theorem Internal.SnakyRows008.containment_568_3 :
    placedSet 0 (-2, 0) envelope_565 ⊆ envelope_568 := by decide +kernel
theorem Internal.SnakyRows008.containment_568_4 :
    placedSet 0 (2, 0) envelope_330 ⊆ envelope_568 := by decide
theorem child_envelope_sub_568 : ∀ j, childrenD_568 j ⊆ envelope_568 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_568_0
  · exact Internal.SnakyRows008.containment_568_1
  · exact Internal.SnakyRows008.containment_568_2
  · exact Internal.SnakyRows008.containment_568_3
  · exact Internal.SnakyRows008.containment_568_4
theorem pivot_mem_568 : (0, 0) ∈ envelope_568 := by decide
theorem children_work_568 : ∀ j, Template HasSnaky 23 (childrenC_568 j) (childrenD_568 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_538 4 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_547 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_275 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_565 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_330 0 (2, 0)).mono (by decide)
theorem row_works_568 : Template HasSnaky 24 required_568 envelope_568 := by
  refine compose HasSnaky 23 childrenC_568 childrenD_568 children_work_568 (0, 0)
    required_568 envelope_568 pivot_mem_568 child_required_sub_568 child_envelope_sub_568 ?_
  intro b hb; exact common_sub_568 (mem_commonEnvelope childrenD_568 b hb)
end SnakyConditional

end OAI
