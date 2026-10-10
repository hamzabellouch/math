import OAI.GameTheory.SnakyConditional.Templates.Level22Part08
import OAI.GameTheory.SnakyConditional.Templates.Level24Part02

namespace OAI

namespace SnakyConditional
def required_563 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_563 : Finset Cell := ⟨(([(-5, 2), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_563 : Fin 5 → Finset Cell := ![(placedSet 0 (3, 0) required_167), (placedSet 0 (-1, 0) required_538), (placedSet 0 (3, 0) required_514), (placedSet 4 (-1, 0) required_330), (placedSet 0 (1, 1) required_545)]
def childrenD_563 : Fin 5 → Finset Cell := ![(placedSet 0 (3, 0) envelope_167), (placedSet 0 (-1, 0) envelope_538), (placedSet 0 (3, 0) envelope_514), (placedSet 4 (-1, 0) envelope_330), (placedSet 0 (1, 1) envelope_545)]
theorem common_sub_563 : commonEnvelope childrenD_563 ⊆ insert (0, 0) required_563 := by decide
theorem child_required_sub_563 : ∀ j, childrenC_563 j ⊆ insert (0, 0) required_563 := by decide
theorem Internal.SnakyRows008.containment_563_0 :
    placedSet 0 (3, 0) envelope_167 ⊆ envelope_563 := by decide
theorem Internal.SnakyRows008.containment_563_1 :
    placedSet 0 (-1, 0) envelope_538 ⊆ envelope_563 := by decide
theorem Internal.SnakyRows008.containment_563_2 :
    placedSet 0 (3, 0) envelope_514 ⊆ envelope_563 := by decide
theorem Internal.SnakyRows008.containment_563_3 :
    placedSet 4 (-1, 0) envelope_330 ⊆ envelope_563 := by decide
theorem Internal.SnakyRows008.containment_563_4 :
    placedSet 0 (1, 1) envelope_545 ⊆ envelope_563 := by decide
theorem child_envelope_sub_563 : ∀ j, childrenD_563 j ⊆ envelope_563 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_563_0
  · exact Internal.SnakyRows008.containment_563_1
  · exact Internal.SnakyRows008.containment_563_2
  · exact Internal.SnakyRows008.containment_563_3
  · exact Internal.SnakyRows008.containment_563_4
theorem pivot_mem_563 : (0, 0) ∈ envelope_563 := by decide
theorem children_work_563 : ∀ j, Template HasSnaky 22 (childrenC_563 j) (childrenD_563 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_167 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_538 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_514 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_330 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_545 0 (1, 1)).mono (by decide)
theorem row_works_563 : Template HasSnaky 23 required_563 envelope_563 := by
  refine compose HasSnaky 22 childrenC_563 childrenD_563 children_work_563 (0, 0)
    required_563 envelope_563 pivot_mem_563 child_required_sub_563 child_envelope_sub_563 ?_
  intro b hb; exact common_sub_563 (mem_commonEnvelope childrenD_563 b hb)
end SnakyConditional

end OAI
