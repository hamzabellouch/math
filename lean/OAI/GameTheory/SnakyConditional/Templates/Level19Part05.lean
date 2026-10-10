import OAI.GameTheory.SnakyConditional.Templates.Level15Part05
import OAI.GameTheory.SnakyConditional.Templates.Level16Part03
import OAI.GameTheory.SnakyConditional.Templates.Level18Part02

namespace OAI

namespace SnakyConditional
def required_566 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_566 : Finset Cell := ⟨(([(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_566 : Fin 5 → Finset Cell := ![(placedSet 0 (-1, 0) required_314), (placedSet 0 (0, 1) required_180), (placedSet 0 (0, 1) required_442), (placedSet 0 (2, -1) required_466), (placedSet 0 (-1, -1) required_504)]
def childrenD_566 : Fin 5 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_314), (placedSet 0 (0, 1) envelope_180), (placedSet 0 (0, 1) envelope_442), (placedSet 0 (2, -1) envelope_466), (placedSet 0 (-1, -1) envelope_504)]
theorem common_sub_566 : commonEnvelope childrenD_566 ⊆ insert (0, 0) required_566 := by decide
theorem child_required_sub_566 : ∀ j, childrenC_566 j ⊆ insert (0, 0) required_566 := by decide
theorem Internal.SnakyRows008.containment_566_0 :
    placedSet 0 (-1, 0) envelope_314 ⊆ envelope_566 := by decide
theorem Internal.SnakyRows008.containment_566_1 :
    placedSet 0 (0, 1) envelope_180 ⊆ envelope_566 := by decide
theorem Internal.SnakyRows008.containment_566_2 :
    placedSet 0 (0, 1) envelope_442 ⊆ envelope_566 := by decide
theorem Internal.SnakyRows008.containment_566_3 :
    placedSet 0 (2, -1) envelope_466 ⊆ envelope_566 := by decide
theorem Internal.SnakyRows008.containment_566_4 :
    placedSet 0 (-1, -1) envelope_504 ⊆ envelope_566 := by decide
theorem child_envelope_sub_566 : ∀ j, childrenD_566 j ⊆ envelope_566 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_566_0
  · exact Internal.SnakyRows008.containment_566_1
  · exact Internal.SnakyRows008.containment_566_2
  · exact Internal.SnakyRows008.containment_566_3
  · exact Internal.SnakyRows008.containment_566_4
theorem pivot_mem_566 : (0, 0) ∈ envelope_566 := by decide
theorem children_work_566 : ∀ j, Template HasSnaky 16 (childrenC_566 j) (childrenD_566 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_314 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_180 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_442 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_466 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_504 0 (-1, -1)).mono (by decide)
theorem row_works_566 : Template HasSnaky 17 required_566 envelope_566 := by
  refine compose HasSnaky 16 childrenC_566 childrenD_566 children_work_566 (0, 0)
    required_566 envelope_566 pivot_mem_566 child_required_sub_566 child_envelope_sub_566 ?_
  intro b hb; exact common_sub_566 (mem_commonEnvelope childrenD_566 b hb)
end SnakyConditional

end OAI
