import OAI.GameTheory.SnakyConditional.Templates.Level22Part04
import OAI.GameTheory.SnakyConditional.Templates.Level24Part02

namespace OAI

namespace SnakyConditional
def required_565 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_565 : Finset Cell := ⟨(([(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_565 : Fin 5 → Finset Cell := ![(placedSet 4 (0, 1) required_443), (placedSet 3 (-1, 0) required_131), (placedSet 0 (-1, 0) required_538), (placedSet 0 (1, 1) required_459), (placedSet 4 (-1, 0) required_144)]
def childrenD_565 : Fin 5 → Finset Cell := ![(placedSet 4 (0, 1) envelope_443), (placedSet 3 (-1, 0) envelope_131), (placedSet 0 (-1, 0) envelope_538), (placedSet 0 (1, 1) envelope_459), (placedSet 4 (-1, 0) envelope_144)]
theorem common_sub_565 : commonEnvelope childrenD_565 ⊆ insert (0, 0) required_565 := by decide
theorem child_required_sub_565 : ∀ j, childrenC_565 j ⊆ insert (0, 0) required_565 := by decide
theorem Internal.SnakyRows008.containment_565_0 :
    placedSet 4 (0, 1) envelope_443 ⊆ envelope_565 := by decide
theorem Internal.SnakyRows008.containment_565_1 :
    placedSet 3 (-1, 0) envelope_131 ⊆ envelope_565 := by decide
theorem Internal.SnakyRows008.containment_565_2 :
    placedSet 0 (-1, 0) envelope_538 ⊆ envelope_565 := by decide
theorem Internal.SnakyRows008.containment_565_3 :
    placedSet 0 (1, 1) envelope_459 ⊆ envelope_565 := by decide
theorem Internal.SnakyRows008.containment_565_4 :
    placedSet 4 (-1, 0) envelope_144 ⊆ envelope_565 := by decide
theorem child_envelope_sub_565 : ∀ j, childrenD_565 j ⊆ envelope_565 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_565_0
  · exact Internal.SnakyRows008.containment_565_1
  · exact Internal.SnakyRows008.containment_565_2
  · exact Internal.SnakyRows008.containment_565_3
  · exact Internal.SnakyRows008.containment_565_4
theorem pivot_mem_565 : (0, 0) ∈ envelope_565 := by decide
theorem children_work_565 : ∀ j, Template HasSnaky 22 (childrenC_565 j) (childrenD_565 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_443 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_131 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_538 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_459 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_144 4 (-1, 0)).mono (by decide)
theorem row_works_565 : Template HasSnaky 23 required_565 envelope_565 := by
  refine compose HasSnaky 22 childrenC_565 childrenD_565 children_work_565 (0, 0)
    required_565 envelope_565 pivot_mem_565 child_required_sub_565 child_envelope_sub_565 ?_
  intro b hb; exact common_sub_565 (mem_commonEnvelope childrenD_565 b hb)
end SnakyConditional

end OAI
