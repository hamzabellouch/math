import OAI.GameTheory.SnakyConditional.Templates.Level24Part03

namespace OAI

namespace SnakyConditional
def required_567 : Finset Cell := ⟨(([(-1, -4), (0, -4), (0, -3), (0, -2), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_567 : Finset Cell := ⟨(([(-5, -4), (-5, -2), (-5, 2), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -1), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_567 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) required_21), (placedSet 0 (2, 0) required_561), (placedSet 4 (-1, -3) required_500)]
def childrenD_567 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -1) envelope_21), (placedSet 0 (2, 0) envelope_561), (placedSet 4 (-1, -3) envelope_500)]
theorem common_sub_567 : commonEnvelope childrenD_567 ⊆ insert (0, 0) required_567 := by decide
theorem child_required_sub_567 : ∀ j, childrenC_567 j ⊆ insert (0, 0) required_567 := by decide
theorem Internal.SnakyRows008.containment_567_0 :
    placedSet 1 (0, -1) envelope_21 ⊆ envelope_567 := by decide
theorem Internal.SnakyRows008.containment_567_1 :
    placedSet 0 (2, 0) envelope_561 ⊆ envelope_567 := by decide +kernel
theorem Internal.SnakyRows008.containment_567_2 :
    placedSet 4 (-1, -3) envelope_500 ⊆ envelope_567 := by decide
theorem child_envelope_sub_567 : ∀ j, childrenD_567 j ⊆ envelope_567 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_567_0
  · exact Internal.SnakyRows008.containment_567_1
  · exact Internal.SnakyRows008.containment_567_2
theorem pivot_mem_567 : (0, 0) ∈ envelope_567 := by decide
theorem children_work_567 : ∀ j, Template HasSnaky 22 (childrenC_567 j) (childrenD_567 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_21 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_561 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_500 4 (-1, -3)).mono (by decide)
theorem row_works_567 : Template HasSnaky 23 required_567 envelope_567 := by
  refine compose HasSnaky 22 childrenC_567 childrenD_567 children_work_567 (0, 0)
    required_567 envelope_567 pivot_mem_567 child_required_sub_567 child_envelope_sub_567 ?_
  intro b hb; exact common_sub_567 (mem_commonEnvelope childrenD_567 b hb)
end SnakyConditional

end OAI
