import OAI.GameTheory.SnakyConditional.Templates.Level19Part04

namespace OAI

namespace SnakyConditional
def required_556 : Finset Cell := ⟨(([(-3, -3), (-2, -3), (-2, 0), (-1, -4), (-1, -3), (0, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_556 : Finset Cell := ⟨(([(-6, 1), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_556 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -2) required_34), (placedSet 0 (-1, 0) required_549)]
def childrenD_556 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -2) envelope_34), (placedSet 0 (-1, 0) envelope_549)]
theorem common_sub_556 : commonEnvelope childrenD_556 ⊆ insert (0, 0) required_556 := by decide
theorem child_required_sub_556 : ∀ j, childrenC_556 j ⊆ insert (0, 0) required_556 := by decide
theorem Internal.SnakyRows008C.containment_556_0 :
    placedSet 1 (0, -2) envelope_34 ⊆ envelope_556 := by decide
theorem Internal.SnakyRows008C.containment_556_1 :
    placedSet 0 (-1, 0) envelope_549 ⊆ envelope_556 := by decide
theorem child_envelope_sub_556 : ∀ j, childrenD_556 j ⊆ envelope_556 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_556_0
  · exact Internal.SnakyRows008C.containment_556_1
theorem pivot_mem_556 : (0, 0) ∈ envelope_556 := by decide
theorem children_work_556 : ∀ j, Template HasSnaky 17 (childrenC_556 j) (childrenD_556 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_34 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_549 0 (-1, 0)).mono (by decide)
theorem row_works_556 : Template HasSnaky 18 required_556 envelope_556 := by
  refine compose HasSnaky 17 childrenC_556 childrenD_556 children_work_556 (0, 0)
    required_556 envelope_556 pivot_mem_556 child_required_sub_556 child_envelope_sub_556 ?_
  intro b hb; exact common_sub_556 (mem_commonEnvelope childrenD_556 b hb)
end SnakyConditional

end OAI
