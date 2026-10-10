import OAI.GameTheory.SnakyConditional.Templates.Level16Part04
import OAI.GameTheory.SnakyConditional.Templates.Level22Part01

namespace OAI

namespace SnakyConditional
def required_546 : Finset Cell := ⟨(([(1, 0), (2, 0), (3, -2), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_546 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -3), (2, -2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_546 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) required_64), (placedSet 7 (0, -1) required_482), (placedSet 0 (3, 1) required_443), (placedSet 6 (3, 1) required_64)]
def childrenD_546 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) envelope_64), (placedSet 7 (0, -1) envelope_482), (placedSet 0 (3, 1) envelope_443), (placedSet 6 (3, 1) envelope_64)]
theorem common_sub_546 : commonEnvelope childrenD_546 ⊆ insert (0, 0) required_546 := by decide
theorem child_required_sub_546 : ∀ j, childrenC_546 j ⊆ insert (0, 0) required_546 := by decide
theorem Internal.SnakyRows008C.containment_546_0 :
    placedSet 0 (0, -1) envelope_64 ⊆ envelope_546 := by decide
theorem Internal.SnakyRows008C.containment_546_1 :
    placedSet 7 (0, -1) envelope_482 ⊆ envelope_546 := by decide
theorem Internal.SnakyRows008C.containment_546_2 :
    placedSet 0 (3, 1) envelope_443 ⊆ envelope_546 := by decide
theorem Internal.SnakyRows008C.containment_546_3 :
    placedSet 6 (3, 1) envelope_64 ⊆ envelope_546 := by decide
theorem child_envelope_sub_546 : ∀ j, childrenD_546 j ⊆ envelope_546 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_546_0
  · exact Internal.SnakyRows008C.containment_546_1
  · exact Internal.SnakyRows008C.containment_546_2
  · exact Internal.SnakyRows008C.containment_546_3
theorem pivot_mem_546 : (0, 0) ∈ envelope_546 := by decide
theorem children_work_546 : ∀ j, Template HasSnaky 20 (childrenC_546 j) (childrenD_546 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_482 7 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_443 0 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_64 6 (3, 1)).mono (by decide)
theorem row_works_546 : Template HasSnaky 21 required_546 envelope_546 := by
  refine compose HasSnaky 20 childrenC_546 childrenD_546 children_work_546 (0, 0)
    required_546 envelope_546 pivot_mem_546 child_required_sub_546 child_envelope_sub_546 ?_
  intro b hb; exact common_sub_546 (mem_commonEnvelope childrenD_546 b hb)
def required_547 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_547 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_547 : Fin 3 → Finset Cell := ![(placedSet 0 (3, 1) required_443), (placedSet 4 (3, 1) required_510), (placedSet 3 (-1, 0) required_131)]
def childrenD_547 : Fin 3 → Finset Cell := ![(placedSet 0 (3, 1) envelope_443), (placedSet 4 (3, 1) envelope_510), (placedSet 3 (-1, 0) envelope_131)]
theorem common_sub_547 : commonEnvelope childrenD_547 ⊆ insert (0, 0) required_547 := by decide
theorem child_required_sub_547 : ∀ j, childrenC_547 j ⊆ insert (0, 0) required_547 := by decide
theorem Internal.SnakyRows008C.containment_547_0 :
    placedSet 0 (3, 1) envelope_443 ⊆ envelope_547 := by decide
theorem Internal.SnakyRows008C.containment_547_1 :
    placedSet 4 (3, 1) envelope_510 ⊆ envelope_547 := by decide
theorem Internal.SnakyRows008C.containment_547_2 :
    placedSet 3 (-1, 0) envelope_131 ⊆ envelope_547 := by decide
theorem child_envelope_sub_547 : ∀ j, childrenD_547 j ⊆ envelope_547 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_547_0
  · exact Internal.SnakyRows008C.containment_547_1
  · exact Internal.SnakyRows008C.containment_547_2
theorem pivot_mem_547 : (0, 0) ∈ envelope_547 := by decide
theorem children_work_547 : ∀ j, Template HasSnaky 20 (childrenC_547 j) (childrenD_547 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_443 0 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_510 4 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_131 3 (-1, 0)).mono (by decide)
theorem row_works_547 : Template HasSnaky 21 required_547 envelope_547 := by
  refine compose HasSnaky 20 childrenC_547 childrenD_547 children_work_547 (0, 0)
    required_547 envelope_547 pivot_mem_547 child_required_sub_547 child_envelope_sub_547 ?_
  intro b hb; exact common_sub_547 (mem_commonEnvelope childrenD_547 b hb)
end SnakyConditional

end OAI
