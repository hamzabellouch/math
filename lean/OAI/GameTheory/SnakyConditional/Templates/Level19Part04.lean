import OAI.GameTheory.SnakyConditional.Templates.Level15Part05
import OAI.GameTheory.SnakyConditional.Templates.Level18Part02
import OAI.GameTheory.SnakyConditional.Templates.Level18Part06

namespace OAI

namespace SnakyConditional
def required_549 : Finset Cell := ⟨(([(-2, -3), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_549 : Finset Cell := ⟨(([(-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_549 : Fin 6 → Finset Cell := ![(placedSet 0 (2, 0) required_385), (placedSet 4 (-2, 0) required_385), (placedSet 0 (2, 0) required_330), (placedSet 6 (-2, 0) required_252), (placedSet 0 (2, 0) required_326), (placedSet 0 (-2, 0) required_529)]
def childrenD_549 : Fin 6 → Finset Cell := ![(placedSet 0 (2, 0) envelope_385), (placedSet 4 (-2, 0) envelope_385), (placedSet 0 (2, 0) envelope_330), (placedSet 6 (-2, 0) envelope_252), (placedSet 0 (2, 0) envelope_326), (placedSet 0 (-2, 0) envelope_529)]
theorem common_sub_549 : commonEnvelope childrenD_549 ⊆ insert (0, 0) required_549 := by decide
theorem child_required_sub_549 : ∀ j, childrenC_549 j ⊆ insert (0, 0) required_549 := by decide
theorem Internal.SnakyRows008C.containment_549_0 :
    placedSet 0 (2, 0) envelope_385 ⊆ envelope_549 := by decide
theorem Internal.SnakyRows008C.containment_549_1 :
    placedSet 4 (-2, 0) envelope_385 ⊆ envelope_549 := by decide
theorem Internal.SnakyRows008C.containment_549_2 :
    placedSet 0 (2, 0) envelope_330 ⊆ envelope_549 := by decide
theorem Internal.SnakyRows008C.containment_549_3 :
    placedSet 6 (-2, 0) envelope_252 ⊆ envelope_549 := by decide
theorem Internal.SnakyRows008C.containment_549_4 :
    placedSet 0 (2, 0) envelope_326 ⊆ envelope_549 := by decide
theorem Internal.SnakyRows008C.containment_549_5 :
    placedSet 0 (-2, 0) envelope_529 ⊆ envelope_549 := by decide
theorem child_envelope_sub_549 : ∀ j, childrenD_549 j ⊆ envelope_549 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_549_0
  · exact Internal.SnakyRows008C.containment_549_1
  · exact Internal.SnakyRows008C.containment_549_2
  · exact Internal.SnakyRows008C.containment_549_3
  · exact Internal.SnakyRows008C.containment_549_4
  · exact Internal.SnakyRows008C.containment_549_5
theorem pivot_mem_549 : (0, 0) ∈ envelope_549 := by decide
theorem children_work_549 : ∀ j, Template HasSnaky 16 (childrenC_549 j) (childrenD_549 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_385 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_385 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_330 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_252 6 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_326 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_529 0 (-2, 0)).mono (by decide)
theorem row_works_549 : Template HasSnaky 17 required_549 envelope_549 := by
  refine compose HasSnaky 16 childrenC_549 childrenD_549 children_work_549 (0, 0)
    required_549 envelope_549 pivot_mem_549 child_required_sub_549 child_envelope_sub_549 ?_
  intro b hb; exact common_sub_549 (mem_commonEnvelope childrenD_549 b hb)
def required_553 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_553 : Finset Cell := ⟨(([(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_553 : Fin 6 → Finset Cell := ![(placedSet 0 (-1, 1) required_63), (placedSet 4 (1, 0) required_261), (placedSet 0 (1, -3) required_471), (placedSet 0 (0, 1) required_442), (placedSet 0 (-1, -1) required_504), (placedSet 0 (0, 1) required_180)]
def childrenD_553 : Fin 6 → Finset Cell := ![(placedSet 0 (-1, 1) envelope_63), (placedSet 4 (1, 0) envelope_261), (placedSet 0 (1, -3) envelope_471), (placedSet 0 (0, 1) envelope_442), (placedSet 0 (-1, -1) envelope_504), (placedSet 0 (0, 1) envelope_180)]
theorem common_sub_553 : commonEnvelope childrenD_553 ⊆ insert (0, 0) required_553 := by decide
theorem child_required_sub_553 : ∀ j, childrenC_553 j ⊆ insert (0, 0) required_553 := by decide
theorem Internal.SnakyRows008C.containment_553_0 :
    placedSet 0 (-1, 1) envelope_63 ⊆ envelope_553 := by decide
theorem Internal.SnakyRows008C.containment_553_1 :
    placedSet 4 (1, 0) envelope_261 ⊆ envelope_553 := by decide
theorem Internal.SnakyRows008C.containment_553_2 :
    placedSet 0 (1, -3) envelope_471 ⊆ envelope_553 := by decide
theorem Internal.SnakyRows008C.containment_553_3 :
    placedSet 0 (0, 1) envelope_442 ⊆ envelope_553 := by decide
theorem Internal.SnakyRows008C.containment_553_4 :
    placedSet 0 (-1, -1) envelope_504 ⊆ envelope_553 := by decide
theorem Internal.SnakyRows008C.containment_553_5 :
    placedSet 0 (0, 1) envelope_180 ⊆ envelope_553 := by decide
theorem child_envelope_sub_553 : ∀ j, childrenD_553 j ⊆ envelope_553 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_553_0
  · exact Internal.SnakyRows008C.containment_553_1
  · exact Internal.SnakyRows008C.containment_553_2
  · exact Internal.SnakyRows008C.containment_553_3
  · exact Internal.SnakyRows008C.containment_553_4
  · exact Internal.SnakyRows008C.containment_553_5
theorem pivot_mem_553 : (0, 0) ∈ envelope_553 := by decide
theorem children_work_553 : ∀ j, Template HasSnaky 16 (childrenC_553 j) (childrenD_553 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_261 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_471 0 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_442 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_504 0 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_180 0 (0, 1)).mono (by decide)
theorem row_works_553 : Template HasSnaky 17 required_553 envelope_553 := by
  refine compose HasSnaky 16 childrenC_553 childrenD_553 children_work_553 (0, 0)
    required_553 envelope_553 pivot_mem_553 child_required_sub_553 child_envelope_sub_553 ?_
  intro b hb; exact common_sub_553 (mem_commonEnvelope childrenD_553 b hb)
end SnakyConditional

end OAI
