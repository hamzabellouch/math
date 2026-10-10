import OAI.GameTheory.SnakyConditional.Templates.Level17Part06
import OAI.GameTheory.SnakyConditional.Templates.Level23Part02
import OAI.GameTheory.SnakyConditional.Templates.Level23Part05

namespace OAI

namespace SnakyConditional
def required_554 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_554 : Finset Cell := ⟨(([(-3, 3), (-3, 5), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_554 : Fin 3 → Finset Cell := ![(placedSet 6 (1, 0) required_30), (placedSet 7 (0, 1) required_96), (placedSet 0 (0, 1) required_474)]
def childrenD_554 : Fin 3 → Finset Cell := ![(placedSet 6 (1, 0) envelope_30), (placedSet 7 (0, 1) envelope_96), (placedSet 0 (0, 1) envelope_474)]
theorem common_sub_554 : commonEnvelope childrenD_554 ⊆ insert (0, 0) required_554 := by decide
theorem child_required_sub_554 : ∀ j, childrenC_554 j ⊆ insert (0, 0) required_554 := by decide
theorem Internal.SnakyRows008C.containment_554_0 :
    placedSet 6 (1, 0) envelope_30 ⊆ envelope_554 := by decide
theorem Internal.SnakyRows008C.containment_554_1 :
    placedSet 7 (0, 1) envelope_96 ⊆ envelope_554 := by decide
theorem Internal.SnakyRows008C.containment_554_2 :
    placedSet 0 (0, 1) envelope_474 ⊆ envelope_554 := by decide
theorem child_envelope_sub_554 : ∀ j, childrenD_554 j ⊆ envelope_554 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_554_0
  · exact Internal.SnakyRows008C.containment_554_1
  · exact Internal.SnakyRows008C.containment_554_2
theorem pivot_mem_554 : (0, 0) ∈ envelope_554 := by decide
theorem children_work_554 : ∀ j, Template HasSnaky 21 (childrenC_554 j) (childrenD_554 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_30 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_96 7 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_474 0 (0, 1)).mono (by decide)
theorem row_works_554 : Template HasSnaky 22 required_554 envelope_554 := by
  refine compose HasSnaky 21 childrenC_554 childrenD_554 children_work_554 (0, 0)
    required_554 envelope_554 pivot_mem_554 child_required_sub_554 child_envelope_sub_554 ?_
  intro b hb; exact common_sub_554 (mem_commonEnvelope childrenD_554 b hb)
def required_561 : Finset Cell := ⟨(([(-2, -2), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_561 : Finset Cell := ⟨(([(-7, 2), (-7, 4), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_561 : Fin 7 → Finset Cell := ![(placedSet 0 (1, 0) required_295), (placedSet 2 (1, 0) required_173), (placedSet 6 (-3, 0) required_263), (placedSet 1 (1, 1) required_236), (placedSet 4 (1, 0) required_546), (placedSet 2 (1, 0) required_176), (placedSet 0 (0, 1) required_535)]
def childrenD_561 : Fin 7 → Finset Cell := ![(placedSet 0 (1, 0) envelope_295), (placedSet 2 (1, 0) envelope_173), (placedSet 6 (-3, 0) envelope_263), (placedSet 1 (1, 1) envelope_236), (placedSet 4 (1, 0) envelope_546), (placedSet 2 (1, 0) envelope_176), (placedSet 0 (0, 1) envelope_535)]
theorem common_sub_561 : commonEnvelope childrenD_561 ⊆ insert (0, 0) required_561 := by decide
theorem child_required_sub_561 : ∀ j, childrenC_561 j ⊆ insert (0, 0) required_561 := by decide
theorem Internal.SnakyRows008.containment_561_0 :
    placedSet 0 (1, 0) envelope_295 ⊆ envelope_561 := by decide
theorem Internal.SnakyRows008.containment_561_1 :
    placedSet 2 (1, 0) envelope_173 ⊆ envelope_561 := by decide
theorem Internal.SnakyRows008.containment_561_2 :
    placedSet 6 (-3, 0) envelope_263 ⊆ envelope_561 := by decide
theorem Internal.SnakyRows008.containment_561_3 :
    placedSet 1 (1, 1) envelope_236 ⊆ envelope_561 := by decide
theorem Internal.SnakyRows008.containment_561_4 :
    placedSet 4 (1, 0) envelope_546 ⊆ envelope_561 := by decide
theorem Internal.SnakyRows008.containment_561_5 :
    placedSet 2 (1, 0) envelope_176 ⊆ envelope_561 := by decide
theorem Internal.SnakyRows008.containment_561_6 :
    placedSet 0 (0, 1) envelope_535 ⊆ envelope_561 := by decide
theorem child_envelope_sub_561 : ∀ j, childrenD_561 j ⊆ envelope_561 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_561_0
  · exact Internal.SnakyRows008.containment_561_1
  · exact Internal.SnakyRows008.containment_561_2
  · exact Internal.SnakyRows008.containment_561_3
  · exact Internal.SnakyRows008.containment_561_4
  · exact Internal.SnakyRows008.containment_561_5
  · exact Internal.SnakyRows008.containment_561_6
theorem pivot_mem_561 : (0, 0) ∈ envelope_561 := by decide
theorem children_work_561 : ∀ j, Template HasSnaky 21 (childrenC_561 j) (childrenD_561 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_295 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_173 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_263 6 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_236 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_546 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_176 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_535 0 (0, 1)).mono (by decide)
theorem row_works_561 : Template HasSnaky 22 required_561 envelope_561 := by
  refine compose HasSnaky 21 childrenC_561 childrenD_561 children_work_561 (0, 0)
    required_561 envelope_561 pivot_mem_561 child_required_sub_561 child_envelope_sub_561 ?_
  intro b hb; exact common_sub_561 (mem_commonEnvelope childrenD_561 b hb)
end SnakyConditional

end OAI
