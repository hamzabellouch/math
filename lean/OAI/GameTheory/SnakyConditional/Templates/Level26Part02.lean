import OAI.GameTheory.SnakyConditional.Templates.Level10Part08
import OAI.GameTheory.SnakyConditional.Templates.Level25Part02

namespace OAI

namespace SnakyConditional
def required_564 : Finset Cell := ⟨(([(-2, -2), (-2, -1), (-2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_564 : Finset Cell := ⟨(([(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (9, -2), (9, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_564 : Fin 9 → Finset Cell := ![(placedSet 0 (0, -1) required_560), (placedSet 0 (-1, 0) required_421), (placedSet 1 (-1, 0) required_401), (placedSet 3 (-1, 0) required_340), (placedSet 0 (-1, 0) required_509), (placedSet 0 (0, -1) required_528), (placedSet 5 (0, -1) required_423), (placedSet 5 (0, -1) required_425), (placedSet 0 (-1, 0) required_336)]
def childrenD_564 : Fin 9 → Finset Cell := ![(placedSet 0 (0, -1) envelope_560), (placedSet 0 (-1, 0) envelope_421), (placedSet 1 (-1, 0) envelope_401), (placedSet 3 (-1, 0) envelope_340), (placedSet 0 (-1, 0) envelope_509), (placedSet 0 (0, -1) envelope_528), (placedSet 5 (0, -1) envelope_423), (placedSet 5 (0, -1) envelope_425), (placedSet 0 (-1, 0) envelope_336)]
theorem common_sub_564 : commonEnvelope childrenD_564 ⊆ insert (0, 0) required_564 := by decide
theorem child_required_sub_564 : ∀ j, childrenC_564 j ⊆ insert (0, 0) required_564 := by decide
theorem Internal.SnakyRows008.containment_564_0 :
    placedSet 0 (0, -1) envelope_560 ⊆ envelope_564 := by decide +kernel
theorem Internal.SnakyRows008.containment_564_1 :
    placedSet 0 (-1, 0) envelope_421 ⊆ envelope_564 := by decide
theorem Internal.SnakyRows008.containment_564_2 :
    placedSet 1 (-1, 0) envelope_401 ⊆ envelope_564 := by decide
theorem Internal.SnakyRows008.containment_564_3 :
    placedSet 3 (-1, 0) envelope_340 ⊆ envelope_564 := by decide
theorem Internal.SnakyRows008.containment_564_4 :
    placedSet 0 (-1, 0) envelope_509 ⊆ envelope_564 := by decide
theorem Internal.SnakyRows008.containment_564_5 :
    placedSet 0 (0, -1) envelope_528 ⊆ envelope_564 := by decide
theorem Internal.SnakyRows008.containment_564_6 :
    placedSet 5 (0, -1) envelope_423 ⊆ envelope_564 := by decide
theorem Internal.SnakyRows008.containment_564_7 :
    placedSet 5 (0, -1) envelope_425 ⊆ envelope_564 := by decide
theorem Internal.SnakyRows008.containment_564_8 :
    placedSet 0 (-1, 0) envelope_336 ⊆ envelope_564 := by decide
theorem child_envelope_sub_564 : ∀ j, childrenD_564 j ⊆ envelope_564 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008.containment_564_0
  · exact Internal.SnakyRows008.containment_564_1
  · exact Internal.SnakyRows008.containment_564_2
  · exact Internal.SnakyRows008.containment_564_3
  · exact Internal.SnakyRows008.containment_564_4
  · exact Internal.SnakyRows008.containment_564_5
  · exact Internal.SnakyRows008.containment_564_6
  · exact Internal.SnakyRows008.containment_564_7
  · exact Internal.SnakyRows008.containment_564_8
theorem pivot_mem_564 : (0, 0) ∈ envelope_564 := by decide
theorem children_work_564 : ∀ j, Template HasSnaky 23 (childrenC_564 j) (childrenD_564 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_560 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_421 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_401 1 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_340 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_509 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_528 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_423 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_425 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_336 0 (-1, 0)).mono (by decide)
theorem row_works_564 : Template HasSnaky 24 required_564 envelope_564 := by
  refine compose HasSnaky 23 childrenC_564 childrenD_564 children_work_564 (0, 0)
    required_564 envelope_564 pivot_mem_564 child_required_sub_564 child_envelope_sub_564 ?_
  intro b hb; exact common_sub_564 (mem_commonEnvelope childrenD_564 b hb)
end SnakyConditional

end OAI
