import OAI.GameTheory.SnakyConditional.Templates.Level15Part05
import OAI.GameTheory.SnakyConditional.Templates.Level16Part05
import OAI.GameTheory.SnakyConditional.Templates.Level17Part04
import OAI.GameTheory.SnakyConditional.Templates.Level22Part01

namespace OAI

namespace SnakyConditional
def required_552 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_552 : Finset Cell := ⟨(([(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -3), (4, -2), (4, -1), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_552 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, 1) required_443), (placedSet 2 (-3, 1) required_64), (placedSet 1 (-1, -1) required_504), (placedSet 5 (-2, -1) required_404)]
def childrenD_552 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, 1) envelope_443), (placedSet 2 (-3, 1) envelope_64), (placedSet 1 (-1, -1) envelope_504), (placedSet 5 (-2, -1) envelope_404)]
theorem common_sub_552 : commonEnvelope childrenD_552 ⊆ insert (0, 0) required_552 := by decide
theorem child_required_sub_552 : ∀ j, childrenC_552 j ⊆ insert (0, 0) required_552 := by decide
theorem Internal.SnakyRows008C.containment_552_0 :
    placedSet 4 (-3, 1) envelope_443 ⊆ envelope_552 := by decide
theorem Internal.SnakyRows008C.containment_552_1 :
    placedSet 2 (-3, 1) envelope_64 ⊆ envelope_552 := by decide
theorem Internal.SnakyRows008C.containment_552_2 :
    placedSet 1 (-1, -1) envelope_504 ⊆ envelope_552 := by decide
theorem Internal.SnakyRows008C.containment_552_3 :
    placedSet 5 (-2, -1) envelope_404 ⊆ envelope_552 := by decide
theorem child_envelope_sub_552 : ∀ j, childrenD_552 j ⊆ envelope_552 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_552_0
  · exact Internal.SnakyRows008C.containment_552_1
  · exact Internal.SnakyRows008C.containment_552_2
  · exact Internal.SnakyRows008C.containment_552_3
theorem pivot_mem_552 : (0, 0) ∈ envelope_552 := by decide
theorem children_work_552 : ∀ j, Template HasSnaky 20 (childrenC_552 j) (childrenD_552 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_443 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_64 2 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_504 1 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_404 5 (-2, -1)).mono (by decide)
theorem row_works_552 : Template HasSnaky 21 required_552 envelope_552 := by
  refine compose HasSnaky 20 childrenC_552 childrenD_552 children_work_552 (0, 0)
    required_552 envelope_552 pivot_mem_552 child_required_sub_552 child_envelope_sub_552 ?_
  intro b hb; exact common_sub_552 (mem_commonEnvelope childrenD_552 b hb)
def required_555 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_555 : Finset Cell := ⟨(([(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_555 : Fin 5 → Finset Cell := ![(placedSet 5 (-1, 1) required_504), (placedSet 0 (-3, 1) required_513), (placedSet 0 (1, 0) required_55), (placedSet 4 (-3, 1) required_443), (placedSet 1 (-3, 1) required_471)]
def childrenD_555 : Fin 5 → Finset Cell := ![(placedSet 5 (-1, 1) envelope_504), (placedSet 0 (-3, 1) envelope_513), (placedSet 0 (1, 0) envelope_55), (placedSet 4 (-3, 1) envelope_443), (placedSet 1 (-3, 1) envelope_471)]
theorem common_sub_555 : commonEnvelope childrenD_555 ⊆ insert (0, 0) required_555 := by decide
theorem child_required_sub_555 : ∀ j, childrenC_555 j ⊆ insert (0, 0) required_555 := by decide
theorem Internal.SnakyRows008C.containment_555_0 :
    placedSet 5 (-1, 1) envelope_504 ⊆ envelope_555 := by decide
theorem Internal.SnakyRows008C.containment_555_1 :
    placedSet 0 (-3, 1) envelope_513 ⊆ envelope_555 := by decide
theorem Internal.SnakyRows008C.containment_555_2 :
    placedSet 0 (1, 0) envelope_55 ⊆ envelope_555 := by decide
theorem Internal.SnakyRows008C.containment_555_3 :
    placedSet 4 (-3, 1) envelope_443 ⊆ envelope_555 := by decide
theorem Internal.SnakyRows008C.containment_555_4 :
    placedSet 1 (-3, 1) envelope_471 ⊆ envelope_555 := by decide
theorem child_envelope_sub_555 : ∀ j, childrenD_555 j ⊆ envelope_555 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_555_0
  · exact Internal.SnakyRows008C.containment_555_1
  · exact Internal.SnakyRows008C.containment_555_2
  · exact Internal.SnakyRows008C.containment_555_3
  · exact Internal.SnakyRows008C.containment_555_4
theorem pivot_mem_555 : (0, 0) ∈ envelope_555 := by decide
theorem children_work_555 : ∀ j, Template HasSnaky 20 (childrenC_555 j) (childrenD_555 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_504 5 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_513 0 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_443 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_471 1 (-3, 1)).mono (by decide)
theorem row_works_555 : Template HasSnaky 21 required_555 envelope_555 := by
  refine compose HasSnaky 20 childrenC_555 childrenD_555 children_work_555 (0, 0)
    required_555 envelope_555 pivot_mem_555 child_required_sub_555 child_envelope_sub_555 ?_
  intro b hb; exact common_sub_555 (mem_commonEnvelope childrenD_555 b hb)
end SnakyConditional

end OAI
