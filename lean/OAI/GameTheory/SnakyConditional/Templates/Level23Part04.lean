import OAI.GameTheory.SnakyConditional.Templates.Level16Part04
import OAI.GameTheory.SnakyConditional.Templates.Level22Part01

namespace OAI

namespace SnakyConditional
def required_479 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_479 : Finset Cell := ⟨(([(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_479 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_55), (placedSet 0 (0, 1) required_443), (placedSet 4 (-3, 1) required_443)]
def childrenD_479 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_55), (placedSet 0 (0, 1) envelope_443), (placedSet 4 (-3, 1) envelope_443)]
theorem common_sub_479 : commonEnvelope childrenD_479 ⊆ insert (0, 0) required_479 := by decide
theorem child_required_sub_479 : ∀ j, childrenC_479 j ⊆ insert (0, 0) required_479 := by decide
theorem child_envelope_sub_479 : ∀ j, childrenD_479 j ⊆ envelope_479 := by decide
theorem pivot_mem_479 : (0, 0) ∈ envelope_479 := by decide
theorem children_work_479 : ∀ j, Template HasSnaky 20 (childrenC_479 j) (childrenD_479 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_443 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_443 4 (-3, 1)).mono (by decide)
theorem row_works_479 : Template HasSnaky 21 required_479 envelope_479 := by
  refine compose HasSnaky 20 childrenC_479 childrenD_479 children_work_479 (0, 0)
    required_479 envelope_479 pivot_mem_479 child_required_sub_479 child_envelope_sub_479 ?_
  intro b hb; exact common_sub_479 (mem_commonEnvelope childrenD_479 b hb)
def required_514 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_514 : Finset Cell := ⟨(([(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_514 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_57), (placedSet 4 (-3, 1) required_443), (placedSet 0 (-3, 1) required_510)]
def childrenD_514 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_57), (placedSet 4 (-3, 1) envelope_443), (placedSet 0 (-3, 1) envelope_510)]
theorem common_sub_514 : commonEnvelope childrenD_514 ⊆ insert (0, 0) required_514 := by decide
theorem child_required_sub_514 : ∀ j, childrenC_514 j ⊆ insert (0, 0) required_514 := by decide
theorem child_envelope_sub_514 : ∀ j, childrenD_514 j ⊆ envelope_514 := by decide
theorem pivot_mem_514 : (0, 0) ∈ envelope_514 := by decide
theorem children_work_514 : ∀ j, Template HasSnaky 20 (childrenC_514 j) (childrenD_514 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_57 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_443 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_510 0 (-3, 1)).mono (by decide)
theorem row_works_514 : Template HasSnaky 21 required_514 envelope_514 := by
  refine compose HasSnaky 20 childrenC_514 childrenD_514 children_work_514 (0, 0)
    required_514 envelope_514 pivot_mem_514 child_required_sub_514 child_envelope_sub_514 ?_
  intro b hb; exact common_sub_514 (mem_commonEnvelope childrenD_514 b hb)
end SnakyConditional

end OAI
