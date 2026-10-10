import OAI.GameTheory.SnakyConditional.Templates.Level07Part08
import OAI.GameTheory.SnakyConditional.Templates.Level08Part06
import OAI.GameTheory.SnakyConditional.Templates.Level09Part03
import OAI.GameTheory.SnakyConditional.Templates.Level09Part05
import OAI.GameTheory.SnakyConditional.Templates.Level09Part06

namespace OAI

namespace SnakyConditional
def required_509 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_509 : Finset Cell := ⟨(([(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_509 : Fin 4 → Finset Cell := ![(placedSet 0 (2, 0) required_252), (placedSet 4 (-2, 0) required_241), (placedSet 0 (2, -1) required_455), (placedSet 2 (2, 0) required_68)]
def childrenD_509 : Fin 4 → Finset Cell := ![(placedSet 0 (2, 0) envelope_252), (placedSet 4 (-2, 0) envelope_241), (placedSet 0 (2, -1) envelope_455), (placedSet 2 (2, 0) envelope_68)]
theorem common_sub_509 : commonEnvelope childrenD_509 ⊆ insert (0, 0) required_509 := by decide
theorem child_required_sub_509 : ∀ j, childrenC_509 j ⊆ insert (0, 0) required_509 := by decide
theorem child_envelope_sub_509 : ∀ j, childrenD_509 j ⊆ envelope_509 := by decide
theorem pivot_mem_509 : (0, 0) ∈ envelope_509 := by decide
theorem children_work_509 : ∀ j, Template HasSnaky 7 (childrenC_509 j) (childrenD_509 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_252 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_241 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_455 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_68 2 (2, 0)).mono (by decide)
theorem row_works_509 : Template HasSnaky 8 required_509 envelope_509 := by
  refine compose HasSnaky 7 childrenC_509 childrenD_509 children_work_509 (0, 0)
    required_509 envelope_509 pivot_mem_509 child_required_sub_509 child_envelope_sub_509 ?_
  intro b hb; exact common_sub_509 (mem_commonEnvelope childrenD_509 b hb)
def required_520 : Finset Cell := ⟨(([(-2, -3), (-1, 0), (1, -2), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_520 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_520 : Fin 5 → Finset Cell := ![(placedSet 0 (-2, -1) required_254), (placedSet 5 (2, 0) required_200), (placedSet 6 (1, -1) required_271), (placedSet 2 (1, -1) required_215), (placedSet 4 (-2, 0) required_252)]
def childrenD_520 : Fin 5 → Finset Cell := ![(placedSet 0 (-2, -1) envelope_254), (placedSet 5 (2, 0) envelope_200), (placedSet 6 (1, -1) envelope_271), (placedSet 2 (1, -1) envelope_215), (placedSet 4 (-2, 0) envelope_252)]
theorem common_sub_520 : commonEnvelope childrenD_520 ⊆ insert (0, 0) required_520 := by decide
theorem child_required_sub_520 : ∀ j, childrenC_520 j ⊆ insert (0, 0) required_520 := by decide
theorem child_envelope_sub_520 : ∀ j, childrenD_520 j ⊆ envelope_520 := by decide
theorem pivot_mem_520 : (0, 0) ∈ envelope_520 := by decide
theorem children_work_520 : ∀ j, Template HasSnaky 7 (childrenC_520 j) (childrenD_520 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_254 0 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_200 5 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_271 6 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_215 2 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_252 4 (-2, 0)).mono (by decide)
theorem row_works_520 : Template HasSnaky 8 required_520 envelope_520 := by
  refine compose HasSnaky 7 childrenC_520 childrenD_520 children_work_520 (0, 0)
    required_520 envelope_520 pivot_mem_520 child_required_sub_520 child_envelope_sub_520 ?_
  intro b hb; exact common_sub_520 (mem_commonEnvelope childrenD_520 b hb)
end SnakyConditional

end OAI
