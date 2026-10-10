import OAI.GameTheory.SnakyConditional.Templates.Level22Part03
import OAI.GameTheory.SnakyConditional.Templates.Level22Part07

namespace OAI

namespace SnakyConditional
def required_475 : Finset Cell := ⟨(([(-3, -2), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_475 : Finset Cell := ⟨(([(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_475 : Fin 4 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 1 (0, -1) required_261), (placedSet 0 (-2, 1) required_457), (placedSet 2 (-2, 1) required_269)]
def childrenD_475 : Fin 4 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 1 (0, -1) envelope_261), (placedSet 0 (-2, 1) envelope_457), (placedSet 2 (-2, 1) envelope_269)]
theorem common_sub_475 : commonEnvelope childrenD_475 ⊆ insert (0, 0) required_475 := by decide
theorem child_required_sub_475 : ∀ j, childrenC_475 j ⊆ insert (0, 0) required_475 := by decide
theorem child_envelope_sub_475 : ∀ j, childrenD_475 j ⊆ envelope_475 := by decide
theorem pivot_mem_475 : (0, 0) ∈ envelope_475 := by decide
theorem children_work_475 : ∀ j, Template HasSnaky 20 (childrenC_475 j) (childrenD_475 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_261 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_457 0 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_269 2 (-2, 1)).mono (by decide)
theorem row_works_475 : Template HasSnaky 21 required_475 envelope_475 := by
  refine compose HasSnaky 20 childrenC_475 childrenD_475 children_work_475 (0, 0)
    required_475 envelope_475 pivot_mem_475 child_required_sub_475 child_envelope_sub_475 ?_
  intro b hb; exact common_sub_475 (mem_commonEnvelope childrenD_475 b hb)
def required_476 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_476 : Finset Cell := ⟨(([(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_476 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) required_0), (placedSet 0 (1, -1) required_473)]
def childrenD_476 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_0), (placedSet 0 (1, -1) envelope_473)]
theorem common_sub_476 : commonEnvelope childrenD_476 ⊆ insert (0, 0) required_476 := by decide
theorem child_required_sub_476 : ∀ j, childrenC_476 j ⊆ insert (0, 0) required_476 := by decide
theorem child_envelope_sub_476 : ∀ j, childrenD_476 j ⊆ envelope_476 := by decide
theorem pivot_mem_476 : (0, 0) ∈ envelope_476 := by decide
theorem children_work_476 : ∀ j, Template HasSnaky 20 (childrenC_476 j) (childrenD_476 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_473 0 (1, -1)).mono (by decide)
theorem row_works_476 : Template HasSnaky 21 required_476 envelope_476 := by
  refine compose HasSnaky 20 childrenC_476 childrenD_476 children_work_476 (0, 0)
    required_476 envelope_476 pivot_mem_476 child_required_sub_476 child_envelope_sub_476 ?_
  intro b hb; exact common_sub_476 (mem_commonEnvelope childrenD_476 b hb)
end SnakyConditional

end OAI
