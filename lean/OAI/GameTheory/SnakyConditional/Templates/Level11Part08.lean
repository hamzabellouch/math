import OAI.GameTheory.SnakyConditional.Templates.Level10Part05
import OAI.GameTheory.SnakyConditional.Templates.Level10Part06
import OAI.GameTheory.SnakyConditional.Templates.Level10Part07

namespace OAI

namespace SnakyConditional
def required_498 : Finset Cell := ⟨(([(-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_498 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_498 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 2) required_14), (placedSet 2 (-2, 0) required_298)]
def childrenD_498 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 2) envelope_14), (placedSet 2 (-2, 0) envelope_298)]
theorem common_sub_498 : commonEnvelope childrenD_498 ⊆ insert (0, 0) required_498 := by decide
theorem child_required_sub_498 : ∀ j, childrenC_498 j ⊆ insert (0, 0) required_498 := by decide
theorem child_envelope_sub_498 : ∀ j, childrenD_498 j ⊆ envelope_498 := by decide
theorem pivot_mem_498 : (0, 0) ∈ envelope_498 := by decide
theorem children_work_498 : ∀ j, Template HasSnaky 8 (childrenC_498 j) (childrenD_498 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_14 1 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_298 2 (-2, 0)).mono (by decide)
theorem row_works_498 : Template HasSnaky 9 required_498 envelope_498 := by
  refine compose HasSnaky 8 childrenC_498 childrenD_498 children_work_498 (0, 0)
    required_498 envelope_498 pivot_mem_498 child_required_sub_498 child_envelope_sub_498 ?_
  intro b hb; exact common_sub_498 (mem_commonEnvelope childrenD_498 b hb)
def required_499 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_499 : Finset Cell := ⟨(([(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_499 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_493), (placedSet 1 (0, 1) required_25), (placedSet 0 (-2, 0) required_478)]
def childrenD_499 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_493), (placedSet 1 (0, 1) envelope_25), (placedSet 0 (-2, 0) envelope_478)]
theorem common_sub_499 : commonEnvelope childrenD_499 ⊆ insert (0, 0) required_499 := by decide
theorem child_required_sub_499 : ∀ j, childrenC_499 j ⊆ insert (0, 0) required_499 := by decide
theorem child_envelope_sub_499 : ∀ j, childrenD_499 j ⊆ envelope_499 := by decide
theorem pivot_mem_499 : (0, 0) ∈ envelope_499 := by decide
theorem children_work_499 : ∀ j, Template HasSnaky 8 (childrenC_499 j) (childrenD_499 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_493 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_25 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_478 0 (-2, 0)).mono (by decide)
theorem row_works_499 : Template HasSnaky 9 required_499 envelope_499 := by
  refine compose HasSnaky 8 childrenC_499 childrenD_499 children_work_499 (0, 0)
    required_499 envelope_499 pivot_mem_499 child_required_sub_499 child_envelope_sub_499 ?_
  intro b hb; exact common_sub_499 (mem_commonEnvelope childrenD_499 b hb)
def required_522 : Finset Cell := ⟨(([(-2, -1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_522 : Finset Cell := ⟨(([(-5, -2), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 2), (3, -2), (3, -1), (3, 0), (3, 2), (4, -2), (4, -1), (4, 0), (5, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_522 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 2) required_176), (placedSet 2 (-1, -1) required_338), (placedSet 1 (0, 2) required_252)]
def childrenD_522 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 2) envelope_176), (placedSet 2 (-1, -1) envelope_338), (placedSet 1 (0, 2) envelope_252)]
theorem common_sub_522 : commonEnvelope childrenD_522 ⊆ insert (0, 0) required_522 := by decide
theorem child_required_sub_522 : ∀ j, childrenC_522 j ⊆ insert (0, 0) required_522 := by decide
theorem child_envelope_sub_522 : ∀ j, childrenD_522 j ⊆ envelope_522 := by decide
theorem pivot_mem_522 : (0, 0) ∈ envelope_522 := by decide
theorem children_work_522 : ∀ j, Template HasSnaky 8 (childrenC_522 j) (childrenD_522 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_176 3 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_338 2 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_252 1 (0, 2)).mono (by decide)
theorem row_works_522 : Template HasSnaky 9 required_522 envelope_522 := by
  refine compose HasSnaky 8 childrenC_522 childrenD_522 children_work_522 (0, 0)
    required_522 envelope_522 pivot_mem_522 child_required_sub_522 child_envelope_sub_522 ?_
  intro b hb; exact common_sub_522 (mem_commonEnvelope childrenD_522 b hb)
end SnakyConditional

end OAI
