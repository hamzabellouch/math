import OAI.GameTheory.SnakyConditional.Templates.Level14Part02
import OAI.GameTheory.SnakyConditional.Templates.Level14Part03

namespace OAI

namespace SnakyConditional
def required_405 : Finset Cell := ⟨(([(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_405 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_405 : Fin 3 → Finset Cell := ![(placedSet 0 (0, -1) required_391), (placedSet 0 (1, -2) required_301), (placedSet 1 (0, -1) required_42)]
def childrenD_405 : Fin 3 → Finset Cell := ![(placedSet 0 (0, -1) envelope_391), (placedSet 0 (1, -2) envelope_301), (placedSet 1 (0, -1) envelope_42)]
theorem common_sub_405 : commonEnvelope childrenD_405 ⊆ insert (0, 0) required_405 := by decide
theorem child_required_sub_405 : ∀ j, childrenC_405 j ⊆ insert (0, 0) required_405 := by decide
theorem child_envelope_sub_405 : ∀ j, childrenD_405 j ⊆ envelope_405 := by decide
theorem pivot_mem_405 : (0, 0) ∈ envelope_405 := by decide
theorem children_work_405 : ∀ j, Template HasSnaky 12 (childrenC_405 j) (childrenD_405 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_391 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_301 0 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_42 1 (0, -1)).mono (by decide)
theorem row_works_405 : Template HasSnaky 13 required_405 envelope_405 := by
  refine compose HasSnaky 12 childrenC_405 childrenD_405 children_work_405 (0, 0)
    required_405 envelope_405 pivot_mem_405 child_required_sub_405 child_envelope_sub_405 ?_
  intro b hb; exact common_sub_405 (mem_commonEnvelope childrenD_405 b hb)
def required_412 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_412 : Finset Cell := ⟨(([(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_412 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) required_0), (placedSet 4 (-1, 2) required_403)]
def childrenD_412 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) envelope_0), (placedSet 4 (-1, 2) envelope_403)]
theorem common_sub_412 : commonEnvelope childrenD_412 ⊆ insert (0, 0) required_412 := by decide
theorem child_required_sub_412 : ∀ j, childrenC_412 j ⊆ insert (0, 0) required_412 := by decide
theorem child_envelope_sub_412 : ∀ j, childrenD_412 j ⊆ envelope_412 := by decide
theorem pivot_mem_412 : (0, 0) ∈ envelope_412 := by decide
theorem children_work_412 : ∀ j, Template HasSnaky 12 (childrenC_412 j) (childrenD_412 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_403 4 (-1, 2)).mono (by decide)
theorem row_works_412 : Template HasSnaky 13 required_412 envelope_412 := by
  refine compose HasSnaky 12 childrenC_412 childrenD_412 children_work_412 (0, 0)
    required_412 envelope_412 pivot_mem_412 child_required_sub_412 child_envelope_sub_412 ?_
  intro b hb; exact common_sub_412 (mem_commonEnvelope childrenD_412 b hb)
def required_413 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 1), (0, 1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_413 : Finset Cell := ⟨(([(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_413 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) required_3), (placedSet 0 (0, 3) required_403)]
def childrenD_413 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) envelope_3), (placedSet 0 (0, 3) envelope_403)]
theorem common_sub_413 : commonEnvelope childrenD_413 ⊆ insert (0, 0) required_413 := by decide
theorem child_required_sub_413 : ∀ j, childrenC_413 j ⊆ insert (0, 0) required_413 := by decide
theorem child_envelope_sub_413 : ∀ j, childrenD_413 j ⊆ envelope_413 := by decide
theorem pivot_mem_413 : (0, 0) ∈ envelope_413 := by decide
theorem children_work_413 : ∀ j, Template HasSnaky 12 (childrenC_413 j) (childrenD_413 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_3 7 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_403 0 (0, 3)).mono (by decide)
theorem row_works_413 : Template HasSnaky 13 required_413 envelope_413 := by
  refine compose HasSnaky 12 childrenC_413 childrenD_413 children_work_413 (0, 0)
    required_413 envelope_413 pivot_mem_413 child_required_sub_413 child_envelope_sub_413 ?_
  intro b hb; exact common_sub_413 (mem_commonEnvelope childrenD_413 b hb)
end SnakyConditional

end OAI
