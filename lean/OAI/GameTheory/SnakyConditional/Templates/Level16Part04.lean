import OAI.GameTheory.SnakyConditional.Templates.Level15Part03
import OAI.GameTheory.SnakyConditional.Templates.Level15Part04
import OAI.GameTheory.SnakyConditional.Templates.Level15Part05

namespace OAI

namespace SnakyConditional
def required_486 : Finset Cell := ⟨(([(0, -3), (0, -1), (1, -4), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_486 : Finset Cell := ⟨(([(-3, 0), (-2, -2), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_486 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -2) required_2), (placedSet 0 (1, -1) required_485)]
def childrenD_486 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -2) envelope_2), (placedSet 0 (1, -1) envelope_485)]
theorem common_sub_486 : commonEnvelope childrenD_486 ⊆ insert (0, 0) required_486 := by decide
theorem child_required_sub_486 : ∀ j, childrenC_486 j ⊆ insert (0, 0) required_486 := by decide
theorem child_envelope_sub_486 : ∀ j, childrenD_486 j ⊆ envelope_486 := by decide
theorem pivot_mem_486 : (0, 0) ∈ envelope_486 := by decide
theorem children_work_486 : ∀ j, Template HasSnaky 13 (childrenC_486 j) (childrenD_486 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 5 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_485 0 (1, -1)).mono (by decide)
theorem row_works_486 : Template HasSnaky 14 required_486 envelope_486 := by
  refine compose HasSnaky 13 childrenC_486 childrenD_486 children_work_486 (0, 0)
    required_486 envelope_486 pivot_mem_486 child_required_sub_486 child_envelope_sub_486 ?_
  intro b hb; exact common_sub_486 (mem_commonEnvelope childrenD_486 b hb)
def required_503 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_503 : Finset Cell := ⟨(([(-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_503 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) required_63), (placedSet 7 (0, -4) required_55), (placedSet 1 (3, -2) required_420), (placedSet 1 (3, 0) required_419)]
def childrenD_503 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) envelope_63), (placedSet 7 (0, -4) envelope_55), (placedSet 1 (3, -2) envelope_420), (placedSet 1 (3, 0) envelope_419)]
theorem common_sub_503 : commonEnvelope childrenD_503 ⊆ insert (0, 0) required_503 := by decide
theorem child_required_sub_503 : ∀ j, childrenC_503 j ⊆ insert (0, 0) required_503 := by decide
theorem child_envelope_sub_503 : ∀ j, childrenD_503 j ⊆ envelope_503 := by decide
theorem pivot_mem_503 : (0, 0) ∈ envelope_503 := by decide
theorem children_work_503 : ∀ j, Template HasSnaky 13 (childrenC_503 j) (childrenD_503 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 7 (0, -4)).mono (by decide)
  · exact (placed_template_map row_works_420 1 (3, -2)).mono (by decide)
  · exact (placed_template_map row_works_419 1 (3, 0)).mono (by decide)
theorem row_works_503 : Template HasSnaky 14 required_503 envelope_503 := by
  refine compose HasSnaky 13 childrenC_503 childrenD_503 children_work_503 (0, 0)
    required_503 envelope_503 pivot_mem_503 child_required_sub_503 child_envelope_sub_503 ?_
  intro b hb; exact common_sub_503 (mem_commonEnvelope childrenD_503 b hb)
def required_510 : Finset Cell := ⟨(([(0, -1), (1, -1), (2, -2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_510 : Finset Cell := ⟨(([(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_510 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (3, 0) required_508)]
def childrenD_510 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (3, 0) envelope_508)]
theorem common_sub_510 : commonEnvelope childrenD_510 ⊆ insert (0, 0) required_510 := by decide
theorem child_required_sub_510 : ∀ j, childrenC_510 j ⊆ insert (0, 0) required_510 := by decide
theorem child_envelope_sub_510 : ∀ j, childrenD_510 j ⊆ envelope_510 := by decide
theorem pivot_mem_510 : (0, 0) ∈ envelope_510 := by decide
theorem children_work_510 : ∀ j, Template HasSnaky 13 (childrenC_510 j) (childrenD_510 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_508 0 (3, 0)).mono (by decide)
theorem row_works_510 : Template HasSnaky 14 required_510 envelope_510 := by
  refine compose HasSnaky 13 childrenC_510 childrenD_510 children_work_510 (0, 0)
    required_510 envelope_510 pivot_mem_510 child_required_sub_510 child_envelope_sub_510 ?_
  intro b hb; exact common_sub_510 (mem_commonEnvelope childrenD_510 b hb)
end SnakyConditional

end OAI
