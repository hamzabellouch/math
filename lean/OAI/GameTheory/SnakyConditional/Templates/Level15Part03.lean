import OAI.GameTheory.SnakyConditional.Templates.Level14Part02
import OAI.GameTheory.SnakyConditional.Templates.Level14Part03
import OAI.GameTheory.SnakyConditional.Templates.Level14Part04

namespace OAI

namespace SnakyConditional
def required_417 : Finset Cell := ⟨(([(-2, -3), (-2, -2), (-1, -3), (0, -3), (0, -1), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_417 : Finset Cell := ⟨(([(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_417 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 0) required_409), (placedSet 1 (0, -2) required_11), (placedSet 4 (0, -2) required_270)]
def childrenD_417 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, 0) envelope_409), (placedSet 1 (0, -2) envelope_11), (placedSet 4 (0, -2) envelope_270)]
theorem common_sub_417 : commonEnvelope childrenD_417 ⊆ insert (0, 0) required_417 := by decide
theorem child_required_sub_417 : ∀ j, childrenC_417 j ⊆ insert (0, 0) required_417 := by decide
theorem child_envelope_sub_417 : ∀ j, childrenD_417 j ⊆ envelope_417 := by decide
theorem pivot_mem_417 : (0, 0) ∈ envelope_417 := by decide
theorem children_work_417 : ∀ j, Template HasSnaky 12 (childrenC_417 j) (childrenD_417 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_409 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_11 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_270 4 (0, -2)).mono (by decide)
theorem row_works_417 : Template HasSnaky 13 required_417 envelope_417 := by
  refine compose HasSnaky 12 childrenC_417 childrenD_417 children_work_417 (0, 0)
    required_417 envelope_417 pivot_mem_417 child_required_sub_417 child_envelope_sub_417 ?_
  intro b hb; exact common_sub_417 (mem_commonEnvelope childrenD_417 b hb)
def required_419 : Finset Cell := ⟨(([(-3, -3), (-2, -3), (-2, -2), (-1, -3), (0, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_419 : Finset Cell := ⟨(([(-5, 1), (-4, -4), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_419 : Fin 5 → Finset Cell := ![(placedSet 0 (0, -2) required_243), (placedSet 1 (0, -2) required_164), (placedSet 0 (-2, 0) required_402), (placedSet 0 (-2, 0) required_253), (placedSet 0 (-2, 0) required_377)]
def childrenD_419 : Fin 5 → Finset Cell := ![(placedSet 0 (0, -2) envelope_243), (placedSet 1 (0, -2) envelope_164), (placedSet 0 (-2, 0) envelope_402), (placedSet 0 (-2, 0) envelope_253), (placedSet 0 (-2, 0) envelope_377)]
theorem common_sub_419 : commonEnvelope childrenD_419 ⊆ insert (0, 0) required_419 := by decide
theorem child_required_sub_419 : ∀ j, childrenC_419 j ⊆ insert (0, 0) required_419 := by decide
theorem child_envelope_sub_419 : ∀ j, childrenD_419 j ⊆ envelope_419 := by decide
theorem pivot_mem_419 : (0, 0) ∈ envelope_419 := by decide
theorem children_work_419 : ∀ j, Template HasSnaky 12 (childrenC_419 j) (childrenD_419 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_243 0 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_164 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_402 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_253 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_377 0 (-2, 0)).mono (by decide)
theorem row_works_419 : Template HasSnaky 13 required_419 envelope_419 := by
  refine compose HasSnaky 12 childrenC_419 childrenD_419 children_work_419 (0, 0)
    required_419 envelope_419 pivot_mem_419 child_required_sub_419 child_envelope_sub_419 ?_
  intro b hb; exact common_sub_419 (mem_commonEnvelope childrenD_419 b hb)
def required_420 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_420 : Finset Cell := ⟨(([(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_420 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) required_29), (placedSet 0 (2, 0) required_415)]
def childrenD_420 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) envelope_29), (placedSet 0 (2, 0) envelope_415)]
theorem common_sub_420 : commonEnvelope childrenD_420 ⊆ insert (0, 0) required_420 := by decide
theorem child_required_sub_420 : ∀ j, childrenC_420 j ⊆ insert (0, 0) required_420 := by decide
theorem child_envelope_sub_420 : ∀ j, childrenD_420 j ⊆ envelope_420 := by decide
theorem pivot_mem_420 : (0, 0) ∈ envelope_420 := by decide
theorem children_work_420 : ∀ j, Template HasSnaky 12 (childrenC_420 j) (childrenD_420 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_29 3 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_415 0 (2, 0)).mono (by decide)
theorem row_works_420 : Template HasSnaky 13 required_420 envelope_420 := by
  refine compose HasSnaky 12 childrenC_420 childrenD_420 children_work_420 (0, 0)
    required_420 envelope_420 pivot_mem_420 child_required_sub_420 child_envelope_sub_420 ?_
  intro b hb; exact common_sub_420 (mem_commonEnvelope childrenD_420 b hb)
end SnakyConditional

end OAI
