import OAI.GameTheory.SnakyConditional.Templates.Level10Part01
import OAI.GameTheory.SnakyConditional.Templates.Level10Part02
import OAI.GameTheory.SnakyConditional.Templates.Level10Part04
import OAI.GameTheory.SnakyConditional.Templates.Level10Part06
import OAI.GameTheory.SnakyConditional.Templates.Level10Part07

namespace OAI

namespace SnakyConditional
def required_373 : Finset Cell := ⟨(([(-1, -1), (0, -1), (0, 1), (2, -1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_373 : Finset Cell := ⟨(([(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_373 : Fin 5 → Finset Cell := ![(placedSet 2 (3, 0) required_156), (placedSet 4 (-1, 1) required_226), (placedSet 0 (1, 0) required_80), (placedSet 0 (1, 1) required_327), (placedSet 6 (-1, 0) required_156)]
def childrenD_373 : Fin 5 → Finset Cell := ![(placedSet 2 (3, 0) envelope_156), (placedSet 4 (-1, 1) envelope_226), (placedSet 0 (1, 0) envelope_80), (placedSet 0 (1, 1) envelope_327), (placedSet 6 (-1, 0) envelope_156)]
theorem common_sub_373 : commonEnvelope childrenD_373 ⊆ insert (0, 0) required_373 := by decide
theorem child_required_sub_373 : ∀ j, childrenC_373 j ⊆ insert (0, 0) required_373 := by decide
theorem child_envelope_sub_373 : ∀ j, childrenD_373 j ⊆ envelope_373 := by decide
theorem pivot_mem_373 : (0, 0) ∈ envelope_373 := by decide
theorem children_work_373 : ∀ j, Template HasSnaky 8 (childrenC_373 j) (childrenD_373 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_156 2 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_226 4 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_80 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_327 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_156 6 (-1, 0)).mono (by decide)
theorem row_works_373 : Template HasSnaky 9 required_373 envelope_373 := by
  refine compose HasSnaky 8 childrenC_373 childrenD_373 children_work_373 (0, 0)
    required_373 envelope_373 pivot_mem_373 child_required_sub_373 child_envelope_sub_373 ?_
  intro b hb; exact common_sub_373 (mem_commonEnvelope childrenD_373 b hb)
def required_375 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_375 : Finset Cell := ⟨(([(-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_375 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 2) required_24), (placedSet 6 (-1, -1) required_327)]
def childrenD_375 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 2) envelope_24), (placedSet 6 (-1, -1) envelope_327)]
theorem common_sub_375 : commonEnvelope childrenD_375 ⊆ insert (0, 0) required_375 := by decide
theorem child_required_sub_375 : ∀ j, childrenC_375 j ⊆ insert (0, 0) required_375 := by decide
theorem child_envelope_sub_375 : ∀ j, childrenD_375 j ⊆ envelope_375 := by decide
theorem pivot_mem_375 : (0, 0) ∈ envelope_375 := by decide
theorem children_work_375 : ∀ j, Template HasSnaky 8 (childrenC_375 j) (childrenD_375 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 3 (-1, 2)).mono (by decide)
  · exact (placed_template_map row_works_327 6 (-1, -1)).mono (by decide)
theorem row_works_375 : Template HasSnaky 9 required_375 envelope_375 := by
  refine compose HasSnaky 8 childrenC_375 childrenD_375 children_work_375 (0, 0)
    required_375 envelope_375 pivot_mem_375 child_required_sub_375 child_envelope_sub_375 ?_
  intro b hb; exact common_sub_375 (mem_commonEnvelope childrenD_375 b hb)
def required_394 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_394 : Finset Cell := ⟨(([(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_394 : Fin 6 → Finset Cell := ![(placedSet 4 (-3, 0) required_226), (placedSet 0 (1, 0) required_226), (placedSet 4 (-1, 0) required_327), (placedSet 6 (-1, -1) required_327), (placedSet 6 (-3, -1) required_226), (placedSet 2 (1, -1) required_226)]
def childrenD_394 : Fin 6 → Finset Cell := ![(placedSet 4 (-3, 0) envelope_226), (placedSet 0 (1, 0) envelope_226), (placedSet 4 (-1, 0) envelope_327), (placedSet 6 (-1, -1) envelope_327), (placedSet 6 (-3, -1) envelope_226), (placedSet 2 (1, -1) envelope_226)]
theorem common_sub_394 : commonEnvelope childrenD_394 ⊆ insert (0, 0) required_394 := by decide
theorem child_required_sub_394 : ∀ j, childrenC_394 j ⊆ insert (0, 0) required_394 := by decide
theorem child_envelope_sub_394 : ∀ j, childrenD_394 j ⊆ envelope_394 := by decide
theorem pivot_mem_394 : (0, 0) ∈ envelope_394 := by decide
theorem children_work_394 : ∀ j, Template HasSnaky 8 (childrenC_394 j) (childrenD_394 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_226 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_226 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_327 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_327 6 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_226 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_226 2 (1, -1)).mono (by decide)
theorem row_works_394 : Template HasSnaky 9 required_394 envelope_394 := by
  refine compose HasSnaky 8 childrenC_394 childrenD_394 children_work_394 (0, 0)
    required_394 envelope_394 pivot_mem_394 child_required_sub_394 child_envelope_sub_394 ?_
  intro b hb; exact common_sub_394 (mem_commonEnvelope childrenD_394 b hb)
def required_488 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_488 : Finset Cell := ⟨(([(-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_488 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) required_0), (placedSet 0 (-2, 1) required_247)]
def childrenD_488 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) envelope_0), (placedSet 0 (-2, 1) envelope_247)]
theorem common_sub_488 : commonEnvelope childrenD_488 ⊆ insert (0, 0) required_488 := by decide
theorem child_required_sub_488 : ∀ j, childrenC_488 j ⊆ insert (0, 0) required_488 := by decide
theorem child_envelope_sub_488 : ∀ j, childrenD_488 j ⊆ envelope_488 := by decide
theorem pivot_mem_488 : (0, 0) ∈ envelope_488 := by decide
theorem children_work_488 : ∀ j, Template HasSnaky 8 (childrenC_488 j) (childrenD_488 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_247 0 (-2, 1)).mono (by decide)
theorem row_works_488 : Template HasSnaky 9 required_488 envelope_488 := by
  refine compose HasSnaky 8 childrenC_488 childrenD_488 children_work_488 (0, 0)
    required_488 envelope_488 pivot_mem_488 child_required_sub_488 child_envelope_sub_488 ?_
  intro b hb; exact common_sub_488 (mem_commonEnvelope childrenD_488 b hb)
def required_489 : Finset Cell := ⟨(([(-2, -2), (-2, 0), (-1, -2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_489 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_489 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, -1) required_356), (placedSet 4 (-3, 0) required_197), (placedSet 6 (-3, 0) required_172)]
def childrenD_489 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, -1) envelope_356), (placedSet 4 (-3, 0) envelope_197), (placedSet 6 (-3, 0) envelope_172)]
theorem common_sub_489 : commonEnvelope childrenD_489 ⊆ insert (0, 0) required_489 := by decide
theorem child_required_sub_489 : ∀ j, childrenC_489 j ⊆ insert (0, 0) required_489 := by decide
theorem child_envelope_sub_489 : ∀ j, childrenD_489 j ⊆ envelope_489 := by decide
theorem pivot_mem_489 : (0, 0) ∈ envelope_489 := by decide
theorem children_work_489 : ∀ j, Template HasSnaky 8 (childrenC_489 j) (childrenD_489 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_356 1 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_197 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_172 6 (-3, 0)).mono (by decide)
theorem row_works_489 : Template HasSnaky 9 required_489 envelope_489 := by
  refine compose HasSnaky 8 childrenC_489 childrenD_489 children_work_489 (0, 0)
    required_489 envelope_489 pivot_mem_489 child_required_sub_489 child_envelope_sub_489 ?_
  intro b hb; exact common_sub_489 (mem_commonEnvelope childrenD_489 b hb)
def required_491 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_491 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_491 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) required_6), (placedSet 0 (1, 0) required_273)]
def childrenD_491 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) envelope_6), (placedSet 0 (1, 0) envelope_273)]
theorem common_sub_491 : commonEnvelope childrenD_491 ⊆ insert (0, 0) required_491 := by decide
theorem child_required_sub_491 : ∀ j, childrenC_491 j ⊆ insert (0, 0) required_491 := by decide
theorem child_envelope_sub_491 : ∀ j, childrenD_491 j ⊆ envelope_491 := by decide
theorem pivot_mem_491 : (0, 0) ∈ envelope_491 := by decide
theorem children_work_491 : ∀ j, Template HasSnaky 8 (childrenC_491 j) (childrenD_491 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_273 0 (1, 0)).mono (by decide)
theorem row_works_491 : Template HasSnaky 9 required_491 envelope_491 := by
  refine compose HasSnaky 8 childrenC_491 childrenD_491 children_work_491 (0, 0)
    required_491 envelope_491 pivot_mem_491 child_required_sub_491 child_envelope_sub_491 ?_
  intro b hb; exact common_sub_491 (mem_commonEnvelope childrenD_491 b hb)
end SnakyConditional

end OAI
