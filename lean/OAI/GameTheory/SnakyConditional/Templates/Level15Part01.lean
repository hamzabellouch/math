import OAI.GameTheory.SnakyConditional.Templates.Level14Part01

namespace OAI

namespace SnakyConditional
def required_367 : Finset Cell := ⟨(([(-3, 1), (-3, 2), (-2, 1), (-1, 1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_367 : Finset Cell := ⟨(([(-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_367 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) required_6), (placedSet 4 (0, 2) required_361)]
def childrenD_367 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) envelope_6), (placedSet 4 (0, 2) envelope_361)]
theorem common_sub_367 : commonEnvelope childrenD_367 ⊆ insert (0, 0) required_367 := by decide
theorem child_required_sub_367 : ∀ j, childrenC_367 j ⊆ insert (0, 0) required_367 := by decide
theorem child_envelope_sub_367 : ∀ j, childrenD_367 j ⊆ envelope_367 := by decide
theorem pivot_mem_367 : (0, 0) ∈ envelope_367 := by decide
theorem children_work_367 : ∀ j, Template HasSnaky 12 (childrenC_367 j) (childrenD_367 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_361 4 (0, 2)).mono (by decide)
theorem row_works_367 : Template HasSnaky 13 required_367 envelope_367 := by
  refine compose HasSnaky 12 childrenC_367 childrenD_367 children_work_367 (0, 0)
    required_367 envelope_367 pivot_mem_367 child_required_sub_367 child_envelope_sub_367 ?_
  intro b hb; exact common_sub_367 (mem_commonEnvelope childrenD_367 b hb)
def required_379 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_379 : Finset Cell := ⟨(([(-3, -3), (-2, -3), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_379 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) required_63), (placedSet 1 (-1, -3) required_64), (placedSet 3 (0, 1) required_55), (placedSet 0 (1, 0) required_368)]
def childrenD_379 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) envelope_63), (placedSet 1 (-1, -3) envelope_64), (placedSet 3 (0, 1) envelope_55), (placedSet 0 (1, 0) envelope_368)]
theorem common_sub_379 : commonEnvelope childrenD_379 ⊆ insert (0, 0) required_379 := by decide
theorem child_required_sub_379 : ∀ j, childrenC_379 j ⊆ insert (0, 0) required_379 := by decide
theorem child_envelope_sub_379 : ∀ j, childrenD_379 j ⊆ envelope_379 := by decide
theorem pivot_mem_379 : (0, 0) ∈ envelope_379 := by decide
theorem children_work_379 : ∀ j, Template HasSnaky 12 (childrenC_379 j) (childrenD_379 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_64 1 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_55 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_368 0 (1, 0)).mono (by decide)
theorem row_works_379 : Template HasSnaky 13 required_379 envelope_379 := by
  refine compose HasSnaky 12 childrenC_379 childrenD_379 children_work_379 (0, 0)
    required_379 envelope_379 pivot_mem_379 child_required_sub_379 child_envelope_sub_379 ?_
  intro b hb; exact common_sub_379 (mem_commonEnvelope childrenD_379 b hb)
def required_396 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -2), (2, -2), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_396 : Finset Cell := ⟨(([(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_396 : Fin 4 → Finset Cell := ![(placedSet 3 (0, 1) required_107), (placedSet 1 (3, -1) required_365), (placedSet 0 (0, 1) required_303), (placedSet 3 (0, 1) required_65)]
def childrenD_396 : Fin 4 → Finset Cell := ![(placedSet 3 (0, 1) envelope_107), (placedSet 1 (3, -1) envelope_365), (placedSet 0 (0, 1) envelope_303), (placedSet 3 (0, 1) envelope_65)]
theorem common_sub_396 : commonEnvelope childrenD_396 ⊆ insert (0, 0) required_396 := by decide
theorem child_required_sub_396 : ∀ j, childrenC_396 j ⊆ insert (0, 0) required_396 := by decide
theorem child_envelope_sub_396 : ∀ j, childrenD_396 j ⊆ envelope_396 := by decide
theorem pivot_mem_396 : (0, 0) ∈ envelope_396 := by decide
theorem children_work_396 : ∀ j, Template HasSnaky 12 (childrenC_396 j) (childrenD_396 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_107 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_365 1 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_303 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_65 3 (0, 1)).mono (by decide)
theorem row_works_396 : Template HasSnaky 13 required_396 envelope_396 := by
  refine compose HasSnaky 12 childrenC_396 childrenD_396 children_work_396 (0, 0)
    required_396 envelope_396 pivot_mem_396 child_required_sub_396 child_envelope_sub_396 ?_
  intro b hb; exact common_sub_396 (mem_commonEnvelope childrenD_396 b hb)
end SnakyConditional

end OAI
