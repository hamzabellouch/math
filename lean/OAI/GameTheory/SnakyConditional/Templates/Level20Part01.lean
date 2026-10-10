import OAI.GameTheory.SnakyConditional.Templates.Level19Part01

namespace OAI

namespace SnakyConditional
def required_432 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (1, -3), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_432 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_432 : Fin 3 → Finset Cell := ![(placedSet 3 (0, -1) required_42), (placedSet 0 (1, 0) required_428), (placedSet 0 (0, -1) required_274)]
def childrenD_432 : Fin 3 → Finset Cell := ![(placedSet 3 (0, -1) envelope_42), (placedSet 0 (1, 0) envelope_428), (placedSet 0 (0, -1) envelope_274)]
theorem common_sub_432 : commonEnvelope childrenD_432 ⊆ insert (0, 0) required_432 := by decide
theorem child_required_sub_432 : ∀ j, childrenC_432 j ⊆ insert (0, 0) required_432 := by decide
theorem child_envelope_sub_432 : ∀ j, childrenD_432 j ⊆ envelope_432 := by decide
theorem pivot_mem_432 : (0, 0) ∈ envelope_432 := by decide
theorem children_work_432 : ∀ j, Template HasSnaky 17 (childrenC_432 j) (childrenD_432 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_42 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_428 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_274 0 (0, -1)).mono (by decide)
theorem row_works_432 : Template HasSnaky 18 required_432 envelope_432 := by
  refine compose HasSnaky 17 childrenC_432 childrenD_432 children_work_432 (0, 0)
    required_432 envelope_432 pivot_mem_432 child_required_sub_432 child_envelope_sub_432 ?_
  intro b hb; exact common_sub_432 (mem_commonEnvelope childrenD_432 b hb)
def required_436 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, -3), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_436 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_436 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) required_51), (placedSet 3 (0, -1) required_60), (placedSet 4 (0, -1) required_274), (placedSet 0 (1, 0) required_428)]
def childrenD_436 : Fin 4 → Finset Cell := ![(placedSet 1 (1, 0) envelope_51), (placedSet 3 (0, -1) envelope_60), (placedSet 4 (0, -1) envelope_274), (placedSet 0 (1, 0) envelope_428)]
theorem common_sub_436 : commonEnvelope childrenD_436 ⊆ insert (0, 0) required_436 := by decide
theorem child_required_sub_436 : ∀ j, childrenC_436 j ⊆ insert (0, 0) required_436 := by decide
theorem child_envelope_sub_436 : ∀ j, childrenD_436 j ⊆ envelope_436 := by decide
theorem pivot_mem_436 : (0, 0) ∈ envelope_436 := by decide
theorem children_work_436 : ∀ j, Template HasSnaky 17 (childrenC_436 j) (childrenD_436 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_51 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_60 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_274 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_428 0 (1, 0)).mono (by decide)
theorem row_works_436 : Template HasSnaky 18 required_436 envelope_436 := by
  refine compose HasSnaky 17 childrenC_436 childrenD_436 children_work_436 (0, 0)
    required_436 envelope_436 pivot_mem_436 child_required_sub_436 child_envelope_sub_436 ?_
  intro b hb; exact common_sub_436 (mem_commonEnvelope childrenD_436 b hb)
end SnakyConditional

end OAI
