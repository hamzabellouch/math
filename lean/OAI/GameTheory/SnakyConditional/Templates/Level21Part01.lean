import OAI.GameTheory.SnakyConditional.Templates.Level20Part01

namespace OAI

namespace SnakyConditional
def required_438 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_438 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_438 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) required_0), (placedSet 0 (0, 2) required_432)]
def childrenD_438 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_0), (placedSet 0 (0, 2) envelope_432)]
theorem common_sub_438 : commonEnvelope childrenD_438 ⊆ insert (0, 0) required_438 := by decide
theorem child_required_sub_438 : ∀ j, childrenC_438 j ⊆ insert (0, 0) required_438 := by decide
theorem child_envelope_sub_438 : ∀ j, childrenD_438 j ⊆ envelope_438 := by decide
theorem pivot_mem_438 : (0, 0) ∈ envelope_438 := by decide
theorem children_work_438 : ∀ j, Template HasSnaky 18 (childrenC_438 j) (childrenD_438 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_432 0 (0, 2)).mono (by decide)
theorem row_works_438 : Template HasSnaky 19 required_438 envelope_438 := by
  refine compose HasSnaky 18 childrenC_438 childrenD_438 children_work_438 (0, 0)
    required_438 envelope_438 pivot_mem_438 child_required_sub_438 child_envelope_sub_438 ?_
  intro b hb; exact common_sub_438 (mem_commonEnvelope childrenD_438 b hb)
def required_445 : Finset Cell := ⟨(([(1, 0), (1, 1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_445 : Finset Cell := ⟨(([(-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_445 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_9), (placedSet 0 (1, 3) required_432)]
def childrenD_445 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_9), (placedSet 0 (1, 3) envelope_432)]
theorem common_sub_445 : commonEnvelope childrenD_445 ⊆ insert (0, 0) required_445 := by decide
theorem child_required_sub_445 : ∀ j, childrenC_445 j ⊆ insert (0, 0) required_445 := by decide
theorem child_envelope_sub_445 : ∀ j, childrenD_445 j ⊆ envelope_445 := by decide
theorem pivot_mem_445 : (0, 0) ∈ envelope_445 := by decide
theorem children_work_445 : ∀ j, Template HasSnaky 18 (childrenC_445 j) (childrenD_445 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_9 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_432 0 (1, 3)).mono (by decide)
theorem row_works_445 : Template HasSnaky 19 required_445 envelope_445 := by
  refine compose HasSnaky 18 childrenC_445 childrenD_445 children_work_445 (0, 0)
    required_445 envelope_445 pivot_mem_445 child_required_sub_445 child_envelope_sub_445 ?_
  intro b hb; exact common_sub_445 (mem_commonEnvelope childrenD_445 b hb)
end SnakyConditional

end OAI
