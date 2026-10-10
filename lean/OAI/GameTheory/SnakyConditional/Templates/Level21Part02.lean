import OAI.GameTheory.SnakyConditional.Templates.Level20Part01

namespace OAI

namespace SnakyConditional
def required_447 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_447 : Finset Cell := ⟨(([(-6, 1), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_447 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) required_0), (placedSet 4 (0, 2) required_436)]
def childrenD_447 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) envelope_0), (placedSet 4 (0, 2) envelope_436)]
theorem common_sub_447 : commonEnvelope childrenD_447 ⊆ insert (0, 0) required_447 := by decide
theorem child_required_sub_447 : ∀ j, childrenC_447 j ⊆ insert (0, 0) required_447 := by decide
theorem child_envelope_sub_447 : ∀ j, childrenD_447 j ⊆ envelope_447 := by decide
theorem pivot_mem_447 : (0, 0) ∈ envelope_447 := by decide
theorem children_work_447 : ∀ j, Template HasSnaky 18 (childrenC_447 j) (childrenD_447 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_436 4 (0, 2)).mono (by decide)
theorem row_works_447 : Template HasSnaky 19 required_447 envelope_447 := by
  refine compose HasSnaky 18 childrenC_447 childrenD_447 children_work_447 (0, 0)
    required_447 envelope_447 pivot_mem_447 child_required_sub_447 child_envelope_sub_447 ?_
  intro b hb; exact common_sub_447 (mem_commonEnvelope childrenD_447 b hb)
def required_448 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_448 : Finset Cell := ⟨(([(-5, 1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_448 : Fin 2 → Finset Cell := ![(placedSet 4 (-3, -1) required_9), (placedSet 0 (-1, 2) required_436)]
def childrenD_448 : Fin 2 → Finset Cell := ![(placedSet 4 (-3, -1) envelope_9), (placedSet 0 (-1, 2) envelope_436)]
theorem common_sub_448 : commonEnvelope childrenD_448 ⊆ insert (0, 0) required_448 := by decide
theorem child_required_sub_448 : ∀ j, childrenC_448 j ⊆ insert (0, 0) required_448 := by decide
theorem child_envelope_sub_448 : ∀ j, childrenD_448 j ⊆ envelope_448 := by decide
theorem pivot_mem_448 : (0, 0) ∈ envelope_448 := by decide
theorem children_work_448 : ∀ j, Template HasSnaky 18 (childrenC_448 j) (childrenD_448 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_9 4 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_436 0 (-1, 2)).mono (by decide)
theorem row_works_448 : Template HasSnaky 19 required_448 envelope_448 := by
  refine compose HasSnaky 18 childrenC_448 childrenD_448 children_work_448 (0, 0)
    required_448 envelope_448 pivot_mem_448 child_required_sub_448 child_envelope_sub_448 ?_
  intro b hb; exact common_sub_448 (mem_commonEnvelope childrenD_448 b hb)
end SnakyConditional

end OAI
