import OAI.GameTheory.SnakyConditional.Templates.Level17Part03

namespace OAI

namespace SnakyConditional
def required_450 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_450 : Finset Cell := ⟨(([(-2, 4), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_450 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) required_6), (placedSet 0 (2, 0) required_440)]
def childrenD_450 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) envelope_6), (placedSet 0 (2, 0) envelope_440)]
theorem common_sub_450 : commonEnvelope childrenD_450 ⊆ insert (0, 0) required_450 := by decide
theorem child_required_sub_450 : ∀ j, childrenC_450 j ⊆ insert (0, 0) required_450 := by decide
theorem child_envelope_sub_450 : ∀ j, childrenD_450 j ⊆ envelope_450 := by decide
theorem pivot_mem_450 : (0, 0) ∈ envelope_450 := by decide
theorem children_work_450 : ∀ j, Template HasSnaky 15 (childrenC_450 j) (childrenD_450 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_440 0 (2, 0)).mono (by decide)
theorem row_works_450 : Template HasSnaky 16 required_450 envelope_450 := by
  refine compose HasSnaky 15 childrenC_450 childrenD_450 children_work_450 (0, 0)
    required_450 envelope_450 pivot_mem_450 child_required_sub_450 child_envelope_sub_450 ?_
  intro b hb; exact common_sub_450 (mem_commonEnvelope childrenD_450 b hb)
end SnakyConditional

end OAI
