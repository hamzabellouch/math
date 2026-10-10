import OAI.GameTheory.SnakyConditional.Templates.Level05Part04

namespace OAI

namespace SnakyConditional
def required_184 : Finset Cell := ⟨(([(0, -3), (1, -4), (1, -3), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_184 : Finset Cell := ⟨(([(-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1), (4, -1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_184 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -2) required_34), (placedSet 2 (1, 0) required_35)]
def childrenD_184 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -2) envelope_34), (placedSet 2 (1, 0) envelope_35)]
theorem common_sub_184 : commonEnvelope childrenD_184 ⊆ insert (0, 0) required_184 := by decide
theorem child_required_sub_184 : ∀ j, childrenC_184 j ⊆ insert (0, 0) required_184 := by decide
theorem child_envelope_sub_184 : ∀ j, childrenD_184 j ⊆ envelope_184 := by decide
theorem pivot_mem_184 : (0, 0) ∈ envelope_184 := by decide
theorem children_work_184 : ∀ j, Template HasSnaky 3 (childrenC_184 j) (childrenD_184 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_34 3 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_35 2 (1, 0)).mono (by decide)
theorem row_works_184 : Template HasSnaky 4 required_184 envelope_184 := by
  refine compose HasSnaky 3 childrenC_184 childrenD_184 children_work_184 (0, 0)
    required_184 envelope_184 pivot_mem_184 child_required_sub_184 child_envelope_sub_184 ?_
  intro b hb; exact common_sub_184 (mem_commonEnvelope childrenD_184 b hb)
end SnakyConditional

end OAI
