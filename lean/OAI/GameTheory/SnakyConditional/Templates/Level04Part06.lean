import OAI.GameTheory.SnakyConditional.Templates.Level03Part01

namespace OAI

namespace SnakyConditional
def required_52 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_52 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_52 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) required_0), (placedSet 4 (3, -1) required_0)]
def childrenD_52 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) envelope_0), (placedSet 4 (3, -1) envelope_0)]
theorem common_sub_52 : commonEnvelope childrenD_52 ⊆ insert (0, 0) required_52 := by decide
theorem child_required_sub_52 : ∀ j, childrenC_52 j ⊆ insert (0, 0) required_52 := by decide
theorem child_envelope_sub_52 : ∀ j, childrenD_52 j ⊆ envelope_52 := by decide
theorem pivot_mem_52 : (0, 0) ∈ envelope_52 := by decide
theorem children_work_52 : ∀ j, Template HasSnaky 1 (childrenC_52 j) (childrenD_52 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_0 4 (3, -1)).mono (by decide)
theorem row_works_52 : Template HasSnaky 2 required_52 envelope_52 := by
  refine compose HasSnaky 1 childrenC_52 childrenD_52 children_work_52 (0, 0)
    required_52 envelope_52 pivot_mem_52 child_required_sub_52 child_envelope_sub_52 ?_
  intro b hb; exact common_sub_52 (mem_commonEnvelope childrenD_52 b hb)
end SnakyConditional

end OAI
