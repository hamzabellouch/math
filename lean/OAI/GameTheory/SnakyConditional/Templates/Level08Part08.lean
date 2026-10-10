import OAI.GameTheory.SnakyConditional.Templates.Level07Part04
import OAI.GameTheory.SnakyConditional.Templates.Level07Part08

namespace OAI

namespace SnakyConditional
def required_293 : Finset Cell := ⟨(([(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_293 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_293 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) required_2), (placedSet 0 (1, 0) required_280)]
def childrenD_293 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) envelope_2), (placedSet 0 (1, 0) envelope_280)]
theorem common_sub_293 : commonEnvelope childrenD_293 ⊆ insert (0, 0) required_293 := by decide
theorem child_required_sub_293 : ∀ j, childrenC_293 j ⊆ insert (0, 0) required_293 := by decide
theorem child_envelope_sub_293 : ∀ j, childrenD_293 j ⊆ envelope_293 := by decide
theorem pivot_mem_293 : (0, 0) ∈ envelope_293 := by decide
theorem children_work_293 : ∀ j, Template HasSnaky 5 (childrenC_293 j) (childrenD_293 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 7 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_280 0 (1, 0)).mono (by decide)
theorem row_works_293 : Template HasSnaky 6 required_293 envelope_293 := by
  refine compose HasSnaky 5 childrenC_293 childrenD_293 children_work_293 (0, 0)
    required_293 envelope_293 pivot_mem_293 child_required_sub_293 child_envelope_sub_293 ?_
  intro b hb; exact common_sub_293 (mem_commonEnvelope childrenD_293 b hb)
def required_429 : Finset Cell := ⟨(([(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_429 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_429 : Fin 2 → Finset Cell := ![(placedSet 0 (2, -1) required_128), (placedSet 3 (0, 1) required_28)]
def childrenD_429 : Fin 2 → Finset Cell := ![(placedSet 0 (2, -1) envelope_128), (placedSet 3 (0, 1) envelope_28)]
theorem common_sub_429 : commonEnvelope childrenD_429 ⊆ insert (0, 0) required_429 := by decide
theorem child_required_sub_429 : ∀ j, childrenC_429 j ⊆ insert (0, 0) required_429 := by decide
theorem child_envelope_sub_429 : ∀ j, childrenD_429 j ⊆ envelope_429 := by decide
theorem pivot_mem_429 : (0, 0) ∈ envelope_429 := by decide
theorem children_work_429 : ∀ j, Template HasSnaky 5 (childrenC_429 j) (childrenD_429 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_128 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_28 3 (0, 1)).mono (by decide)
theorem row_works_429 : Template HasSnaky 6 required_429 envelope_429 := by
  refine compose HasSnaky 5 childrenC_429 childrenD_429 children_work_429 (0, 0)
    required_429 envelope_429 pivot_mem_429 child_required_sub_429 child_envelope_sub_429 ?_
  intro b hb; exact common_sub_429 (mem_commonEnvelope childrenD_429 b hb)
end SnakyConditional

end OAI
