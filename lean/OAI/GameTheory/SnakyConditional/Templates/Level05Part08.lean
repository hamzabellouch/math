import OAI.GameTheory.SnakyConditional.Templates.Level04Part01
import OAI.GameTheory.SnakyConditional.Templates.Level04Part02
import OAI.GameTheory.SnakyConditional.Templates.Level04Part06

namespace OAI

namespace SnakyConditional
def required_77 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_77 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_77 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) required_0), (placedSet 0 (1, 0) required_12)]
def childrenD_77 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) envelope_0), (placedSet 0 (1, 0) envelope_12)]
theorem common_sub_77 : commonEnvelope childrenD_77 ⊆ insert (0, 0) required_77 := by decide
theorem child_required_sub_77 : ∀ j, childrenC_77 j ⊆ insert (0, 0) required_77 := by decide
theorem child_envelope_sub_77 : ∀ j, childrenD_77 j ⊆ envelope_77 := by decide
theorem pivot_mem_77 : (0, 0) ∈ envelope_77 := by decide
theorem children_work_77 : ∀ j, Template HasSnaky 2 (childrenC_77 j) (childrenD_77 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_12 0 (1, 0)).mono (by decide)
theorem row_works_77 : Template HasSnaky 3 required_77 envelope_77 := by
  refine compose HasSnaky 2 childrenC_77 childrenD_77 children_work_77 (0, 0)
    required_77 envelope_77 pivot_mem_77 child_required_sub_77 child_envelope_sub_77 ?_
  intro b hb; exact common_sub_77 (mem_commonEnvelope childrenD_77 b hb)
def required_78 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_78 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_78 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (1, 0) required_52)]
def childrenD_78 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (1, 0) envelope_52)]
theorem common_sub_78 : commonEnvelope childrenD_78 ⊆ insert (0, 0) required_78 := by decide
theorem child_required_sub_78 : ∀ j, childrenC_78 j ⊆ insert (0, 0) required_78 := by decide
theorem child_envelope_sub_78 : ∀ j, childrenD_78 j ⊆ envelope_78 := by decide
theorem pivot_mem_78 : (0, 0) ∈ envelope_78 := by decide
theorem children_work_78 : ∀ j, Template HasSnaky 2 (childrenC_78 j) (childrenD_78 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_52 0 (1, 0)).mono (by decide)
theorem row_works_78 : Template HasSnaky 3 required_78 envelope_78 := by
  refine compose HasSnaky 2 childrenC_78 childrenD_78 children_work_78 (0, 0)
    required_78 envelope_78 pivot_mem_78 child_required_sub_78 child_envelope_sub_78 ?_
  intro b hb; exact common_sub_78 (mem_commonEnvelope childrenD_78 b hb)
end SnakyConditional

end OAI
