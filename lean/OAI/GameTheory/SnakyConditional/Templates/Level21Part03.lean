import OAI.GameTheory.SnakyConditional.Templates.Level20Part01
import OAI.GameTheory.SnakyConditional.Templates.Level20Part02

namespace OAI

namespace SnakyConditional
def required_454 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_454 : Finset Cell := ⟨(([(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_454 : Fin 2 → Finset Cell := ![(placedSet 0 (2, -1) required_58), (placedSet 0 (-1, 2) required_436)]
def childrenD_454 : Fin 2 → Finset Cell := ![(placedSet 0 (2, -1) envelope_58), (placedSet 0 (-1, 2) envelope_436)]
theorem common_sub_454 : commonEnvelope childrenD_454 ⊆ insert (0, 0) required_454 := by decide
theorem child_required_sub_454 : ∀ j, childrenC_454 j ⊆ insert (0, 0) required_454 := by decide
theorem child_envelope_sub_454 : ∀ j, childrenD_454 j ⊆ envelope_454 := by decide
theorem pivot_mem_454 : (0, 0) ∈ envelope_454 := by decide
theorem children_work_454 : ∀ j, Template HasSnaky 18 (childrenC_454 j) (childrenD_454 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_58 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_436 0 (-1, 2)).mono (by decide)
theorem row_works_454 : Template HasSnaky 19 required_454 envelope_454 := by
  refine compose HasSnaky 18 childrenC_454 childrenD_454 children_work_454 (0, 0)
    required_454 envelope_454 pivot_mem_454 child_required_sub_454 child_envelope_sub_454 ?_
  intro b hb; exact common_sub_454 (mem_commonEnvelope childrenD_454 b hb)
def required_462 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_462 : Finset Cell := ⟨(([(-5, 3), (-5, 5), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_462 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, -2) required_452), (placedSet 0 (1, 0) required_86), (placedSet 1 (1, 0) required_328)]
def childrenD_462 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, -2) envelope_452), (placedSet 0 (1, 0) envelope_86), (placedSet 1 (1, 0) envelope_328)]
theorem common_sub_462 : commonEnvelope childrenD_462 ⊆ insert (0, 0) required_462 := by decide
theorem child_required_sub_462 : ∀ j, childrenC_462 j ⊆ insert (0, 0) required_462 := by decide
theorem child_envelope_sub_462 : ∀ j, childrenD_462 j ⊆ envelope_462 := by decide
theorem pivot_mem_462 : (0, 0) ∈ envelope_462 := by decide
theorem children_work_462 : ∀ j, Template HasSnaky 18 (childrenC_462 j) (childrenD_462 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_452 0 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_86 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_328 1 (1, 0)).mono (by decide)
theorem row_works_462 : Template HasSnaky 19 required_462 envelope_462 := by
  refine compose HasSnaky 18 childrenC_462 childrenD_462 children_work_462 (0, 0)
    required_462 envelope_462 pivot_mem_462 child_required_sub_462 child_envelope_sub_462 ?_
  intro b hb; exact common_sub_462 (mem_commonEnvelope childrenD_462 b hb)
end SnakyConditional

end OAI
