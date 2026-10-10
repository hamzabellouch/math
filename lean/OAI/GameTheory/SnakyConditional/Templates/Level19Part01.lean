import OAI.GameTheory.SnakyConditional.Templates.Level18Part01
import OAI.GameTheory.SnakyConditional.Templates.Level18Part03

namespace OAI

namespace SnakyConditional
def required_428 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_428 : Finset Cell := ⟨(([(-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_428 : Fin 4 → Finset Cell := ![(placedSet 3 (0, -1) required_26), (placedSet 0 (1, 0) required_416), (placedSet 0 (1, 0) required_244), (placedSet 0 (0, -1) required_329)]
def childrenD_428 : Fin 4 → Finset Cell := ![(placedSet 3 (0, -1) envelope_26), (placedSet 0 (1, 0) envelope_416), (placedSet 0 (1, 0) envelope_244), (placedSet 0 (0, -1) envelope_329)]
theorem common_sub_428 : commonEnvelope childrenD_428 ⊆ insert (0, 0) required_428 := by decide
theorem child_required_sub_428 : ∀ j, childrenC_428 j ⊆ insert (0, 0) required_428 := by decide
theorem child_envelope_sub_428 : ∀ j, childrenD_428 j ⊆ envelope_428 := by decide
theorem pivot_mem_428 : (0, 0) ∈ envelope_428 := by decide
theorem children_work_428 : ∀ j, Template HasSnaky 16 (childrenC_428 j) (childrenD_428 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_26 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_416 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_244 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_329 0 (0, -1)).mono (by decide)
theorem row_works_428 : Template HasSnaky 17 required_428 envelope_428 := by
  refine compose HasSnaky 16 childrenC_428 childrenD_428 children_work_428 (0, 0)
    required_428 envelope_428 pivot_mem_428 child_required_sub_428 child_envelope_sub_428 ?_
  intro b hb; exact common_sub_428 (mem_commonEnvelope childrenD_428 b hb)
def required_451 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, -4), (1, -3), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_451 : Finset Cell := ⟨(([(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_451 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -1) required_1), (placedSet 0 (1, 0) required_449)]
def childrenD_451 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -1) envelope_1), (placedSet 0 (1, 0) envelope_449)]
theorem common_sub_451 : commonEnvelope childrenD_451 ⊆ insert (0, 0) required_451 := by decide
theorem child_required_sub_451 : ∀ j, childrenC_451 j ⊆ insert (0, 0) required_451 := by decide
theorem child_envelope_sub_451 : ∀ j, childrenD_451 j ⊆ envelope_451 := by decide
theorem pivot_mem_451 : (0, 0) ∈ envelope_451 := by decide
theorem children_work_451 : ∀ j, Template HasSnaky 16 (childrenC_451 j) (childrenD_451 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_1 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_449 0 (1, 0)).mono (by decide)
theorem row_works_451 : Template HasSnaky 17 required_451 envelope_451 := by
  refine compose HasSnaky 16 childrenC_451 childrenD_451 children_work_451 (0, 0)
    required_451 envelope_451 pivot_mem_451 child_required_sub_451 child_envelope_sub_451 ?_
  intro b hb; exact common_sub_451 (mem_commonEnvelope childrenD_451 b hb)
end SnakyConditional

end OAI
