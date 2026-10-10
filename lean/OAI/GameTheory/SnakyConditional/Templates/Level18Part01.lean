import OAI.GameTheory.SnakyConditional.Templates.Level17Part01

namespace OAI

namespace SnakyConditional
def required_416 : Finset Cell := ⟨(([(-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_416 : Finset Cell := ⟨(([(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_416 : Fin 6 → Finset Cell := ![(placedSet 2 (1, 0) required_176), (placedSet 4 (-3, 0) required_385), (placedSet 4 (-3, 0) required_197), (placedSet 0 (1, 0) required_295), (placedSet 2 (1, 0) required_245), (placedSet 2 (1, 0) required_220)]
def childrenD_416 : Fin 6 → Finset Cell := ![(placedSet 2 (1, 0) envelope_176), (placedSet 4 (-3, 0) envelope_385), (placedSet 4 (-3, 0) envelope_197), (placedSet 0 (1, 0) envelope_295), (placedSet 2 (1, 0) envelope_245), (placedSet 2 (1, 0) envelope_220)]
theorem common_sub_416 : commonEnvelope childrenD_416 ⊆ insert (0, 0) required_416 := by decide
theorem child_required_sub_416 : ∀ j, childrenC_416 j ⊆ insert (0, 0) required_416 := by decide
theorem child_envelope_sub_416 : ∀ j, childrenD_416 j ⊆ envelope_416 := by decide
theorem pivot_mem_416 : (0, 0) ∈ envelope_416 := by decide
theorem children_work_416 : ∀ j, Template HasSnaky 15 (childrenC_416 j) (childrenD_416 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_176 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_385 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_197 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_295 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_245 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_220 2 (1, 0)).mono (by decide)
theorem row_works_416 : Template HasSnaky 16 required_416 envelope_416 := by
  refine compose HasSnaky 15 childrenC_416 childrenD_416 children_work_416 (0, 0)
    required_416 envelope_416 pivot_mem_416 child_required_sub_416 child_envelope_sub_416 ?_
  intro b hb; exact common_sub_416 (mem_commonEnvelope childrenD_416 b hb)
end SnakyConditional

end OAI
