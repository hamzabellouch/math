import OAI.GameTheory.SnakyConditional.Templates.Level18Part01
import OAI.GameTheory.SnakyConditional.Templates.Level18Part04

namespace OAI

namespace SnakyConditional
def required_458 : Finset Cell := ⟨(([(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_458 : Finset Cell := ⟨(([(-5, 4), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_458 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -2) required_130), (placedSet 1 (0, -2) required_177), (placedSet 0 (-3, 0) required_450)]
def childrenD_458 : Fin 3 → Finset Cell := ![(placedSet 1 (0, -2) envelope_130), (placedSet 1 (0, -2) envelope_177), (placedSet 0 (-3, 0) envelope_450)]
theorem common_sub_458 : commonEnvelope childrenD_458 ⊆ insert (0, 0) required_458 := by decide
theorem child_required_sub_458 : ∀ j, childrenC_458 j ⊆ insert (0, 0) required_458 := by decide
theorem child_envelope_sub_458 : ∀ j, childrenD_458 j ⊆ envelope_458 := by decide
theorem pivot_mem_458 : (0, 0) ∈ envelope_458 := by decide
theorem children_work_458 : ∀ j, Template HasSnaky 16 (childrenC_458 j) (childrenD_458 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_130 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_177 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_450 0 (-3, 0)).mono (by decide)
theorem row_works_458 : Template HasSnaky 17 required_458 envelope_458 := by
  refine compose HasSnaky 16 childrenC_458 childrenD_458 children_work_458 (0, 0)
    required_458 envelope_458 pivot_mem_458 child_required_sub_458 child_envelope_sub_458 ?_
  intro b hb; exact common_sub_458 (mem_commonEnvelope childrenD_458 b hb)
def required_526 : Finset Cell := ⟨(([(-1, -2), (-1, 0), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_526 : Finset Cell := ⟨(([(-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_526 : Fin 5 → Finset Cell := ![(placedSet 0 (0, -1) required_359), (placedSet 4 (-2, 0) required_416), (placedSet 5 (0, -1) required_327), (placedSet 0 (1, 0) required_489), (placedSet 3 (-2, 0) required_399)]
def childrenD_526 : Fin 5 → Finset Cell := ![(placedSet 0 (0, -1) envelope_359), (placedSet 4 (-2, 0) envelope_416), (placedSet 5 (0, -1) envelope_327), (placedSet 0 (1, 0) envelope_489), (placedSet 3 (-2, 0) envelope_399)]
theorem common_sub_526 : commonEnvelope childrenD_526 ⊆ insert (0, 0) required_526 := by decide
theorem child_required_sub_526 : ∀ j, childrenC_526 j ⊆ insert (0, 0) required_526 := by decide
theorem child_envelope_sub_526 : ∀ j, childrenD_526 j ⊆ envelope_526 := by decide
theorem pivot_mem_526 : (0, 0) ∈ envelope_526 := by decide
theorem children_work_526 : ∀ j, Template HasSnaky 16 (childrenC_526 j) (childrenD_526 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_359 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_416 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_327 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_489 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_399 3 (-2, 0)).mono (by decide)
theorem row_works_526 : Template HasSnaky 17 required_526 envelope_526 := by
  refine compose HasSnaky 16 childrenC_526 childrenD_526 children_work_526 (0, 0)
    required_526 envelope_526 pivot_mem_526 child_required_sub_526 child_envelope_sub_526 ?_
  intro b hb; exact common_sub_526 (mem_commonEnvelope childrenD_526 b hb)
end SnakyConditional

end OAI
