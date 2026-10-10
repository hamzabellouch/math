import OAI.GameTheory.SnakyConditional.Templates.Level14Part03
import OAI.GameTheory.SnakyConditional.Templates.Level14Part05
import OAI.GameTheory.SnakyConditional.Templates.Level14Part06

namespace OAI

namespace SnakyConditional
def required_495 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_495 : Finset Cell := ⟨(([(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_495 : Fin 3 → Finset Cell := ![(placedSet 6 (-3, -1) required_25), (placedSet 4 (-3, 0) required_167), (placedSet 4 (-3, 0) required_456)]
def childrenD_495 : Fin 3 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_25), (placedSet 4 (-3, 0) envelope_167), (placedSet 4 (-3, 0) envelope_456)]
theorem common_sub_495 : commonEnvelope childrenD_495 ⊆ insert (0, 0) required_495 := by decide
theorem child_required_sub_495 : ∀ j, childrenC_495 j ⊆ insert (0, 0) required_495 := by decide
theorem child_envelope_sub_495 : ∀ j, childrenD_495 j ⊆ envelope_495 := by decide
theorem pivot_mem_495 : (0, 0) ∈ envelope_495 := by decide
theorem children_work_495 : ∀ j, Template HasSnaky 12 (childrenC_495 j) (childrenD_495 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_167 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_456 4 (-3, 0)).mono (by decide)
theorem row_works_495 : Template HasSnaky 13 required_495 envelope_495 := by
  refine compose HasSnaky 12 childrenC_495 childrenD_495 children_work_495 (0, 0)
    required_495 envelope_495 pivot_mem_495 child_required_sub_495 child_envelope_sub_495 ?_
  intro b hb; exact common_sub_495 (mem_commonEnvelope childrenD_495 b hb)
def required_504 : Finset Cell := ⟨(([(1, -2), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_504 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_504 : Fin 5 → Finset Cell := ![(placedSet 0 (-1, 0) required_381), (placedSet 4 (0, 1) required_310), (placedSet 0 (1, 2) required_159), (placedSet 4 (-1, 0) required_351), (placedSet 0 (-1, 0) required_496)]
def childrenD_504 : Fin 5 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_381), (placedSet 4 (0, 1) envelope_310), (placedSet 0 (1, 2) envelope_159), (placedSet 4 (-1, 0) envelope_351), (placedSet 0 (-1, 0) envelope_496)]
theorem common_sub_504 : commonEnvelope childrenD_504 ⊆ insert (0, 0) required_504 := by decide
theorem child_required_sub_504 : ∀ j, childrenC_504 j ⊆ insert (0, 0) required_504 := by decide
theorem child_envelope_sub_504 : ∀ j, childrenD_504 j ⊆ envelope_504 := by decide
theorem pivot_mem_504 : (0, 0) ∈ envelope_504 := by decide
theorem children_work_504 : ∀ j, Template HasSnaky 12 (childrenC_504 j) (childrenD_504 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_381 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_310 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_159 0 (1, 2)).mono (by decide)
  · exact (placed_template_map row_works_351 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_496 0 (-1, 0)).mono (by decide)
theorem row_works_504 : Template HasSnaky 13 required_504 envelope_504 := by
  refine compose HasSnaky 12 childrenC_504 childrenD_504 children_work_504 (0, 0)
    required_504 envelope_504 pivot_mem_504 child_required_sub_504 child_envelope_sub_504 ?_
  intro b hb; exact common_sub_504 (mem_commonEnvelope childrenD_504 b hb)
def required_508 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, -1), (-1, -2), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_508 : Finset Cell := ⟨(([(-5, 2), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_508 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (-3, 1) required_393)]
def childrenD_508 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (-3, 1) envelope_393)]
theorem common_sub_508 : commonEnvelope childrenD_508 ⊆ insert (0, 0) required_508 := by decide
theorem child_required_sub_508 : ∀ j, childrenC_508 j ⊆ insert (0, 0) required_508 := by decide
theorem child_envelope_sub_508 : ∀ j, childrenD_508 j ⊆ envelope_508 := by decide
theorem pivot_mem_508 : (0, 0) ∈ envelope_508 := by decide
theorem children_work_508 : ∀ j, Template HasSnaky 12 (childrenC_508 j) (childrenD_508 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_393 0 (-3, 1)).mono (by decide)
theorem row_works_508 : Template HasSnaky 13 required_508 envelope_508 := by
  refine compose HasSnaky 12 childrenC_508 childrenD_508 children_work_508 (0, 0)
    required_508 envelope_508 pivot_mem_508 child_required_sub_508 child_envelope_sub_508 ?_
  intro b hb; exact common_sub_508 (mem_commonEnvelope childrenD_508 b hb)
end SnakyConditional

end OAI
