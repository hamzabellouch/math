import OAI.GameTheory.SnakyConditional.Templates.Level15Part02
import OAI.GameTheory.SnakyConditional.Templates.Level15Part05

namespace OAI

namespace SnakyConditional
def required_524 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_524 : Finset Cell := ⟨(([(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_524 : Fin 5 → Finset Cell := ![(placedSet 4 (1, -1) required_504), (placedSet 0 (-1, -1) required_504), (placedSet 0 (0, 1) required_180), (placedSet 4 (0, 1) required_180), (placedSet 0 (-1, 0) required_261)]
def childrenD_524 : Fin 5 → Finset Cell := ![(placedSet 4 (1, -1) envelope_504), (placedSet 0 (-1, -1) envelope_504), (placedSet 0 (0, 1) envelope_180), (placedSet 4 (0, 1) envelope_180), (placedSet 0 (-1, 0) envelope_261)]
theorem common_sub_524 : commonEnvelope childrenD_524 ⊆ insert (0, 0) required_524 := by decide
theorem child_required_sub_524 : ∀ j, childrenC_524 j ⊆ insert (0, 0) required_524 := by decide
theorem child_envelope_sub_524 : ∀ j, childrenD_524 j ⊆ envelope_524 := by decide
theorem pivot_mem_524 : (0, 0) ∈ envelope_524 := by decide
theorem children_work_524 : ∀ j, Template HasSnaky 13 (childrenC_524 j) (childrenD_524 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_504 4 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_504 0 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_180 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_180 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_261 0 (-1, 0)).mono (by decide)
theorem row_works_524 : Template HasSnaky 14 required_524 envelope_524 := by
  refine compose HasSnaky 13 childrenC_524 childrenD_524 children_work_524 (0, 0)
    required_524 envelope_524 pivot_mem_524 child_required_sub_524 child_envelope_sub_524 ?_
  intro b hb; exact common_sub_524 (mem_commonEnvelope childrenD_524 b hb)
def required_532 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_532 : Finset Cell := ⟨(([(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_532 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -1) required_504), (placedSet 7 (-1, -4) required_6)]
def childrenD_532 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -1) envelope_504), (placedSet 7 (-1, -4) envelope_6)]
theorem common_sub_532 : commonEnvelope childrenD_532 ⊆ insert (0, 0) required_532 := by decide
theorem child_required_sub_532 : ∀ j, childrenC_532 j ⊆ insert (0, 0) required_532 := by decide
theorem child_envelope_sub_532 : ∀ j, childrenD_532 j ⊆ envelope_532 := by decide
theorem pivot_mem_532 : (0, 0) ∈ envelope_532 := by decide
theorem children_work_532 : ∀ j, Template HasSnaky 13 (childrenC_532 j) (childrenD_532 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_504 4 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_6 7 (-1, -4)).mono (by decide)
theorem row_works_532 : Template HasSnaky 14 required_532 envelope_532 := by
  refine compose HasSnaky 13 childrenC_532 childrenD_532 children_work_532 (0, 0)
    required_532 envelope_532 pivot_mem_532 child_required_sub_532 child_envelope_sub_532 ?_
  intro b hb; exact common_sub_532 (mem_commonEnvelope childrenD_532 b hb)
def required_541 : Finset Cell := ⟨(([(-2, -2), (-1, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_541 : Finset Cell := ⟨(([(-5, 0), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_541 : Fin 6 → Finset Cell := ![(placedSet 0 (1, 1) required_236), (placedSet 7 (0, -3) required_142), (placedSet 3 (0, -3) required_160), (placedSet 0 (1, -1) required_194), (placedSet 4 (-3, -2) required_501), (placedSet 0 (1, -1) required_412)]
def childrenD_541 : Fin 6 → Finset Cell := ![(placedSet 0 (1, 1) envelope_236), (placedSet 7 (0, -3) envelope_142), (placedSet 3 (0, -3) envelope_160), (placedSet 0 (1, -1) envelope_194), (placedSet 4 (-3, -2) envelope_501), (placedSet 0 (1, -1) envelope_412)]
theorem common_sub_541 : commonEnvelope childrenD_541 ⊆ insert (0, 0) required_541 := by decide
theorem child_required_sub_541 : ∀ j, childrenC_541 j ⊆ insert (0, 0) required_541 := by decide
theorem child_envelope_sub_541 : ∀ j, childrenD_541 j ⊆ envelope_541 := by decide
theorem pivot_mem_541 : (0, 0) ∈ envelope_541 := by decide
theorem children_work_541 : ∀ j, Template HasSnaky 13 (childrenC_541 j) (childrenD_541 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_236 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_142 7 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_160 3 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_194 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_501 4 (-3, -2)).mono (by decide)
  · exact (placed_template_map row_works_412 0 (1, -1)).mono (by decide)
theorem row_works_541 : Template HasSnaky 14 required_541 envelope_541 := by
  refine compose HasSnaky 13 childrenC_541 childrenD_541 children_work_541 (0, 0)
    required_541 envelope_541 pivot_mem_541 child_required_sub_541 child_envelope_sub_541 ?_
  intro b hb; exact common_sub_541 (mem_commonEnvelope childrenD_541 b hb)
end SnakyConditional

end OAI
