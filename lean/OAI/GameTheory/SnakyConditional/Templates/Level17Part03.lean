import OAI.GameTheory.SnakyConditional.Templates.Level16Part02
import OAI.GameTheory.SnakyConditional.Templates.Level16Part03

namespace OAI

namespace SnakyConditional
def required_439 : Finset Cell := ⟨(([(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_439 : Finset Cell := ⟨(([(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_439 : Fin 5 → Finset Cell := ![(placedSet 2 (1, 0) required_176), (placedSet 0 (1, 0) required_295), (placedSet 2 (1, 0) required_263), (placedSet 0 (0, 1) required_418), (placedSet 0 (0, -1) required_149)]
def childrenD_439 : Fin 5 → Finset Cell := ![(placedSet 2 (1, 0) envelope_176), (placedSet 0 (1, 0) envelope_295), (placedSet 2 (1, 0) envelope_263), (placedSet 0 (0, 1) envelope_418), (placedSet 0 (0, -1) envelope_149)]
theorem common_sub_439 : commonEnvelope childrenD_439 ⊆ insert (0, 0) required_439 := by decide
theorem child_required_sub_439 : ∀ j, childrenC_439 j ⊆ insert (0, 0) required_439 := by decide
theorem child_envelope_sub_439 : ∀ j, childrenD_439 j ⊆ envelope_439 := by decide
theorem pivot_mem_439 : (0, 0) ∈ envelope_439 := by decide
theorem children_work_439 : ∀ j, Template HasSnaky 14 (childrenC_439 j) (childrenD_439 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_176 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_295 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_263 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_418 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_149 0 (0, -1)).mono (by decide)
theorem row_works_439 : Template HasSnaky 15 required_439 envelope_439 := by
  refine compose HasSnaky 14 childrenC_439 childrenD_439 children_work_439 (0, 0)
    required_439 envelope_439 pivot_mem_439 child_required_sub_439 child_envelope_sub_439 ?_
  intro b hb; exact common_sub_439 (mem_commonEnvelope childrenD_439 b hb)
def required_440 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_440 : Finset Cell := ⟨(([(-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_440 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_6), (placedSet 0 (-2, 1) required_435)]
def childrenD_440 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_6), (placedSet 0 (-2, 1) envelope_435)]
theorem common_sub_440 : commonEnvelope childrenD_440 ⊆ insert (0, 0) required_440 := by decide
theorem child_required_sub_440 : ∀ j, childrenC_440 j ⊆ insert (0, 0) required_440 := by decide
theorem child_envelope_sub_440 : ∀ j, childrenD_440 j ⊆ envelope_440 := by decide
theorem pivot_mem_440 : (0, 0) ∈ envelope_440 := by decide
theorem children_work_440 : ∀ j, Template HasSnaky 14 (childrenC_440 j) (childrenD_440 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_435 0 (-2, 1)).mono (by decide)
theorem row_works_440 : Template HasSnaky 15 required_440 envelope_440 := by
  refine compose HasSnaky 14 childrenC_440 childrenD_440 children_work_440 (0, 0)
    required_440 envelope_440 pivot_mem_440 child_required_sub_440 child_envelope_sub_440 ?_
  intro b hb; exact common_sub_440 (mem_commonEnvelope childrenD_440 b hb)
end SnakyConditional

end OAI
