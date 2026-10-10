import OAI.GameTheory.SnakyConditional.Templates.Level16Part02

namespace OAI

namespace SnakyConditional
def required_434 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_434 : Finset Cell := ⟨(([(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_434 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 1) required_418), (placedSet 2 (1, 0) required_263), (placedSet 0 (1, 0) required_295), (placedSet 2 (1, 0) required_176), (placedSet 0 (0, -1) required_116)]
def childrenD_434 : Fin 5 → Finset Cell := ![(placedSet 0 (0, 1) envelope_418), (placedSet 2 (1, 0) envelope_263), (placedSet 0 (1, 0) envelope_295), (placedSet 2 (1, 0) envelope_176), (placedSet 0 (0, -1) envelope_116)]
theorem common_sub_434 : commonEnvelope childrenD_434 ⊆ insert (0, 0) required_434 := by decide
theorem child_required_sub_434 : ∀ j, childrenC_434 j ⊆ insert (0, 0) required_434 := by decide
theorem child_envelope_sub_434 : ∀ j, childrenD_434 j ⊆ envelope_434 := by decide
theorem pivot_mem_434 : (0, 0) ∈ envelope_434 := by decide
theorem children_work_434 : ∀ j, Template HasSnaky 14 (childrenC_434 j) (childrenD_434 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_418 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_263 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_295 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_176 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_116 0 (0, -1)).mono (by decide)
theorem row_works_434 : Template HasSnaky 15 required_434 envelope_434 := by
  refine compose HasSnaky 14 childrenC_434 childrenD_434 children_work_434 (0, 0)
    required_434 envelope_434 pivot_mem_434 child_required_sub_434 child_envelope_sub_434 ?_
  intro b hb; exact common_sub_434 (mem_commonEnvelope childrenD_434 b hb)
def required_437 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_437 : Finset Cell := ⟨(([(-3, -3), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_437 : Fin 4 → Finset Cell := ![(placedSet 7 (0, -4) required_55), (placedSet 0 (1, -2) required_427), (placedSet 0 (-1, 1) required_63), (placedSet 0 (1, -2) required_422)]
def childrenD_437 : Fin 4 → Finset Cell := ![(placedSet 7 (0, -4) envelope_55), (placedSet 0 (1, -2) envelope_427), (placedSet 0 (-1, 1) envelope_63), (placedSet 0 (1, -2) envelope_422)]
theorem common_sub_437 : commonEnvelope childrenD_437 ⊆ insert (0, 0) required_437 := by decide
theorem child_required_sub_437 : ∀ j, childrenC_437 j ⊆ insert (0, 0) required_437 := by decide
theorem child_envelope_sub_437 : ∀ j, childrenD_437 j ⊆ envelope_437 := by decide
theorem pivot_mem_437 : (0, 0) ∈ envelope_437 := by decide
theorem children_work_437 : ∀ j, Template HasSnaky 14 (childrenC_437 j) (childrenD_437 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 7 (0, -4)).mono (by decide)
  · exact (placed_template_map row_works_427 0 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_422 0 (1, -2)).mono (by decide)
theorem row_works_437 : Template HasSnaky 15 required_437 envelope_437 := by
  refine compose HasSnaky 14 childrenC_437 childrenD_437 children_work_437 (0, 0)
    required_437 envelope_437 pivot_mem_437 child_required_sub_437 child_envelope_sub_437 ?_
  intro b hb; exact common_sub_437 (mem_commonEnvelope childrenD_437 b hb)
end SnakyConditional

end OAI
