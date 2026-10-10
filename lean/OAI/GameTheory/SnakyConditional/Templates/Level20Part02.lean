import OAI.GameTheory.SnakyConditional.Templates.Level19Part01
import OAI.GameTheory.SnakyConditional.Templates.Level19Part02

namespace OAI

namespace SnakyConditional
def required_452 : Finset Cell := ⟨(([(-1, 1), (-1, 2), (0, 1), (0, 2), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_452 : Finset Cell := ⟨(([(-4, 5), (-4, 7), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_452 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 3) required_24), (placedSet 0 (-1, 4) required_451), (placedSet 3 (-1, 3) required_25)]
def childrenD_452 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 3) envelope_24), (placedSet 0 (-1, 4) envelope_451), (placedSet 3 (-1, 3) envelope_25)]
theorem common_sub_452 : commonEnvelope childrenD_452 ⊆ insert (0, 0) required_452 := by decide
theorem child_required_sub_452 : ∀ j, childrenC_452 j ⊆ insert (0, 0) required_452 := by decide
theorem child_envelope_sub_452 : ∀ j, childrenD_452 j ⊆ envelope_452 := by decide
theorem pivot_mem_452 : (0, 0) ∈ envelope_452 := by decide
theorem children_work_452 : ∀ j, Template HasSnaky 17 (childrenC_452 j) (childrenD_452 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 1 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_451 0 (-1, 4)).mono (by decide)
  · exact (placed_template_map row_works_25 3 (-1, 3)).mono (by decide)
theorem row_works_452 : Template HasSnaky 18 required_452 envelope_452 := by
  refine compose HasSnaky 17 childrenC_452 childrenD_452 children_work_452 (0, 0)
    required_452 envelope_452 pivot_mem_452 child_required_sub_452 child_envelope_sub_452 ?_
  intro b hb; exact common_sub_452 (mem_commonEnvelope childrenD_452 b hb)
def required_461 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_461 : Finset Cell := ⟨(([(-3, 4), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_461 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_4), (placedSet 0 (2, 0) required_458)]
def childrenD_461 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_4), (placedSet 0 (2, 0) envelope_458)]
theorem common_sub_461 : commonEnvelope childrenD_461 ⊆ insert (0, 0) required_461 := by decide
theorem child_required_sub_461 : ∀ j, childrenC_461 j ⊆ insert (0, 0) required_461 := by decide
theorem child_envelope_sub_461 : ∀ j, childrenD_461 j ⊆ envelope_461 := by decide
theorem pivot_mem_461 : (0, 0) ∈ envelope_461 := by decide
theorem children_work_461 : ∀ j, Template HasSnaky 17 (childrenC_461 j) (childrenD_461 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_458 0 (2, 0)).mono (by decide)
theorem row_works_461 : Template HasSnaky 18 required_461 envelope_461 := by
  refine compose HasSnaky 17 childrenC_461 childrenD_461 children_work_461 (0, 0)
    required_461 envelope_461 pivot_mem_461 child_required_sub_461 child_envelope_sub_461 ?_
  intro b hb; exact common_sub_461 (mem_commonEnvelope childrenD_461 b hb)
end SnakyConditional

end OAI
