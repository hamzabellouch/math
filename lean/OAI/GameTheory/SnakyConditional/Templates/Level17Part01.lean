import OAI.GameTheory.SnakyConditional.Templates.Level16Part01
import OAI.GameTheory.SnakyConditional.Templates.Level16Part02

namespace OAI

namespace SnakyConditional
def required_385 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_385 : Finset Cell := ⟨(([(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_385 : Fin 4 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 2 (-3, 1) required_64), (placedSet 0 (1, 0) required_55), (placedSet 4 (-3, 1) required_369)]
def childrenD_385 : Fin 4 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 2 (-3, 1) envelope_64), (placedSet 0 (1, 0) envelope_55), (placedSet 4 (-3, 1) envelope_369)]
theorem common_sub_385 : commonEnvelope childrenD_385 ⊆ insert (0, 0) required_385 := by decide
theorem child_required_sub_385 : ∀ j, childrenC_385 j ⊆ insert (0, 0) required_385 := by decide
theorem child_envelope_sub_385 : ∀ j, childrenD_385 j ⊆ envelope_385 := by decide
theorem pivot_mem_385 : (0, 0) ∈ envelope_385 := by decide
theorem children_work_385 : ∀ j, Template HasSnaky 14 (childrenC_385 j) (childrenD_385 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_64 2 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_369 4 (-3, 1)).mono (by decide)
theorem row_works_385 : Template HasSnaky 15 required_385 envelope_385 := by
  refine compose HasSnaky 14 childrenC_385 childrenD_385 children_work_385 (0, 0)
    required_385 envelope_385 pivot_mem_385 child_required_sub_385 child_envelope_sub_385 ?_
  intro b hb; exact common_sub_385 (mem_commonEnvelope childrenD_385 b hb)
def required_433 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_433 : Finset Cell := ⟨(([(-3, -3), (-2, -3), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_433 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) required_63), (placedSet 3 (-1, 0) required_7), (placedSet 0 (1, -2) required_427), (placedSet 0 (1, -2) required_422)]
def childrenD_433 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) envelope_63), (placedSet 3 (-1, 0) envelope_7), (placedSet 0 (1, -2) envelope_427), (placedSet 0 (1, -2) envelope_422)]
theorem common_sub_433 : commonEnvelope childrenD_433 ⊆ insert (0, 0) required_433 := by decide
theorem child_required_sub_433 : ∀ j, childrenC_433 j ⊆ insert (0, 0) required_433 := by decide
theorem child_envelope_sub_433 : ∀ j, childrenD_433 j ⊆ envelope_433 := by decide
theorem pivot_mem_433 : (0, 0) ∈ envelope_433 := by decide
theorem children_work_433 : ∀ j, Template HasSnaky 14 (childrenC_433 j) (childrenD_433 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_427 0 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_422 0 (1, -2)).mono (by decide)
theorem row_works_433 : Template HasSnaky 15 required_433 envelope_433 := by
  refine compose HasSnaky 14 childrenC_433 childrenD_433 children_work_433 (0, 0)
    required_433 envelope_433 pivot_mem_433 child_required_sub_433 child_envelope_sub_433 ?_
  intro b hb; exact common_sub_433 (mem_commonEnvelope childrenD_433 b hb)
end SnakyConditional

end OAI
