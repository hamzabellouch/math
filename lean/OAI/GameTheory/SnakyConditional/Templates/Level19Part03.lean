import OAI.GameTheory.SnakyConditional.Templates.Level18Part02
import OAI.GameTheory.SnakyConditional.Templates.Level18Part07

namespace OAI

namespace SnakyConditional
def required_536 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_536 : Finset Cell := ⟨(([(-4, 1), (-4, 3), (-3, -3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_536 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) required_307), (placedSet 0 (1, 0) required_244), (placedSet 3 (0, -1) required_26), (placedSet 0 (1, -2) required_534)]
def childrenD_536 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) envelope_307), (placedSet 0 (1, 0) envelope_244), (placedSet 3 (0, -1) envelope_26), (placedSet 0 (1, -2) envelope_534)]
theorem common_sub_536 : commonEnvelope childrenD_536 ⊆ insert (0, 0) required_536 := by decide
theorem child_required_sub_536 : ∀ j, childrenC_536 j ⊆ insert (0, 0) required_536 := by decide
theorem child_envelope_sub_536 : ∀ j, childrenD_536 j ⊆ envelope_536 := by decide
theorem pivot_mem_536 : (0, 0) ∈ envelope_536 := by decide
theorem children_work_536 : ∀ j, Template HasSnaky 16 (childrenC_536 j) (childrenD_536 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_307 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_244 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_26 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_534 0 (1, -2)).mono (by decide)
theorem row_works_536 : Template HasSnaky 17 required_536 envelope_536 := by
  refine compose HasSnaky 16 childrenC_536 childrenD_536 children_work_536 (0, 0)
    required_536 envelope_536 pivot_mem_536 child_required_sub_536 child_envelope_sub_536 ?_
  intro b hb; exact common_sub_536 (mem_commonEnvelope childrenD_536 b hb)
def required_542 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_542 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_542 : Fin 2 → Finset Cell := ![(placedSet 5 (1, -4) required_6), (placedSet 0 (0, 1) required_442)]
def childrenD_542 : Fin 2 → Finset Cell := ![(placedSet 5 (1, -4) envelope_6), (placedSet 0 (0, 1) envelope_442)]
theorem common_sub_542 : commonEnvelope childrenD_542 ⊆ insert (0, 0) required_542 := by decide
theorem child_required_sub_542 : ∀ j, childrenC_542 j ⊆ insert (0, 0) required_542 := by decide
theorem child_envelope_sub_542 : ∀ j, childrenD_542 j ⊆ envelope_542 := by decide
theorem pivot_mem_542 : (0, 0) ∈ envelope_542 := by decide
theorem children_work_542 : ∀ j, Template HasSnaky 16 (childrenC_542 j) (childrenD_542 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 5 (1, -4)).mono (by decide)
  · exact (placed_template_map row_works_442 0 (0, 1)).mono (by decide)
theorem row_works_542 : Template HasSnaky 17 required_542 envelope_542 := by
  refine compose HasSnaky 16 childrenC_542 childrenD_542 children_work_542 (0, 0)
    required_542 envelope_542 pivot_mem_542 child_required_sub_542 child_envelope_sub_542 ?_
  intro b hb; exact common_sub_542 (mem_commonEnvelope childrenD_542 b hb)
end SnakyConditional

end OAI
