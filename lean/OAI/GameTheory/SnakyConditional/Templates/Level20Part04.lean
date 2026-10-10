import OAI.GameTheory.SnakyConditional.Templates.Level19Part01
import OAI.GameTheory.SnakyConditional.Templates.Level19Part03

namespace OAI

namespace SnakyConditional
def required_540 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, -3), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_540 : Finset Cell := ⟨(([(-3, -3), (-3, 1), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_540 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) required_334), (placedSet 1 (1, 0) required_51), (placedSet 3 (0, -1) required_88), (placedSet 0 (1, 0) required_536)]
def childrenD_540 : Fin 4 → Finset Cell := ![(placedSet 0 (0, -1) envelope_334), (placedSet 1 (1, 0) envelope_51), (placedSet 3 (0, -1) envelope_88), (placedSet 0 (1, 0) envelope_536)]
theorem common_sub_540 : commonEnvelope childrenD_540 ⊆ insert (0, 0) required_540 := by decide
theorem child_required_sub_540 : ∀ j, childrenC_540 j ⊆ insert (0, 0) required_540 := by decide
theorem child_envelope_sub_540 : ∀ j, childrenD_540 j ⊆ envelope_540 := by decide
theorem pivot_mem_540 : (0, 0) ∈ envelope_540 := by decide
theorem children_work_540 : ∀ j, Template HasSnaky 17 (childrenC_540 j) (childrenD_540 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_334 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_51 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_88 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_536 0 (1, 0)).mono (by decide)
theorem row_works_540 : Template HasSnaky 18 required_540 envelope_540 := by
  refine compose HasSnaky 17 childrenC_540 childrenD_540 children_work_540 (0, 0)
    required_540 envelope_540 pivot_mem_540 child_required_sub_540 child_envelope_sub_540 ?_
  intro b hb; exact common_sub_540 (mem_commonEnvelope childrenD_540 b hb)
def required_544 : Finset Cell := ⟨(([(1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_544 : Finset Cell := ⟨(([(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -2), (10, 0), (10, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_544 : Fin 3 → Finset Cell := ![(placedSet 2 (3, 0) required_263), (placedSet 6 (-1, 0) required_9), (placedSet 1 (4, -1) required_451)]
def childrenD_544 : Fin 3 → Finset Cell := ![(placedSet 2 (3, 0) envelope_263), (placedSet 6 (-1, 0) envelope_9), (placedSet 1 (4, -1) envelope_451)]
theorem common_sub_544 : commonEnvelope childrenD_544 ⊆ insert (0, 0) required_544 := by decide
theorem child_required_sub_544 : ∀ j, childrenC_544 j ⊆ insert (0, 0) required_544 := by decide
theorem Internal.SnakyRows008C.containment_544_0 :
    placedSet 2 (3, 0) envelope_263 ⊆ envelope_544 := by decide
theorem Internal.SnakyRows008C.containment_544_1 :
    placedSet 6 (-1, 0) envelope_9 ⊆ envelope_544 := by decide
theorem Internal.SnakyRows008C.containment_544_2 :
    placedSet 1 (4, -1) envelope_451 ⊆ envelope_544 := by decide
theorem child_envelope_sub_544 : ∀ j, childrenD_544 j ⊆ envelope_544 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_544_0
  · exact Internal.SnakyRows008C.containment_544_1
  · exact Internal.SnakyRows008C.containment_544_2
theorem pivot_mem_544 : (0, 0) ∈ envelope_544 := by decide
theorem children_work_544 : ∀ j, Template HasSnaky 17 (childrenC_544 j) (childrenD_544 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_263 2 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_9 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_451 1 (4, -1)).mono (by decide)
theorem row_works_544 : Template HasSnaky 18 required_544 envelope_544 := by
  refine compose HasSnaky 17 childrenC_544 childrenD_544 children_work_544 (0, 0)
    required_544 envelope_544 pivot_mem_544 child_required_sub_544 child_envelope_sub_544 ?_
  intro b hb; exact common_sub_544 (mem_commonEnvelope childrenD_544 b hb)
end SnakyConditional

end OAI
