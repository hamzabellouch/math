import OAI.GameTheory.SnakyConditional.Templates.Level16Part03
import OAI.GameTheory.SnakyConditional.Templates.Level16Part06

namespace OAI

namespace SnakyConditional
def required_535 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_535 : Finset Cell := ⟨(([(-5, -2), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_535 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) required_444), (placedSet 0 (0, 1) required_426), (placedSet 0 (1, 0) required_25), (placedSet 4 (0, -2) required_321)]
def childrenD_535 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) envelope_444), (placedSet 0 (0, 1) envelope_426), (placedSet 0 (1, 0) envelope_25), (placedSet 4 (0, -2) envelope_321)]
theorem common_sub_535 : commonEnvelope childrenD_535 ⊆ insert (0, 0) required_535 := by decide
theorem child_required_sub_535 : ∀ j, childrenC_535 j ⊆ insert (0, 0) required_535 := by decide
theorem child_envelope_sub_535 : ∀ j, childrenD_535 j ⊆ envelope_535 := by decide
theorem pivot_mem_535 : (0, 0) ∈ envelope_535 := by decide
theorem children_work_535 : ∀ j, Template HasSnaky 14 (childrenC_535 j) (childrenD_535 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_444 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_426 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_25 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_321 4 (0, -2)).mono (by decide)
theorem row_works_535 : Template HasSnaky 15 required_535 envelope_535 := by
  refine compose HasSnaky 14 childrenC_535 childrenD_535 children_work_535 (0, 0)
    required_535 envelope_535 pivot_mem_535 child_required_sub_535 child_envelope_sub_535 ?_
  intro b hb; exact common_sub_535 (mem_commonEnvelope childrenD_535 b hb)
def required_548 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_548 : Finset Cell := ⟨(([(-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_548 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) required_426), (placedSet 0 (0, 1) required_541), (placedSet 0 (1, 0) required_25), (placedSet 4 (0, -2) required_321)]
def childrenD_548 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 1) envelope_426), (placedSet 0 (0, 1) envelope_541), (placedSet 0 (1, 0) envelope_25), (placedSet 4 (0, -2) envelope_321)]
theorem common_sub_548 : commonEnvelope childrenD_548 ⊆ insert (0, 0) required_548 := by decide
theorem child_required_sub_548 : ∀ j, childrenC_548 j ⊆ insert (0, 0) required_548 := by decide
theorem Internal.SnakyRows008C.containment_548_0 :
    placedSet 0 (0, 1) envelope_426 ⊆ envelope_548 := by decide
theorem Internal.SnakyRows008C.containment_548_1 :
    placedSet 0 (0, 1) envelope_541 ⊆ envelope_548 := by decide
theorem Internal.SnakyRows008C.containment_548_2 :
    placedSet 0 (1, 0) envelope_25 ⊆ envelope_548 := by decide
theorem Internal.SnakyRows008C.containment_548_3 :
    placedSet 4 (0, -2) envelope_321 ⊆ envelope_548 := by decide
theorem child_envelope_sub_548 : ∀ j, childrenD_548 j ⊆ envelope_548 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_548_0
  · exact Internal.SnakyRows008C.containment_548_1
  · exact Internal.SnakyRows008C.containment_548_2
  · exact Internal.SnakyRows008C.containment_548_3
theorem pivot_mem_548 : (0, 0) ∈ envelope_548 := by decide
theorem children_work_548 : ∀ j, Template HasSnaky 14 (childrenC_548 j) (childrenD_548 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_426 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_541 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_25 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_321 4 (0, -2)).mono (by decide)
theorem row_works_548 : Template HasSnaky 15 required_548 envelope_548 := by
  refine compose HasSnaky 14 childrenC_548 childrenD_548 children_work_548 (0, 0)
    required_548 envelope_548 pivot_mem_548 child_required_sub_548 child_envelope_sub_548 ?_
  intro b hb; exact common_sub_548 (mem_commonEnvelope childrenD_548 b hb)
end SnakyConditional

end OAI
