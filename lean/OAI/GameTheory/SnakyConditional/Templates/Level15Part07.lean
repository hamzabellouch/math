import OAI.GameTheory.SnakyConditional.Templates.Level14Part05

namespace OAI

namespace SnakyConditional
def required_530 : Finset Cell := ⟨(([(0, -1), (0, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_530 : Finset Cell := ⟨(([(-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_530 : Fin 4 → Finset Cell := ![(placedSet 7 (0, -2) required_456), (placedSet 0 (1, 1) required_336), (placedSet 7 (0, -2) required_283), (placedSet 5 (1, 1) required_271)]
def childrenD_530 : Fin 4 → Finset Cell := ![(placedSet 7 (0, -2) envelope_456), (placedSet 0 (1, 1) envelope_336), (placedSet 7 (0, -2) envelope_283), (placedSet 5 (1, 1) envelope_271)]
theorem common_sub_530 : commonEnvelope childrenD_530 ⊆ insert (0, 0) required_530 := by decide
theorem child_required_sub_530 : ∀ j, childrenC_530 j ⊆ insert (0, 0) required_530 := by decide
theorem child_envelope_sub_530 : ∀ j, childrenD_530 j ⊆ envelope_530 := by decide
theorem pivot_mem_530 : (0, 0) ∈ envelope_530 := by decide
theorem children_work_530 : ∀ j, Template HasSnaky 12 (childrenC_530 j) (childrenD_530 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_456 7 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_336 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_283 7 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_271 5 (1, 1)).mono (by decide)
theorem row_works_530 : Template HasSnaky 13 required_530 envelope_530 := by
  refine compose HasSnaky 12 childrenC_530 childrenD_530 children_work_530 (0, 0)
    required_530 envelope_530 pivot_mem_530 child_required_sub_530 child_envelope_sub_530 ?_
  intro b hb; exact common_sub_530 (mem_commonEnvelope childrenD_530 b hb)
def required_550 : Finset Cell := ⟨(([(0, -1), (0, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_550 : Finset Cell := ⟨(([(-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_550 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 2) required_424), (placedSet 7 (0, -2) required_172), (placedSet 1 (1, 1) required_215), (placedSet 7 (0, -2) required_456)]
def childrenD_550 : Fin 4 → Finset Cell := ![(placedSet 0 (0, 2) envelope_424), (placedSet 7 (0, -2) envelope_172), (placedSet 1 (1, 1) envelope_215), (placedSet 7 (0, -2) envelope_456)]
theorem common_sub_550 : commonEnvelope childrenD_550 ⊆ insert (0, 0) required_550 := by decide
theorem child_required_sub_550 : ∀ j, childrenC_550 j ⊆ insert (0, 0) required_550 := by decide
theorem Internal.SnakyRows008C.containment_550_0 :
    placedSet 0 (0, 2) envelope_424 ⊆ envelope_550 := by decide
theorem Internal.SnakyRows008C.containment_550_1 :
    placedSet 7 (0, -2) envelope_172 ⊆ envelope_550 := by decide
theorem Internal.SnakyRows008C.containment_550_2 :
    placedSet 1 (1, 1) envelope_215 ⊆ envelope_550 := by decide
theorem Internal.SnakyRows008C.containment_550_3 :
    placedSet 7 (0, -2) envelope_456 ⊆ envelope_550 := by decide
theorem child_envelope_sub_550 : ∀ j, childrenD_550 j ⊆ envelope_550 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_550_0
  · exact Internal.SnakyRows008C.containment_550_1
  · exact Internal.SnakyRows008C.containment_550_2
  · exact Internal.SnakyRows008C.containment_550_3
theorem pivot_mem_550 : (0, 0) ∈ envelope_550 := by decide
theorem children_work_550 : ∀ j, Template HasSnaky 12 (childrenC_550 j) (childrenD_550 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_424 0 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_172 7 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_215 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_456 7 (0, -2)).mono (by decide)
theorem row_works_550 : Template HasSnaky 13 required_550 envelope_550 := by
  refine compose HasSnaky 12 childrenC_550 childrenD_550 children_work_550 (0, 0)
    required_550 envelope_550 pivot_mem_550 child_required_sub_550 child_envelope_sub_550 ?_
  intro b hb; exact common_sub_550 (mem_commonEnvelope childrenD_550 b hb)
end SnakyConditional

end OAI
