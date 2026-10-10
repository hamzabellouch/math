import OAI.GameTheory.SnakyConditional.Regions.Region557
import OAI.GameTheory.SnakyConditional.Templates.Level20Part02
import OAI.GameTheory.SnakyConditional.Templates.Level20Part03

namespace OAI

namespace SnakyConditional
def required_464 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_464 : Finset Cell := ⟨(([(-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_464 : Fin 6 → Finset Cell := ![(placedSet 0 (-1, 1) required_63), (placedSet 0 (1, 0) required_224), (placedSet 0 (3, -1) required_315), (placedSet 0 (1, 1) required_306), (placedSet 0 (3, -1) required_358), (placedSet 0 (1, 1) required_461)]
def childrenD_464 : Fin 6 → Finset Cell := ![(placedSet 0 (-1, 1) envelope_63), (placedSet 0 (1, 0) envelope_224), (placedSet 0 (3, -1) envelope_315), (placedSet 0 (1, 1) envelope_306), (placedSet 0 (3, -1) envelope_358), (placedSet 0 (1, 1) envelope_461)]
theorem common_sub_464 : commonEnvelope childrenD_464 ⊆ insert (0, 0) required_464 := by decide
theorem child_required_sub_464 : ∀ j, childrenC_464 j ⊆ insert (0, 0) required_464 := by decide
theorem child_envelope_sub_464 : ∀ j, childrenD_464 j ⊆ envelope_464 := by decide
theorem pivot_mem_464 : (0, 0) ∈ envelope_464 := by decide
theorem children_work_464 : ∀ j, Template HasSnaky 18 (childrenC_464 j) (childrenD_464 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_224 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_315 0 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_306 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_358 0 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_461 0 (1, 1)).mono (by decide)
theorem row_works_464 : Template HasSnaky 19 required_464 envelope_464 := by
  refine compose HasSnaky 18 childrenC_464 childrenD_464 children_work_464 (0, 0)
    required_464 envelope_464 pivot_mem_464 child_required_sub_464 child_envelope_sub_464 ?_
  intro b hb; exact common_sub_464 (mem_commonEnvelope childrenD_464 b hb)
def childrenC_557 : Fin 7 → Finset Cell := ![(placedSet 0 (1, 0) required_460), (placedSet 4 (-2, 0) required_460), (placedSet 2 (1, 0) required_460), (placedSet 4 (1, 0) required_411), (placedSet 0 (-1, 2) required_531), (placedSet 4 (0, 2) required_531), (placedSet 5 (1, 0) required_406)]
def childrenD_557 : Fin 7 → Finset Cell := ![(placedSet 0 (1, 0) envelope_460), (placedSet 4 (-2, 0) envelope_460), (placedSet 2 (1, 0) envelope_460), (placedSet 4 (1, 0) envelope_411), (placedSet 0 (-1, 2) envelope_531), (placedSet 4 (0, 2) envelope_531), (placedSet 5 (1, 0) envelope_406)]
theorem common_sub_557 : commonEnvelope childrenD_557 ⊆ insert (0, 0) required_557 := by decide
theorem child_required_sub_557 : ∀ j, childrenC_557 j ⊆ insert (0, 0) required_557 := by decide
theorem Internal.SnakyRows008C.containment_557_0 :
    placedSet 0 (1, 0) envelope_460 ⊆ envelope_557 := by decide
theorem Internal.SnakyRows008C.containment_557_1 :
    placedSet 4 (-2, 0) envelope_460 ⊆ envelope_557 := by decide
theorem Internal.SnakyRows008C.containment_557_2 :
    placedSet 2 (1, 0) envelope_460 ⊆ envelope_557 := by decide
theorem Internal.SnakyRows008C.containment_557_3 :
    placedSet 4 (1, 0) envelope_411 ⊆ envelope_557 := by decide
theorem Internal.SnakyRows008C.containment_557_4 :
    placedSet 0 (-1, 2) envelope_531 ⊆ envelope_557 := by decide +kernel
theorem Internal.SnakyRows008C.containment_557_5 :
    placedSet 4 (0, 2) envelope_531 ⊆ envelope_557 := by decide
theorem Internal.SnakyRows008C.containment_557_6 :
    placedSet 5 (1, 0) envelope_406 ⊆ envelope_557 := by decide
theorem child_envelope_sub_557 : ∀ j, childrenD_557 j ⊆ envelope_557 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_557_0
  · exact Internal.SnakyRows008C.containment_557_1
  · exact Internal.SnakyRows008C.containment_557_2
  · exact Internal.SnakyRows008C.containment_557_3
  · exact Internal.SnakyRows008C.containment_557_4
  · exact Internal.SnakyRows008C.containment_557_5
  · exact Internal.SnakyRows008C.containment_557_6
theorem pivot_mem_557 : (0, 0) ∈ envelope_557 := by decide
theorem children_work_557 : ∀ j, Template HasSnaky 18 (childrenC_557 j) (childrenD_557 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_460 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_460 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_460 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_411 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_531 0 (-1, 2)).mono (by decide)
  · exact (placed_template_map row_works_531 4 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_406 5 (1, 0)).mono (by decide)
theorem row_works_557 : Template HasSnaky 19 required_557 envelope_557 := by
  refine compose HasSnaky 18 childrenC_557 childrenD_557 children_work_557 (0, 0)
    required_557 envelope_557 pivot_mem_557 child_required_sub_557 child_envelope_sub_557 ?_
  intro b hb; exact common_sub_557 (mem_commonEnvelope childrenD_557 b hb)
end SnakyConditional

end OAI
