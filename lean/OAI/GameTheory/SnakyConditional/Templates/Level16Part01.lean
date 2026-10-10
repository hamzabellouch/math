import OAI.GameTheory.SnakyConditional.Templates.Level15Part01
import OAI.GameTheory.SnakyConditional.Templates.Level15Part02

namespace OAI

namespace SnakyConditional
def required_369 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_369 : Finset Cell := ⟨(([(-4, -2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_369 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 4 (-3, -2) required_367)]
def childrenD_369 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 4 (-3, -2) envelope_367)]
theorem common_sub_369 : commonEnvelope childrenD_369 ⊆ insert (0, 0) required_369 := by decide
theorem child_required_sub_369 : ∀ j, childrenC_369 j ⊆ insert (0, 0) required_369 := by decide
theorem child_envelope_sub_369 : ∀ j, childrenD_369 j ⊆ envelope_369 := by decide
theorem pivot_mem_369 : (0, 0) ∈ envelope_369 := by decide
theorem children_work_369 : ∀ j, Template HasSnaky 13 (childrenC_369 j) (childrenD_369 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_367 4 (-3, -2)).mono (by decide)
theorem row_works_369 : Template HasSnaky 14 required_369 envelope_369 := by
  refine compose HasSnaky 13 childrenC_369 childrenD_369 children_work_369 (0, 0)
    required_369 envelope_369 pivot_mem_369 child_required_sub_369 child_envelope_sub_369 ?_
  intro b hb; exact common_sub_369 (mem_commonEnvelope childrenD_369 b hb)
def required_410 : Finset Cell := ⟨(([(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_410 : Finset Cell := ⟨(([(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_410 : Fin 2 → Finset Cell := ![(placedSet 4 (1, 0) required_0), (placedSet 0 (-1, 3) required_405)]
def childrenD_410 : Fin 2 → Finset Cell := ![(placedSet 4 (1, 0) envelope_0), (placedSet 0 (-1, 3) envelope_405)]
theorem common_sub_410 : commonEnvelope childrenD_410 ⊆ insert (0, 0) required_410 := by decide
theorem child_required_sub_410 : ∀ j, childrenC_410 j ⊆ insert (0, 0) required_410 := by decide
theorem child_envelope_sub_410 : ∀ j, childrenD_410 j ⊆ envelope_410 := by decide
theorem pivot_mem_410 : (0, 0) ∈ envelope_410 := by decide
theorem children_work_410 : ∀ j, Template HasSnaky 13 (childrenC_410 j) (childrenD_410 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_405 0 (-1, 3)).mono (by decide)
theorem row_works_410 : Template HasSnaky 14 required_410 envelope_410 := by
  refine compose HasSnaky 13 childrenC_410 childrenD_410 children_work_410 (0, 0)
    required_410 envelope_410 pivot_mem_410 child_required_sub_410 child_envelope_sub_410 ?_
  intro b hb; exact common_sub_410 (mem_commonEnvelope childrenD_410 b hb)
def required_411 : Finset Cell := ⟨(([(1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_411 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_411 : Fin 6 → Finset Cell := ![(placedSet 0 (3, 0) required_252), (placedSet 0 (3, 0) required_263), (placedSet 3 (-1, 0) required_300), (placedSet 1 (3, 0) required_379), (placedSet 0 (3, 0) required_173), (placedSet 0 (3, 0) required_246)]
def childrenD_411 : Fin 6 → Finset Cell := ![(placedSet 0 (3, 0) envelope_252), (placedSet 0 (3, 0) envelope_263), (placedSet 3 (-1, 0) envelope_300), (placedSet 1 (3, 0) envelope_379), (placedSet 0 (3, 0) envelope_173), (placedSet 0 (3, 0) envelope_246)]
theorem common_sub_411 : commonEnvelope childrenD_411 ⊆ insert (0, 0) required_411 := by decide
theorem child_required_sub_411 : ∀ j, childrenC_411 j ⊆ insert (0, 0) required_411 := by decide
theorem child_envelope_sub_411 : ∀ j, childrenD_411 j ⊆ envelope_411 := by decide
theorem pivot_mem_411 : (0, 0) ∈ envelope_411 := by decide
theorem children_work_411 : ∀ j, Template HasSnaky 13 (childrenC_411 j) (childrenD_411 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_252 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_263 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_300 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_379 1 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_173 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_246 0 (3, 0)).mono (by decide)
theorem row_works_411 : Template HasSnaky 14 required_411 envelope_411 := by
  refine compose HasSnaky 13 childrenC_411 childrenD_411 children_work_411 (0, 0)
    required_411 envelope_411 pivot_mem_411 child_required_sub_411 child_envelope_sub_411 ?_
  intro b hb; exact common_sub_411 (mem_commonEnvelope childrenD_411 b hb)
end SnakyConditional

end OAI
