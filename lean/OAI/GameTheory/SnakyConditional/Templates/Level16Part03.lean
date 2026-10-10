import OAI.GameTheory.SnakyConditional.Templates.Level14Part01
import OAI.GameTheory.SnakyConditional.Templates.Level15Part02
import OAI.GameTheory.SnakyConditional.Templates.Level15Part03
import OAI.GameTheory.SnakyConditional.Templates.Level15Part04

namespace OAI

namespace SnakyConditional
def required_435 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_435 : Finset Cell := ⟨(([(-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_435 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (1, 2) required_431)]
def childrenD_435 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (1, 2) envelope_431)]
theorem common_sub_435 : commonEnvelope childrenD_435 ⊆ insert (0, 0) required_435 := by decide
theorem child_required_sub_435 : ∀ j, childrenC_435 j ⊆ insert (0, 0) required_435 := by decide
theorem child_envelope_sub_435 : ∀ j, childrenD_435 j ⊆ envelope_435 := by decide
theorem pivot_mem_435 : (0, 0) ∈ envelope_435 := by decide
theorem children_work_435 : ∀ j, Template HasSnaky 13 (childrenC_435 j) (childrenD_435 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_431 0 (1, 2)).mono (by decide)
theorem row_works_435 : Template HasSnaky 14 required_435 envelope_435 := by
  refine compose HasSnaky 13 childrenC_435 childrenD_435 children_work_435 (0, 0)
    required_435 envelope_435 pivot_mem_435 child_required_sub_435 child_envelope_sub_435 ?_
  intro b hb; exact common_sub_435 (mem_commonEnvelope childrenD_435 b hb)
def required_444 : Finset Cell := ⟨(([(-2, -2), (-1, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_444 : Finset Cell := ⟨(([(-5, -3), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_444 : Fin 6 → Finset Cell := ![(placedSet 0 (1, -1) required_194), (placedSet 3 (0, -3) required_160), (placedSet 7 (0, -3) required_142), (placedSet 0 (1, 1) required_236), (placedSet 4 (-3, -2) required_353), (placedSet 0 (1, -1) required_412)]
def childrenD_444 : Fin 6 → Finset Cell := ![(placedSet 0 (1, -1) envelope_194), (placedSet 3 (0, -3) envelope_160), (placedSet 7 (0, -3) envelope_142), (placedSet 0 (1, 1) envelope_236), (placedSet 4 (-3, -2) envelope_353), (placedSet 0 (1, -1) envelope_412)]
theorem common_sub_444 : commonEnvelope childrenD_444 ⊆ insert (0, 0) required_444 := by decide
theorem child_required_sub_444 : ∀ j, childrenC_444 j ⊆ insert (0, 0) required_444 := by decide
theorem child_envelope_sub_444 : ∀ j, childrenD_444 j ⊆ envelope_444 := by decide
theorem pivot_mem_444 : (0, 0) ∈ envelope_444 := by decide
theorem children_work_444 : ∀ j, Template HasSnaky 13 (childrenC_444 j) (childrenD_444 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_194 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_160 3 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_142 7 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_236 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_353 4 (-3, -2)).mono (by decide)
  · exact (placed_template_map row_works_412 0 (1, -1)).mono (by decide)
theorem row_works_444 : Template HasSnaky 14 required_444 envelope_444 := by
  refine compose HasSnaky 13 childrenC_444 childrenD_444 children_work_444 (0, 0)
    required_444 envelope_444 pivot_mem_444 child_required_sub_444 child_envelope_sub_444 ?_
  intro b hb; exact common_sub_444 (mem_commonEnvelope childrenD_444 b hb)
def required_466 : Finset Cell := ⟨(([(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_466 : Finset Cell := ⟨(([(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_466 : Fin 5 → Finset Cell := ![(placedSet 4 (-1, 0) required_395), (placedSet 4 (-2, 2) required_360), (placedSet 1 (1, 0) required_417), (placedSet 4 (-1, 0) required_325), (placedSet 4 (-1, 1) required_324)]
def childrenD_466 : Fin 5 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_395), (placedSet 4 (-2, 2) envelope_360), (placedSet 1 (1, 0) envelope_417), (placedSet 4 (-1, 0) envelope_325), (placedSet 4 (-1, 1) envelope_324)]
theorem common_sub_466 : commonEnvelope childrenD_466 ⊆ insert (0, 0) required_466 := by decide
theorem child_required_sub_466 : ∀ j, childrenC_466 j ⊆ insert (0, 0) required_466 := by decide
theorem child_envelope_sub_466 : ∀ j, childrenD_466 j ⊆ envelope_466 := by decide
theorem pivot_mem_466 : (0, 0) ∈ envelope_466 := by decide
theorem children_work_466 : ∀ j, Template HasSnaky 13 (childrenC_466 j) (childrenD_466 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_395 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_360 4 (-2, 2)).mono (by decide)
  · exact (placed_template_map row_works_417 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_325 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_324 4 (-1, 1)).mono (by decide)
theorem row_works_466 : Template HasSnaky 14 required_466 envelope_466 := by
  refine compose HasSnaky 13 childrenC_466 childrenD_466 children_work_466 (0, 0)
    required_466 envelope_466 pivot_mem_466 child_required_sub_466 child_envelope_sub_466 ?_
  intro b hb; exact common_sub_466 (mem_commonEnvelope childrenD_466 b hb)
end SnakyConditional

end OAI
