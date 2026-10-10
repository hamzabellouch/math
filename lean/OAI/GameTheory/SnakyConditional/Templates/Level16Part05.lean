import OAI.GameTheory.SnakyConditional.Templates.Level15Part01
import OAI.GameTheory.SnakyConditional.Templates.Level15Part04
import OAI.GameTheory.SnakyConditional.Templates.Level15Part06

namespace OAI

namespace SnakyConditional
def required_513 : Finset Cell := ⟨(([(0, -1), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_513 : Finset Cell := ⟨(([(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_513 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (0, 1) required_396)]
def childrenD_513 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (0, 1) envelope_396)]
theorem common_sub_513 : commonEnvelope childrenD_513 ⊆ insert (0, 0) required_513 := by decide
theorem child_required_sub_513 : ∀ j, childrenC_513 j ⊆ insert (0, 0) required_513 := by decide
theorem child_envelope_sub_513 : ∀ j, childrenD_513 j ⊆ envelope_513 := by decide
theorem pivot_mem_513 : (0, 0) ∈ envelope_513 := by decide
theorem children_work_513 : ∀ j, Template HasSnaky 13 (childrenC_513 j) (childrenD_513 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_396 0 (0, 1)).mono (by decide)
theorem row_works_513 : Template HasSnaky 14 required_513 envelope_513 := by
  refine compose HasSnaky 13 childrenC_513 childrenD_513 children_work_513 (0, 0)
    required_513 envelope_513 pivot_mem_513 child_required_sub_513 child_envelope_sub_513 ?_
  intro b hb; exact common_sub_513 (mem_commonEnvelope childrenD_513 b hb)
def required_515 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_515 : Finset Cell := ⟨(([(-4, -2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_515 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, 0) required_2), (placedSet 1 (-3, 1) required_512)]
def childrenD_515 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, 0) envelope_2), (placedSet 1 (-3, 1) envelope_512)]
theorem common_sub_515 : commonEnvelope childrenD_515 ⊆ insert (0, 0) required_515 := by decide
theorem child_required_sub_515 : ∀ j, childrenC_515 j ⊆ insert (0, 0) required_515 := by decide
theorem child_envelope_sub_515 : ∀ j, childrenD_515 j ⊆ envelope_515 := by decide
theorem pivot_mem_515 : (0, 0) ∈ envelope_515 := by decide
theorem children_work_515 : ∀ j, Template HasSnaky 13 (childrenC_515 j) (childrenD_515 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 6 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_512 1 (-3, 1)).mono (by decide)
theorem row_works_515 : Template HasSnaky 14 required_515 envelope_515 := by
  refine compose HasSnaky 13 childrenC_515 childrenD_515 children_work_515 (0, 0)
    required_515 envelope_515 pivot_mem_515 child_required_sub_515 child_envelope_sub_515 ?_
  intro b hb; exact common_sub_515 (mem_commonEnvelope childrenD_515 b hb)
def required_521 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (0, -3), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_521 : Finset Cell := ⟨(([(-6, 1), (-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (3, -1), (4, -4), (4, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_521 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -3) required_492), (placedSet 7 (0, -2) required_2)]
def childrenD_521 : Fin 2 → Finset Cell := ![(placedSet 4 (1, -3) envelope_492), (placedSet 7 (0, -2) envelope_2)]
theorem common_sub_521 : commonEnvelope childrenD_521 ⊆ insert (0, 0) required_521 := by decide
theorem child_required_sub_521 : ∀ j, childrenC_521 j ⊆ insert (0, 0) required_521 := by decide
theorem child_envelope_sub_521 : ∀ j, childrenD_521 j ⊆ envelope_521 := by decide
theorem pivot_mem_521 : (0, 0) ∈ envelope_521 := by decide
theorem children_work_521 : ∀ j, Template HasSnaky 13 (childrenC_521 j) (childrenD_521 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_492 4 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_2 7 (0, -2)).mono (by decide)
theorem row_works_521 : Template HasSnaky 14 required_521 envelope_521 := by
  refine compose HasSnaky 13 childrenC_521 childrenD_521 children_work_521 (0, 0)
    required_521 envelope_521 pivot_mem_521 child_required_sub_521 child_envelope_sub_521 ?_
  intro b hb; exact common_sub_521 (mem_commonEnvelope childrenD_521 b hb)
end SnakyConditional

end OAI
