import OAI.GameTheory.SnakyConditional.Templates.Level15Part02
import OAI.GameTheory.SnakyConditional.Templates.Level15Part03

namespace OAI

namespace SnakyConditional
def required_418 : Finset Cell := ⟨(([(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_418 : Finset Cell := ⟨(([(-5, 0), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_418 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, -1) required_68), (placedSet 6 (-3, -1) required_62), (placedSet 6 (-3, -1) required_147), (placedSet 0 (0, -2) required_413)]
def childrenD_418 : Fin 4 → Finset Cell := ![(placedSet 4 (-3, -1) envelope_68), (placedSet 6 (-3, -1) envelope_62), (placedSet 6 (-3, -1) envelope_147), (placedSet 0 (0, -2) envelope_413)]
theorem common_sub_418 : commonEnvelope childrenD_418 ⊆ insert (0, 0) required_418 := by decide
theorem child_required_sub_418 : ∀ j, childrenC_418 j ⊆ insert (0, 0) required_418 := by decide
theorem child_envelope_sub_418 : ∀ j, childrenD_418 j ⊆ envelope_418 := by decide
theorem pivot_mem_418 : (0, 0) ∈ envelope_418 := by decide
theorem children_work_418 : ∀ j, Template HasSnaky 13 (childrenC_418 j) (childrenD_418 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_68 4 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_62 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_147 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_413 0 (0, -2)).mono (by decide)
theorem row_works_418 : Template HasSnaky 14 required_418 envelope_418 := by
  refine compose HasSnaky 13 childrenC_418 childrenD_418 children_work_418 (0, 0)
    required_418 envelope_418 pivot_mem_418 child_required_sub_418 child_envelope_sub_418 ?_
  intro b hb; exact common_sub_418 (mem_commonEnvelope childrenD_418 b hb)
def required_422 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_422 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_422 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, 3) required_45), (placedSet 6 (-2, -1) required_106), (placedSet 1 (2, 2) required_419)]
def childrenD_422 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, 3) envelope_45), (placedSet 6 (-2, -1) envelope_106), (placedSet 1 (2, 2) envelope_419)]
theorem common_sub_422 : commonEnvelope childrenD_422 ⊆ insert (0, 0) required_422 := by decide
theorem child_required_sub_422 : ∀ j, childrenC_422 j ⊆ insert (0, 0) required_422 := by decide
theorem child_envelope_sub_422 : ∀ j, childrenD_422 j ⊆ envelope_422 := by decide
theorem pivot_mem_422 : (0, 0) ∈ envelope_422 := by decide
theorem children_work_422 : ∀ j, Template HasSnaky 13 (childrenC_422 j) (childrenD_422 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_45 1 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_106 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_419 1 (2, 2)).mono (by decide)
theorem row_works_422 : Template HasSnaky 14 required_422 envelope_422 := by
  refine compose HasSnaky 13 childrenC_422 childrenD_422 children_work_422 (0, 0)
    required_422 envelope_422 pivot_mem_422 child_required_sub_422 child_envelope_sub_422 ?_
  intro b hb; exact common_sub_422 (mem_commonEnvelope childrenD_422 b hb)
def required_427 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_427 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_427 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, 3) required_45), (placedSet 6 (-2, -1) required_106), (placedSet 1 (2, 0) required_420)]
def childrenD_427 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, 3) envelope_45), (placedSet 6 (-2, -1) envelope_106), (placedSet 1 (2, 0) envelope_420)]
theorem common_sub_427 : commonEnvelope childrenD_427 ⊆ insert (0, 0) required_427 := by decide
theorem child_required_sub_427 : ∀ j, childrenC_427 j ⊆ insert (0, 0) required_427 := by decide
theorem child_envelope_sub_427 : ∀ j, childrenD_427 j ⊆ envelope_427 := by decide
theorem pivot_mem_427 : (0, 0) ∈ envelope_427 := by decide
theorem children_work_427 : ∀ j, Template HasSnaky 13 (childrenC_427 j) (childrenD_427 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_45 1 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_106 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_420 1 (2, 0)).mono (by decide)
theorem row_works_427 : Template HasSnaky 14 required_427 envelope_427 := by
  refine compose HasSnaky 13 childrenC_427 childrenD_427 children_work_427 (0, 0)
    required_427 envelope_427 pivot_mem_427 child_required_sub_427 child_envelope_sub_427 ?_
  intro b hb; exact common_sub_427 (mem_commonEnvelope childrenD_427 b hb)
end SnakyConditional

end OAI
