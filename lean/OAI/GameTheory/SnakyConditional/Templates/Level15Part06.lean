import OAI.GameTheory.SnakyConditional.Templates.Level14Part02
import OAI.GameTheory.SnakyConditional.Templates.Level14Part06
import OAI.GameTheory.SnakyConditional.Templates.Level14Part07

namespace OAI

namespace SnakyConditional
def required_512 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 0), (-1, 2), (-1, 3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_512 : Finset Cell := ⟨(([(-4, 2), (-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 3), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_512 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_62), (placedSet 0 (1, 0) required_107), (placedSet 0 (0, 2) required_507)]
def childrenD_512 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_62), (placedSet 0 (1, 0) envelope_107), (placedSet 0 (0, 2) envelope_507)]
theorem common_sub_512 : commonEnvelope childrenD_512 ⊆ insert (0, 0) required_512 := by decide
theorem child_required_sub_512 : ∀ j, childrenC_512 j ⊆ insert (0, 0) required_512 := by decide
theorem child_envelope_sub_512 : ∀ j, childrenD_512 j ⊆ envelope_512 := by decide
theorem pivot_mem_512 : (0, 0) ∈ envelope_512 := by decide
theorem children_work_512 : ∀ j, Template HasSnaky 12 (childrenC_512 j) (childrenD_512 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_62 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_107 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_507 0 (0, 2)).mono (by decide)
theorem row_works_512 : Template HasSnaky 13 required_512 envelope_512 := by
  refine compose HasSnaky 12 childrenC_512 childrenD_512 children_work_512 (0, 0)
    required_512 envelope_512 pivot_mem_512 child_required_sub_512 child_envelope_sub_512 ?_
  intro b hb; exact common_sub_512 (mem_commonEnvelope childrenD_512 b hb)
def required_517 : Finset Cell := ⟨(([(-1, -3), (-1, -1), (0, -3), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_517 : Finset Cell := ⟨(([(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_517 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, -1) required_496), (placedSet 0 (0, -2) required_140), (placedSet 1 (0, -2) required_193)]
def childrenD_517 : Fin 3 → Finset Cell := ![(placedSet 0 (-2, -1) envelope_496), (placedSet 0 (0, -2) envelope_140), (placedSet 1 (0, -2) envelope_193)]
theorem common_sub_517 : commonEnvelope childrenD_517 ⊆ insert (0, 0) required_517 := by decide
theorem child_required_sub_517 : ∀ j, childrenC_517 j ⊆ insert (0, 0) required_517 := by decide
theorem child_envelope_sub_517 : ∀ j, childrenD_517 j ⊆ envelope_517 := by decide
theorem pivot_mem_517 : (0, 0) ∈ envelope_517 := by decide
theorem children_work_517 : ∀ j, Template HasSnaky 12 (childrenC_517 j) (childrenD_517 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_496 0 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_140 0 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_193 1 (0, -2)).mono (by decide)
theorem row_works_517 : Template HasSnaky 13 required_517 envelope_517 := by
  refine compose HasSnaky 12 childrenC_517 childrenD_517 children_work_517 (0, 0)
    required_517 envelope_517 pivot_mem_517 child_required_sub_517 child_envelope_sub_517 ?_
  intro b hb; exact common_sub_517 (mem_commonEnvelope childrenD_517 b hb)
def required_527 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_527 : Finset Cell := ⟨(([(-5, 1), (-4, -2), (-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (7, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_527 : Fin 4 → Finset Cell := ![(placedSet 4 (0, -1) required_387), (placedSet 3 (0, 1) required_38), (placedSet 0 (1, 0) required_491), (placedSet 0 (2, 0) required_519)]
def childrenD_527 : Fin 4 → Finset Cell := ![(placedSet 4 (0, -1) envelope_387), (placedSet 3 (0, 1) envelope_38), (placedSet 0 (1, 0) envelope_491), (placedSet 0 (2, 0) envelope_519)]
theorem common_sub_527 : commonEnvelope childrenD_527 ⊆ insert (0, 0) required_527 := by decide
theorem child_required_sub_527 : ∀ j, childrenC_527 j ⊆ insert (0, 0) required_527 := by decide
theorem child_envelope_sub_527 : ∀ j, childrenD_527 j ⊆ envelope_527 := by decide
theorem pivot_mem_527 : (0, 0) ∈ envelope_527 := by decide
theorem children_work_527 : ∀ j, Template HasSnaky 12 (childrenC_527 j) (childrenD_527 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_387 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_38 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_491 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_519 0 (2, 0)).mono (by decide)
theorem row_works_527 : Template HasSnaky 13 required_527 envelope_527 := by
  refine compose HasSnaky 12 childrenC_527 childrenD_527 children_work_527 (0, 0)
    required_527 envelope_527 pivot_mem_527 child_required_sub_527 child_envelope_sub_527 ?_
  intro b hb; exact common_sub_527 (mem_commonEnvelope childrenD_527 b hb)
end SnakyConditional

end OAI
