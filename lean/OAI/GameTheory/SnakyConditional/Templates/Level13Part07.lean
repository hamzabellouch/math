import OAI.GameTheory.SnakyConditional.Templates.Level12Part03
import OAI.GameTheory.SnakyConditional.Templates.Level12Part07

namespace OAI

namespace SnakyConditional
def required_533 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_533 : Finset Cell := ⟨(([(-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, 0), (4, -4), (4, -3), (4, -2), (5, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_533 : Fin 5 → Finset Cell := ![(placedSet 4 (0, 1) required_318), (placedSet 7 (1, -3) required_319), (placedSet 4 (0, -3) required_407), (placedSet 3 (0, 1) required_173), (placedSet 1 (0, 1) required_217)]
def childrenD_533 : Fin 5 → Finset Cell := ![(placedSet 4 (0, 1) envelope_318), (placedSet 7 (1, -3) envelope_319), (placedSet 4 (0, -3) envelope_407), (placedSet 3 (0, 1) envelope_173), (placedSet 1 (0, 1) envelope_217)]
theorem common_sub_533 : commonEnvelope childrenD_533 ⊆ insert (0, 0) required_533 := by decide
theorem child_required_sub_533 : ∀ j, childrenC_533 j ⊆ insert (0, 0) required_533 := by decide
theorem child_envelope_sub_533 : ∀ j, childrenD_533 j ⊆ envelope_533 := by decide
theorem pivot_mem_533 : (0, 0) ∈ envelope_533 := by decide
theorem children_work_533 : ∀ j, Template HasSnaky 10 (childrenC_533 j) (childrenD_533 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_318 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_319 7 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_407 4 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_173 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_217 1 (0, 1)).mono (by decide)
theorem row_works_533 : Template HasSnaky 11 required_533 envelope_533 := by
  refine compose HasSnaky 10 childrenC_533 childrenD_533 children_work_533 (0, 0)
    required_533 envelope_533 pivot_mem_533 child_required_sub_533 child_envelope_sub_533 ?_
  intro b hb; exact common_sub_533 (mem_commonEnvelope childrenD_533 b hb)
def required_537 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_537 : Finset Cell := ⟨(([(-7, -2), (-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_537 : Fin 4 → Finset Cell := ![(placedSet 2 (-2, 0) required_373), (placedSet 3 (-1, -1) required_271), (placedSet 1 (0, 2) required_176), (placedSet 1 (0, 2) required_330)]
def childrenD_537 : Fin 4 → Finset Cell := ![(placedSet 2 (-2, 0) envelope_373), (placedSet 3 (-1, -1) envelope_271), (placedSet 1 (0, 2) envelope_176), (placedSet 1 (0, 2) envelope_330)]
theorem common_sub_537 : commonEnvelope childrenD_537 ⊆ insert (0, 0) required_537 := by decide
theorem child_required_sub_537 : ∀ j, childrenC_537 j ⊆ insert (0, 0) required_537 := by decide
theorem child_envelope_sub_537 : ∀ j, childrenD_537 j ⊆ envelope_537 := by decide
theorem pivot_mem_537 : (0, 0) ∈ envelope_537 := by decide
theorem children_work_537 : ∀ j, Template HasSnaky 10 (childrenC_537 j) (childrenD_537 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_373 2 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_271 3 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_176 1 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_330 1 (0, 2)).mono (by decide)
theorem row_works_537 : Template HasSnaky 11 required_537 envelope_537 := by
  refine compose HasSnaky 10 childrenC_537 childrenD_537 children_work_537 (0, 0)
    required_537 envelope_537 pivot_mem_537 child_required_sub_537 child_envelope_sub_537 ?_
  intro b hb; exact common_sub_537 (mem_commonEnvelope childrenD_537 b hb)
def required_543 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_543 : Finset Cell := ⟨(([(-6, 3), (-5, -1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_543 : Fin 3 → Finset Cell := ![(placedSet 3 (-2, 2) required_493), (placedSet 2 (1, 0) required_107), (placedSet 5 (1, 0) required_318)]
def childrenD_543 : Fin 3 → Finset Cell := ![(placedSet 3 (-2, 2) envelope_493), (placedSet 2 (1, 0) envelope_107), (placedSet 5 (1, 0) envelope_318)]
theorem common_sub_543 : commonEnvelope childrenD_543 ⊆ insert (0, 0) required_543 := by decide
theorem child_required_sub_543 : ∀ j, childrenC_543 j ⊆ insert (0, 0) required_543 := by decide
theorem child_envelope_sub_543 : ∀ j, childrenD_543 j ⊆ envelope_543 := by decide
theorem pivot_mem_543 : (0, 0) ∈ envelope_543 := by decide
theorem children_work_543 : ∀ j, Template HasSnaky 10 (childrenC_543 j) (childrenD_543 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_493 3 (-2, 2)).mono (by decide)
  · exact (placed_template_map row_works_107 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_318 5 (1, 0)).mono (by decide)
theorem row_works_543 : Template HasSnaky 11 required_543 envelope_543 := by
  refine compose HasSnaky 10 childrenC_543 childrenD_543 children_work_543 (0, 0)
    required_543 envelope_543 pivot_mem_543 child_required_sub_543 child_envelope_sub_543 ?_
  intro b hb; exact common_sub_543 (mem_commonEnvelope childrenD_543 b hb)
end SnakyConditional

end OAI
