import OAI.GameTheory.SnakyConditional.Templates.Level13Part02
import OAI.GameTheory.SnakyConditional.Templates.Level13Part03

namespace OAI

namespace SnakyConditional
def required_377 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_377 : Finset Cell := ⟨(([(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_377 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) required_29), (placedSet 0 (3, -2) required_362)]
def childrenD_377 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) envelope_29), (placedSet 0 (3, -2) envelope_362)]
theorem common_sub_377 : commonEnvelope childrenD_377 ⊆ insert (0, 0) required_377 := by decide
theorem child_required_sub_377 : ∀ j, childrenC_377 j ⊆ insert (0, 0) required_377 := by decide
theorem child_envelope_sub_377 : ∀ j, childrenD_377 j ⊆ envelope_377 := by decide
theorem pivot_mem_377 : (0, 0) ∈ envelope_377 := by decide
theorem children_work_377 : ∀ j, Template HasSnaky 11 (childrenC_377 j) (childrenD_377 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_29 3 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_362 0 (3, -2)).mono (by decide)
theorem row_works_377 : Template HasSnaky 12 required_377 envelope_377 := by
  refine compose HasSnaky 11 childrenC_377 childrenD_377 children_work_377 (0, 0)
    required_377 envelope_377 pivot_mem_377 child_required_sub_377 child_envelope_sub_377 ?_
  intro b hb; exact common_sub_377 (mem_commonEnvelope childrenD_377 b hb)
def required_387 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_387 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_387 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 2) required_14), (placedSet 0 (1, 0) required_370)]
def childrenD_387 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 2) envelope_14), (placedSet 0 (1, 0) envelope_370)]
theorem common_sub_387 : commonEnvelope childrenD_387 ⊆ insert (0, 0) required_387 := by decide
theorem child_required_sub_387 : ∀ j, childrenC_387 j ⊆ insert (0, 0) required_387 := by decide
theorem child_envelope_sub_387 : ∀ j, childrenD_387 j ⊆ envelope_387 := by decide
theorem pivot_mem_387 : (0, 0) ∈ envelope_387 := by decide
theorem children_work_387 : ∀ j, Template HasSnaky 11 (childrenC_387 j) (childrenD_387 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_14 1 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_370 0 (1, 0)).mono (by decide)
theorem row_works_387 : Template HasSnaky 12 required_387 envelope_387 := by
  refine compose HasSnaky 11 childrenC_387 childrenD_387 children_work_387 (0, 0)
    required_387 envelope_387 pivot_mem_387 child_required_sub_387 child_envelope_sub_387 ?_
  intro b hb; exact common_sub_387 (mem_commonEnvelope childrenD_387 b hb)
def required_390 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_390 : Finset Cell := ⟨(([(-4, -5), (-3, -5), (-3, -4), (-2, -5), (-2, -4), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -5), (2, -4), (2, -2), (3, -5), (3, -4), (3, -3), (3, -2), (4, -5), (4, -4), (4, -3), (5, -5), (5, -4), (5, -3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_390 : Fin 3 → Finset Cell := ![(placedSet 2 (1, -4) required_372), (placedSet 5 (0, -3) required_167), (placedSet 7 (-1, -3) required_12)]
def childrenD_390 : Fin 3 → Finset Cell := ![(placedSet 2 (1, -4) envelope_372), (placedSet 5 (0, -3) envelope_167), (placedSet 7 (-1, -3) envelope_12)]
theorem common_sub_390 : commonEnvelope childrenD_390 ⊆ insert (0, 0) required_390 := by decide
theorem child_required_sub_390 : ∀ j, childrenC_390 j ⊆ insert (0, 0) required_390 := by decide
theorem child_envelope_sub_390 : ∀ j, childrenD_390 j ⊆ envelope_390 := by decide
theorem pivot_mem_390 : (0, 0) ∈ envelope_390 := by decide
theorem children_work_390 : ∀ j, Template HasSnaky 11 (childrenC_390 j) (childrenD_390 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_372 2 (1, -4)).mono (by decide)
  · exact (placed_template_map row_works_167 5 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_12 7 (-1, -3)).mono (by decide)
theorem row_works_390 : Template HasSnaky 12 required_390 envelope_390 := by
  refine compose HasSnaky 11 childrenC_390 childrenD_390 children_work_390 (0, 0)
    required_390 envelope_390 pivot_mem_390 child_required_sub_390 child_envelope_sub_390 ?_
  intro b hb; exact common_sub_390 (mem_commonEnvelope childrenD_390 b hb)
def required_391 : Finset Cell := ⟨(([(-1, -1), (0, -2), (0, -1), (0, 1), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_391 : Finset Cell := ⟨(([(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_391 : Fin 2 → Finset Cell := ![(placedSet 5 (1, -3) required_6), (placedSet 0 (-1, 1) required_388)]
def childrenD_391 : Fin 2 → Finset Cell := ![(placedSet 5 (1, -3) envelope_6), (placedSet 0 (-1, 1) envelope_388)]
theorem common_sub_391 : commonEnvelope childrenD_391 ⊆ insert (0, 0) required_391 := by decide
theorem child_required_sub_391 : ∀ j, childrenC_391 j ⊆ insert (0, 0) required_391 := by decide
theorem child_envelope_sub_391 : ∀ j, childrenD_391 j ⊆ envelope_391 := by decide
theorem pivot_mem_391 : (0, 0) ∈ envelope_391 := by decide
theorem children_work_391 : ∀ j, Template HasSnaky 11 (childrenC_391 j) (childrenD_391 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 5 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_388 0 (-1, 1)).mono (by decide)
theorem row_works_391 : Template HasSnaky 12 required_391 envelope_391 := by
  refine compose HasSnaky 11 childrenC_391 childrenD_391 children_work_391 (0, 0)
    required_391 envelope_391 pivot_mem_391 child_required_sub_391 child_envelope_sub_391 ?_
  intro b hb; exact common_sub_391 (mem_commonEnvelope childrenD_391 b hb)
end SnakyConditional

end OAI
