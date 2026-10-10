import OAI.GameTheory.SnakyConditional.Templates.Level13Part01
import OAI.GameTheory.SnakyConditional.Templates.Level13Part02

namespace OAI

namespace SnakyConditional
def required_353 : Finset Cell := ⟨(([(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_353 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_353 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_6), (placedSet 0 (-3, -1) required_347)]
def childrenD_353 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_6), (placedSet 0 (-3, -1) envelope_347)]
theorem common_sub_353 : commonEnvelope childrenD_353 ⊆ insert (0, 0) required_353 := by decide
theorem child_required_sub_353 : ∀ j, childrenC_353 j ⊆ insert (0, 0) required_353 := by decide
theorem child_envelope_sub_353 : ∀ j, childrenD_353 j ⊆ envelope_353 := by decide
theorem pivot_mem_353 : (0, 0) ∈ envelope_353 := by decide
theorem children_work_353 : ∀ j, Template HasSnaky 11 (childrenC_353 j) (childrenD_353 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_347 0 (-3, -1)).mono (by decide)
theorem row_works_353 : Template HasSnaky 12 required_353 envelope_353 := by
  refine compose HasSnaky 11 childrenC_353 childrenD_353 children_work_353 (0, 0)
    required_353 envelope_353 pivot_mem_353 child_required_sub_353 child_envelope_sub_353 ?_
  intro b hb; exact common_sub_353 (mem_commonEnvelope childrenD_353 b hb)
def required_361 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -1), (2, -1), (3, -1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_361 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_361 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (0, 1) required_352)]
def childrenD_361 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (0, 1) envelope_352)]
theorem common_sub_361 : commonEnvelope childrenD_361 ⊆ insert (0, 0) required_361 := by decide
theorem child_required_sub_361 : ∀ j, childrenC_361 j ⊆ insert (0, 0) required_361 := by decide
theorem child_envelope_sub_361 : ∀ j, childrenD_361 j ⊆ envelope_361 := by decide
theorem pivot_mem_361 : (0, 0) ∈ envelope_361 := by decide
theorem children_work_361 : ∀ j, Template HasSnaky 11 (childrenC_361 j) (childrenD_361 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_352 0 (0, 1)).mono (by decide)
theorem row_works_361 : Template HasSnaky 12 required_361 envelope_361 := by
  refine compose HasSnaky 11 childrenC_361 childrenD_361 children_work_361 (0, 0)
    required_361 envelope_361 pivot_mem_361 child_required_sub_361 child_envelope_sub_361 ?_
  intro b hb; exact common_sub_361 (mem_commonEnvelope childrenD_361 b hb)
def required_365 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_365 : Finset Cell := ⟨(([(-3, -1), (-2, -2), (-2, -1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_365 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (0, -1) required_354)]
def childrenD_365 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (0, -1) envelope_354)]
theorem common_sub_365 : commonEnvelope childrenD_365 ⊆ insert (0, 0) required_365 := by decide
theorem child_required_sub_365 : ∀ j, childrenC_365 j ⊆ insert (0, 0) required_365 := by decide
theorem child_envelope_sub_365 : ∀ j, childrenD_365 j ⊆ envelope_365 := by decide
theorem pivot_mem_365 : (0, 0) ∈ envelope_365 := by decide
theorem children_work_365 : ∀ j, Template HasSnaky 11 (childrenC_365 j) (childrenD_365 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_354 0 (0, -1)).mono (by decide)
theorem row_works_365 : Template HasSnaky 12 required_365 envelope_365 := by
  refine compose HasSnaky 11 childrenC_365 childrenD_365 children_work_365 (0, 0)
    required_365 envelope_365 pivot_mem_365 child_required_sub_365 child_envelope_sub_365 ?_
  intro b hb; exact common_sub_365 (mem_commonEnvelope childrenD_365 b hb)
def required_368 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_368 : Finset Cell := ⟨(([(-4, -3), (-3, -3), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_368 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (-2, 0) required_366)]
def childrenD_368 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (-2, 0) envelope_366)]
theorem common_sub_368 : commonEnvelope childrenD_368 ⊆ insert (0, 0) required_368 := by decide
theorem child_required_sub_368 : ∀ j, childrenC_368 j ⊆ insert (0, 0) required_368 := by decide
theorem child_envelope_sub_368 : ∀ j, childrenD_368 j ⊆ envelope_368 := by decide
theorem pivot_mem_368 : (0, 0) ∈ envelope_368 := by decide
theorem children_work_368 : ∀ j, Template HasSnaky 11 (childrenC_368 j) (childrenD_368 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_366 0 (-2, 0)).mono (by decide)
theorem row_works_368 : Template HasSnaky 12 required_368 envelope_368 := by
  refine compose HasSnaky 11 childrenC_368 childrenD_368 children_work_368 (0, 0)
    required_368 envelope_368 pivot_mem_368 child_required_sub_368 child_envelope_sub_368 ?_
  intro b hb; exact common_sub_368 (mem_commonEnvelope childrenD_368 b hb)
end SnakyConditional

end OAI
