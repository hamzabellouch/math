import OAI.GameTheory.SnakyConditional.Templates.Level11Part03
import OAI.GameTheory.SnakyConditional.Templates.Level11Part04

namespace OAI

namespace SnakyConditional
def required_332 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_332 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -4), (5, -3), (5, -2), (6, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_332 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_67), (placedSet 2 (1, -3) required_289)]
def childrenD_332 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_67), (placedSet 2 (1, -3) envelope_289)]
theorem common_sub_332 : commonEnvelope childrenD_332 ⊆ insert (0, 0) required_332 := by decide
theorem child_required_sub_332 : ∀ j, childrenC_332 j ⊆ insert (0, 0) required_332 := by decide
theorem child_envelope_sub_332 : ∀ j, childrenD_332 j ⊆ envelope_332 := by decide
theorem pivot_mem_332 : (0, 0) ∈ envelope_332 := by decide
theorem children_work_332 : ∀ j, Template HasSnaky 9 (childrenC_332 j) (childrenD_332 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_67 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_289 2 (1, -3)).mono (by decide)
theorem row_works_332 : Template HasSnaky 10 required_332 envelope_332 := by
  refine compose HasSnaky 9 childrenC_332 childrenD_332 children_work_332 (0, 0)
    required_332 envelope_332 pivot_mem_332 child_required_sub_332 child_envelope_sub_332 ?_
  intro b hb; exact common_sub_332 (mem_commonEnvelope childrenD_332 b hb)
def required_333 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, -4), (1, -3), (1, -2), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_333 : Finset Cell := ⟨(([(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_333 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_317), (placedSet 5 (0, -1) required_1)]
def childrenD_333 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_317), (placedSet 5 (0, -1) envelope_1)]
theorem common_sub_333 : commonEnvelope childrenD_333 ⊆ insert (0, 0) required_333 := by decide
theorem child_required_sub_333 : ∀ j, childrenC_333 j ⊆ insert (0, 0) required_333 := by decide
theorem child_envelope_sub_333 : ∀ j, childrenD_333 j ⊆ envelope_333 := by decide
theorem pivot_mem_333 : (0, 0) ∈ envelope_333 := by decide
theorem children_work_333 : ∀ j, Template HasSnaky 9 (childrenC_333 j) (childrenD_333 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_317 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_1 5 (0, -1)).mono (by decide)
theorem row_works_333 : Template HasSnaky 10 required_333 envelope_333 := by
  refine compose HasSnaky 9 childrenC_333 childrenD_333 children_work_333 (0, 0)
    required_333 envelope_333 pivot_mem_333 child_required_sub_333 child_envelope_sub_333 ?_
  intro b hb; exact common_sub_333 (mem_commonEnvelope childrenD_333 b hb)
def required_334 : Finset Cell := ⟨(([(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_334 : Finset Cell := ⟨(([(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_334 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, -2) required_67), (placedSet 0 (1, 1) required_289)]
def childrenD_334 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, -2) envelope_67), (placedSet 0 (1, 1) envelope_289)]
theorem common_sub_334 : commonEnvelope childrenD_334 ⊆ insert (0, 0) required_334 := by decide
theorem child_required_sub_334 : ∀ j, childrenC_334 j ⊆ insert (0, 0) required_334 := by decide
theorem child_envelope_sub_334 : ∀ j, childrenD_334 j ⊆ envelope_334 := by decide
theorem pivot_mem_334 : (0, 0) ∈ envelope_334 := by decide
theorem children_work_334 : ∀ j, Template HasSnaky 9 (childrenC_334 j) (childrenD_334 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_67 6 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_289 0 (1, 1)).mono (by decide)
theorem row_works_334 : Template HasSnaky 10 required_334 envelope_334 := by
  refine compose HasSnaky 9 childrenC_334 childrenD_334 children_work_334 (0, 0)
    required_334 envelope_334 pivot_mem_334 child_required_sub_334 child_envelope_sub_334 ?_
  intro b hb; exact common_sub_334 (mem_commonEnvelope childrenD_334 b hb)
def required_339 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_339 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (4, -4), (4, -2), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_339 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_4), (placedSet 0 (2, 0) required_322)]
def childrenD_339 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_4), (placedSet 0 (2, 0) envelope_322)]
theorem common_sub_339 : commonEnvelope childrenD_339 ⊆ insert (0, 0) required_339 := by decide
theorem child_required_sub_339 : ∀ j, childrenC_339 j ⊆ insert (0, 0) required_339 := by decide
theorem child_envelope_sub_339 : ∀ j, childrenD_339 j ⊆ envelope_339 := by decide
theorem pivot_mem_339 : (0, 0) ∈ envelope_339 := by decide
theorem children_work_339 : ∀ j, Template HasSnaky 9 (childrenC_339 j) (childrenD_339 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_322 0 (2, 0)).mono (by decide)
theorem row_works_339 : Template HasSnaky 10 required_339 envelope_339 := by
  refine compose HasSnaky 9 childrenC_339 childrenD_339 children_work_339 (0, 0)
    required_339 envelope_339 pivot_mem_339 child_required_sub_339 child_envelope_sub_339 ?_
  intro b hb; exact common_sub_339 (mem_commonEnvelope childrenD_339 b hb)
def required_340 : Finset Cell := ⟨(([(-1, 1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_340 : Finset Cell := ⟨(([(-4, -2), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_340 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 2) required_25), (placedSet 4 (0, 2) required_300), (placedSet 3 (-1, 2) required_24)]
def childrenD_340 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 2) envelope_25), (placedSet 4 (0, 2) envelope_300), (placedSet 3 (-1, 2) envelope_24)]
theorem common_sub_340 : commonEnvelope childrenD_340 ⊆ insert (0, 0) required_340 := by decide
theorem child_required_sub_340 : ∀ j, childrenC_340 j ⊆ insert (0, 0) required_340 := by decide
theorem child_envelope_sub_340 : ∀ j, childrenD_340 j ⊆ envelope_340 := by decide
theorem pivot_mem_340 : (0, 0) ∈ envelope_340 := by decide
theorem children_work_340 : ∀ j, Template HasSnaky 9 (childrenC_340 j) (childrenD_340 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 3 (-1, 2)).mono (by decide)
  · exact (placed_template_map row_works_300 4 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_24 3 (-1, 2)).mono (by decide)
theorem row_works_340 : Template HasSnaky 10 required_340 envelope_340 := by
  refine compose HasSnaky 9 childrenC_340 childrenD_340 children_work_340 (0, 0)
    required_340 envelope_340 pivot_mem_340 child_required_sub_340 child_envelope_sub_340 ?_
  intro b hb; exact common_sub_340 (mem_commonEnvelope childrenD_340 b hb)
end SnakyConditional

end OAI
