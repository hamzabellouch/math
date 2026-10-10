import OAI.GameTheory.SnakyConditional.Templates.Level12Part01
import OAI.GameTheory.SnakyConditional.Templates.Level12Part02
import OAI.GameTheory.SnakyConditional.Templates.Level12Part04

namespace OAI

namespace SnakyConditional
def required_308 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_308 : Finset Cell := ⟨(([(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_308 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 0 (0, 2) required_299)]
def childrenD_308 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 0 (0, 2) envelope_299)]
theorem common_sub_308 : commonEnvelope childrenD_308 ⊆ insert (0, 0) required_308 := by decide
theorem child_required_sub_308 : ∀ j, childrenC_308 j ⊆ insert (0, 0) required_308 := by decide
theorem child_envelope_sub_308 : ∀ j, childrenD_308 j ⊆ envelope_308 := by decide
theorem pivot_mem_308 : (0, 0) ∈ envelope_308 := by decide
theorem children_work_308 : ∀ j, Template HasSnaky 10 (childrenC_308 j) (childrenD_308 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_299 0 (0, 2)).mono (by decide)
theorem row_works_308 : Template HasSnaky 11 required_308 envelope_308 := by
  refine compose HasSnaky 10 childrenC_308 childrenD_308 children_work_308 (0, 0)
    required_308 envelope_308 pivot_mem_308 child_required_sub_308 child_envelope_sub_308 ?_
  intro b hb; exact common_sub_308 (mem_commonEnvelope childrenD_308 b hb)
def required_347 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_347 : Finset Cell := ⟨(([(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 1), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_347 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 0 (1, 4) required_339)]
def childrenD_347 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 0 (1, 4) envelope_339)]
theorem common_sub_347 : commonEnvelope childrenD_347 ⊆ insert (0, 0) required_347 := by decide
theorem child_required_sub_347 : ∀ j, childrenC_347 j ⊆ insert (0, 0) required_347 := by decide
theorem child_envelope_sub_347 : ∀ j, childrenD_347 j ⊆ envelope_347 := by decide
theorem pivot_mem_347 : (0, 0) ∈ envelope_347 := by decide
theorem children_work_347 : ∀ j, Template HasSnaky 10 (childrenC_347 j) (childrenD_347 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_339 0 (1, 4)).mono (by decide)
theorem row_works_347 : Template HasSnaky 11 required_347 envelope_347 := by
  refine compose HasSnaky 10 childrenC_347 childrenD_347 children_work_347 (0, 0)
    required_347 envelope_347 pivot_mem_347 child_required_sub_347 child_envelope_sub_347 ?_
  intro b hb; exact common_sub_347 (mem_commonEnvelope childrenD_347 b hb)
def required_348 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, -1), (0, -2), (0, -1), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_348 : Finset Cell := ⟨(([(-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_348 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 1) required_312), (placedSet 4 (-1, 0) required_114), (placedSet 3 (0, 1) required_139)]
def childrenD_348 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 1) envelope_312), (placedSet 4 (-1, 0) envelope_114), (placedSet 3 (0, 1) envelope_139)]
theorem common_sub_348 : commonEnvelope childrenD_348 ⊆ insert (0, 0) required_348 := by decide
theorem child_required_sub_348 : ∀ j, childrenC_348 j ⊆ insert (0, 0) required_348 := by decide
theorem child_envelope_sub_348 : ∀ j, childrenD_348 j ⊆ envelope_348 := by decide
theorem pivot_mem_348 : (0, 0) ∈ envelope_348 := by decide
theorem children_work_348 : ∀ j, Template HasSnaky 10 (childrenC_348 j) (childrenD_348 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_312 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_114 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_139 3 (0, 1)).mono (by decide)
theorem row_works_348 : Template HasSnaky 11 required_348 envelope_348 := by
  refine compose HasSnaky 10 childrenC_348 childrenD_348 children_work_348 (0, 0)
    required_348 envelope_348 pivot_mem_348 child_required_sub_348 child_envelope_sub_348 ?_
  intro b hb; exact common_sub_348 (mem_commonEnvelope childrenD_348 b hb)
def required_349 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_349 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, -4), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_349 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) required_14), (placedSet 1 (0, 1) required_17), (placedSet 0 (-1, 0) required_332)]
def childrenD_349 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) envelope_14), (placedSet 1 (0, 1) envelope_17), (placedSet 0 (-1, 0) envelope_332)]
theorem common_sub_349 : commonEnvelope childrenD_349 ⊆ insert (0, 0) required_349 := by decide
theorem child_required_sub_349 : ∀ j, childrenC_349 j ⊆ insert (0, 0) required_349 := by decide
theorem child_envelope_sub_349 : ∀ j, childrenD_349 j ⊆ envelope_349 := by decide
theorem pivot_mem_349 : (0, 0) ∈ envelope_349 := by decide
theorem children_work_349 : ∀ j, Template HasSnaky 10 (childrenC_349 j) (childrenD_349 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_14 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_17 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_332 0 (-1, 0)).mono (by decide)
theorem row_works_349 : Template HasSnaky 11 required_349 envelope_349 := by
  refine compose HasSnaky 10 childrenC_349 childrenD_349 children_work_349 (0, 0)
    required_349 envelope_349 pivot_mem_349 child_required_sub_349 child_envelope_sub_349 ?_
  intro b hb; exact common_sub_349 (mem_commonEnvelope childrenD_349 b hb)
def required_351 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_351 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_351 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_163), (placedSet 4 (-3, 0) required_287), (placedSet 4 (-3, 1) required_25)]
def childrenD_351 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_163), (placedSet 4 (-3, 0) envelope_287), (placedSet 4 (-3, 1) envelope_25)]
theorem common_sub_351 : commonEnvelope childrenD_351 ⊆ insert (0, 0) required_351 := by decide
theorem child_required_sub_351 : ∀ j, childrenC_351 j ⊆ insert (0, 0) required_351 := by decide
theorem child_envelope_sub_351 : ∀ j, childrenD_351 j ⊆ envelope_351 := by decide
theorem pivot_mem_351 : (0, 0) ∈ envelope_351 := by decide
theorem children_work_351 : ∀ j, Template HasSnaky 10 (childrenC_351 j) (childrenD_351 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_163 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_287 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_25 4 (-3, 1)).mono (by decide)
theorem row_works_351 : Template HasSnaky 11 required_351 envelope_351 := by
  refine compose HasSnaky 10 childrenC_351 childrenD_351 children_work_351 (0, 0)
    required_351 envelope_351 pivot_mem_351 child_required_sub_351 child_envelope_sub_351 ?_
  intro b hb; exact common_sub_351 (mem_commonEnvelope childrenD_351 b hb)
end SnakyConditional

end OAI
