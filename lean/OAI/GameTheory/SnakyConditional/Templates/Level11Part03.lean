import OAI.GameTheory.SnakyConditional.Templates.Level10Part01
import OAI.GameTheory.SnakyConditional.Templates.Level10Part02
import OAI.GameTheory.SnakyConditional.Templates.Level10Part04

namespace OAI

namespace SnakyConditional
def required_284 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_284 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_284 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) required_45), (placedSet 0 (1, 0) required_224), (placedSet 3 (0, 1) required_46)]
def childrenD_284 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) envelope_45), (placedSet 0 (1, 0) envelope_224), (placedSet 3 (0, 1) envelope_46)]
theorem common_sub_284 : commonEnvelope childrenD_284 ⊆ insert (0, 0) required_284 := by decide
theorem child_required_sub_284 : ∀ j, childrenC_284 j ⊆ insert (0, 0) required_284 := by decide
theorem child_envelope_sub_284 : ∀ j, childrenD_284 j ⊆ envelope_284 := by decide
theorem pivot_mem_284 : (0, 0) ∈ envelope_284 := by decide
theorem children_work_284 : ∀ j, Template HasSnaky 8 (childrenC_284 j) (childrenD_284 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_45 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_224 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_46 3 (0, 1)).mono (by decide)
theorem row_works_284 : Template HasSnaky 9 required_284 envelope_284 := by
  refine compose HasSnaky 8 childrenC_284 childrenD_284 children_work_284 (0, 0)
    required_284 envelope_284 pivot_mem_284 child_required_sub_284 child_envelope_sub_284 ?_
  intro b hb; exact common_sub_284 (mem_commonEnvelope childrenD_284 b hb)
def required_285 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_285 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_285 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, 0) required_273)]
def childrenD_285 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, 0) envelope_273)]
theorem common_sub_285 : commonEnvelope childrenD_285 ⊆ insert (0, 0) required_285 := by decide
theorem child_required_sub_285 : ∀ j, childrenC_285 j ⊆ insert (0, 0) required_285 := by decide
theorem child_envelope_sub_285 : ∀ j, childrenD_285 j ⊆ envelope_285 := by decide
theorem pivot_mem_285 : (0, 0) ∈ envelope_285 := by decide
theorem children_work_285 : ∀ j, Template HasSnaky 8 (childrenC_285 j) (childrenD_285 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_273 0 (2, 0)).mono (by decide)
theorem row_works_285 : Template HasSnaky 9 required_285 envelope_285 := by
  refine compose HasSnaky 8 childrenC_285 childrenD_285 children_work_285 (0, 0)
    required_285 envelope_285 pivot_mem_285 child_required_sub_285 child_envelope_sub_285 ?_
  intro b hb; exact common_sub_285 (mem_commonEnvelope childrenD_285 b hb)
def required_289 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_289 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_289 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (-2, 0) required_279)]
def childrenD_289 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (-2, 0) envelope_279)]
theorem common_sub_289 : commonEnvelope childrenD_289 ⊆ insert (0, 0) required_289 := by decide
theorem child_required_sub_289 : ∀ j, childrenC_289 j ⊆ insert (0, 0) required_289 := by decide
theorem child_envelope_sub_289 : ∀ j, childrenD_289 j ⊆ envelope_289 := by decide
theorem pivot_mem_289 : (0, 0) ∈ envelope_289 := by decide
theorem children_work_289 : ∀ j, Template HasSnaky 8 (childrenC_289 j) (childrenD_289 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_279 0 (-2, 0)).mono (by decide)
theorem row_works_289 : Template HasSnaky 9 required_289 envelope_289 := by
  refine compose HasSnaky 8 childrenC_289 childrenD_289 children_work_289 (0, 0)
    required_289 envelope_289 pivot_mem_289 child_required_sub_289 child_envelope_sub_289 ?_
  intro b hb; exact common_sub_289 (mem_commonEnvelope childrenD_289 b hb)
def required_292 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_292 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_292 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) required_39), (placedSet 3 (-1, 0) required_219), (placedSet 1 (0, -1) required_79)]
def childrenD_292 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_39), (placedSet 3 (-1, 0) envelope_219), (placedSet 1 (0, -1) envelope_79)]
theorem common_sub_292 : commonEnvelope childrenD_292 ⊆ insert (0, 0) required_292 := by decide
theorem child_required_sub_292 : ∀ j, childrenC_292 j ⊆ insert (0, 0) required_292 := by decide
theorem child_envelope_sub_292 : ∀ j, childrenD_292 j ⊆ envelope_292 := by decide
theorem pivot_mem_292 : (0, 0) ∈ envelope_292 := by decide
theorem children_work_292 : ∀ j, Template HasSnaky 8 (childrenC_292 j) (childrenD_292 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_39 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_219 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_79 1 (0, -1)).mono (by decide)
theorem row_works_292 : Template HasSnaky 9 required_292 envelope_292 := by
  refine compose HasSnaky 8 childrenC_292 childrenD_292 children_work_292 (0, 0)
    required_292 envelope_292 pivot_mem_292 child_required_sub_292 child_envelope_sub_292 ?_
  intro b hb; exact common_sub_292 (mem_commonEnvelope childrenD_292 b hb)
def required_294 : Finset Cell := ⟨(([(-3, 0), (-2, -2), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_294 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_294 : Fin 2 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 3 (-3, -1) required_196)]
def childrenD_294 : Fin 2 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 3 (-3, -1) envelope_196)]
theorem common_sub_294 : commonEnvelope childrenD_294 ⊆ insert (0, 0) required_294 := by decide
theorem child_required_sub_294 : ∀ j, childrenC_294 j ⊆ insert (0, 0) required_294 := by decide
theorem child_envelope_sub_294 : ∀ j, childrenD_294 j ⊆ envelope_294 := by decide
theorem pivot_mem_294 : (0, 0) ∈ envelope_294 := by decide
theorem children_work_294 : ∀ j, Template HasSnaky 8 (childrenC_294 j) (childrenD_294 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_196 3 (-3, -1)).mono (by decide)
theorem row_works_294 : Template HasSnaky 9 required_294 envelope_294 := by
  refine compose HasSnaky 8 childrenC_294 childrenD_294 children_work_294 (0, 0)
    required_294 envelope_294 pivot_mem_294 child_required_sub_294 child_envelope_sub_294 ?_
  intro b hb; exact common_sub_294 (mem_commonEnvelope childrenD_294 b hb)
def required_300 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_300 : Finset Cell := ⟨(([(-3, -2), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_300 : Fin 3 → Finset Cell := ![(placedSet 3 (1, -3) required_64), (placedSet 2 (1, -3) required_240), (placedSet 3 (0, 1) required_55)]
def childrenD_300 : Fin 3 → Finset Cell := ![(placedSet 3 (1, -3) envelope_64), (placedSet 2 (1, -3) envelope_240), (placedSet 3 (0, 1) envelope_55)]
theorem common_sub_300 : commonEnvelope childrenD_300 ⊆ insert (0, 0) required_300 := by decide
theorem child_required_sub_300 : ∀ j, childrenC_300 j ⊆ insert (0, 0) required_300 := by decide
theorem child_envelope_sub_300 : ∀ j, childrenD_300 j ⊆ envelope_300 := by decide
theorem pivot_mem_300 : (0, 0) ∈ envelope_300 := by decide
theorem children_work_300 : ∀ j, Template HasSnaky 8 (childrenC_300 j) (childrenD_300 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 3 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_240 2 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_55 3 (0, 1)).mono (by decide)
theorem row_works_300 : Template HasSnaky 9 required_300 envelope_300 := by
  refine compose HasSnaky 8 childrenC_300 childrenD_300 children_work_300 (0, 0)
    required_300 envelope_300 pivot_mem_300 child_required_sub_300 child_envelope_sub_300 ?_
  intro b hb; exact common_sub_300 (mem_commonEnvelope childrenD_300 b hb)
end SnakyConditional

end OAI
