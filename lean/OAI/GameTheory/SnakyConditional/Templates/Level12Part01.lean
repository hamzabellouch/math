import OAI.GameTheory.SnakyConditional.Templates.Level11Part01
import OAI.GameTheory.SnakyConditional.Templates.Level11Part03

namespace OAI

namespace SnakyConditional
def required_282 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_282 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_282 : Fin 4 → Finset Cell := ![(placedSet 0 (1, 0) required_56), (placedSet 0 (-3, -1) required_64), (placedSet 0 (1, 0) required_55), (placedSet 0 (-3, -1) required_265)]
def childrenD_282 : Fin 4 → Finset Cell := ![(placedSet 0 (1, 0) envelope_56), (placedSet 0 (-3, -1) envelope_64), (placedSet 0 (1, 0) envelope_55), (placedSet 0 (-3, -1) envelope_265)]
theorem common_sub_282 : commonEnvelope childrenD_282 ⊆ insert (0, 0) required_282 := by decide
theorem child_required_sub_282 : ∀ j, childrenC_282 j ⊆ insert (0, 0) required_282 := by decide
theorem child_envelope_sub_282 : ∀ j, childrenD_282 j ⊆ envelope_282 := by decide
theorem pivot_mem_282 : (0, 0) ∈ envelope_282 := by decide
theorem children_work_282 : ∀ j, Template HasSnaky 9 (childrenC_282 j) (childrenD_282 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_56 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_64 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_265 0 (-3, -1)).mono (by decide)
theorem row_works_282 : Template HasSnaky 10 required_282 envelope_282 := by
  refine compose HasSnaky 9 childrenC_282 childrenD_282 children_work_282 (0, 0)
    required_282 envelope_282 pivot_mem_282 child_required_sub_282 child_envelope_sub_282 ?_
  intro b hb; exact common_sub_282 (mem_commonEnvelope childrenD_282 b hb)
def required_286 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_286 : Finset Cell := ⟨(([(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_286 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -4) required_6), (placedSet 0 (-1, 0) required_261)]
def childrenD_286 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -4) envelope_6), (placedSet 0 (-1, 0) envelope_261)]
theorem common_sub_286 : commonEnvelope childrenD_286 ⊆ insert (0, 0) required_286 := by decide
theorem child_required_sub_286 : ∀ j, childrenC_286 j ⊆ insert (0, 0) required_286 := by decide
theorem child_envelope_sub_286 : ∀ j, childrenD_286 j ⊆ envelope_286 := by decide
theorem pivot_mem_286 : (0, 0) ∈ envelope_286 := by decide
theorem children_work_286 : ∀ j, Template HasSnaky 9 (childrenC_286 j) (childrenD_286 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 7 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_261 0 (-1, 0)).mono (by decide)
theorem row_works_286 : Template HasSnaky 10 required_286 envelope_286 := by
  refine compose HasSnaky 9 childrenC_286 childrenD_286 children_work_286 (0, 0)
    required_286 envelope_286 pivot_mem_286 child_required_sub_286 child_envelope_sub_286 ?_
  intro b hb; exact common_sub_286 (mem_commonEnvelope childrenD_286 b hb)
def required_287 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_287 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_287 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, -1) required_64), (placedSet 0 (1, 0) required_55), (placedSet 0 (1, 0) required_56), (placedSet 4 (0, 1) required_264)]
def childrenD_287 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_64), (placedSet 0 (1, 0) envelope_55), (placedSet 0 (1, 0) envelope_56), (placedSet 4 (0, 1) envelope_264)]
theorem common_sub_287 : commonEnvelope childrenD_287 ⊆ insert (0, 0) required_287 := by decide
theorem child_required_sub_287 : ∀ j, childrenC_287 j ⊆ insert (0, 0) required_287 := by decide
theorem child_envelope_sub_287 : ∀ j, childrenD_287 j ⊆ envelope_287 := by decide
theorem pivot_mem_287 : (0, 0) ∈ envelope_287 := by decide
theorem children_work_287 : ∀ j, Template HasSnaky 9 (childrenC_287 j) (childrenD_287 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_56 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_264 4 (0, 1)).mono (by decide)
theorem row_works_287 : Template HasSnaky 10 required_287 envelope_287 := by
  refine compose HasSnaky 9 childrenC_287 childrenD_287 children_work_287 (0, 0)
    required_287 envelope_287 pivot_mem_287 child_required_sub_287 child_envelope_sub_287 ?_
  intro b hb; exact common_sub_287 (mem_commonEnvelope childrenD_287 b hb)
def required_295 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_295 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_295 : Fin 4 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 2 (-3, 1) required_64), (placedSet 0 (1, 0) required_55), (placedSet 4 (0, -1) required_265)]
def childrenD_295 : Fin 4 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 2 (-3, 1) envelope_64), (placedSet 0 (1, 0) envelope_55), (placedSet 4 (0, -1) envelope_265)]
theorem common_sub_295 : commonEnvelope childrenD_295 ⊆ insert (0, 0) required_295 := by decide
theorem child_required_sub_295 : ∀ j, childrenC_295 j ⊆ insert (0, 0) required_295 := by decide
theorem child_envelope_sub_295 : ∀ j, childrenD_295 j ⊆ envelope_295 := by decide
theorem pivot_mem_295 : (0, 0) ∈ envelope_295 := by decide
theorem children_work_295 : ∀ j, Template HasSnaky 9 (childrenC_295 j) (childrenD_295 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_64 2 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_265 4 (0, -1)).mono (by decide)
theorem row_works_295 : Template HasSnaky 10 required_295 envelope_295 := by
  refine compose HasSnaky 9 childrenC_295 childrenD_295 children_work_295 (0, 0)
    required_295 envelope_295 pivot_mem_295 child_required_sub_295 child_envelope_sub_295 ?_
  intro b hb; exact common_sub_295 (mem_commonEnvelope childrenD_295 b hb)
def required_297 : Finset Cell := ⟨(([(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_297 : Finset Cell := ⟨(([(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_297 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 1 (3, 0) required_289)]
def childrenD_297 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 1 (3, 0) envelope_289)]
theorem common_sub_297 : commonEnvelope childrenD_297 ⊆ insert (0, 0) required_297 := by decide
theorem child_required_sub_297 : ∀ j, childrenC_297 j ⊆ insert (0, 0) required_297 := by decide
theorem child_envelope_sub_297 : ∀ j, childrenD_297 j ⊆ envelope_297 := by decide
theorem pivot_mem_297 : (0, 0) ∈ envelope_297 := by decide
theorem children_work_297 : ∀ j, Template HasSnaky 9 (childrenC_297 j) (childrenD_297 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_289 1 (3, 0)).mono (by decide)
theorem row_works_297 : Template HasSnaky 10 required_297 envelope_297 := by
  refine compose HasSnaky 9 childrenC_297 childrenD_297 children_work_297 (0, 0)
    required_297 envelope_297 pivot_mem_297 child_required_sub_297 child_envelope_sub_297 ?_
  intro b hb; exact common_sub_297 (mem_commonEnvelope childrenD_297 b hb)
end SnakyConditional

end OAI
