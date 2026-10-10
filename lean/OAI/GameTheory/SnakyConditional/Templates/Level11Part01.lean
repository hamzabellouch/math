import OAI.GameTheory.SnakyConditional.Templates.Level10Part01
import OAI.GameTheory.SnakyConditional.Templates.Level10Part02
import OAI.GameTheory.SnakyConditional.Templates.Level10Part03

namespace OAI

namespace SnakyConditional
def required_255 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_255 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_255 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, -1) required_69), (placedSet 0 (1, 1) required_205), (placedSet 3 (-1, 0) required_7)]
def childrenD_255 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, -1) envelope_69), (placedSet 0 (1, 1) envelope_205), (placedSet 3 (-1, 0) envelope_7)]
theorem common_sub_255 : commonEnvelope childrenD_255 ⊆ insert (0, 0) required_255 := by decide
theorem child_required_sub_255 : ∀ j, childrenC_255 j ⊆ insert (0, 0) required_255 := by decide
theorem child_envelope_sub_255 : ∀ j, childrenD_255 j ⊆ envelope_255 := by decide
theorem pivot_mem_255 : (0, 0) ∈ envelope_255 := by decide
theorem children_work_255 : ∀ j, Template HasSnaky 8 (childrenC_255 j) (childrenD_255 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_69 0 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_205 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
theorem row_works_255 : Template HasSnaky 9 required_255 envelope_255 := by
  refine compose HasSnaky 8 childrenC_255 childrenD_255 children_work_255 (0, 0)
    required_255 envelope_255 pivot_mem_255 child_required_sub_255 child_envelope_sub_255 ?_
  intro b hb; exact common_sub_255 (mem_commonEnvelope childrenD_255 b hb)
def required_258 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -1), (1, 1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_258 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_258 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (0, 1) required_227)]
def childrenD_258 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (0, 1) envelope_227)]
theorem common_sub_258 : commonEnvelope childrenD_258 ⊆ insert (0, 0) required_258 := by decide
theorem child_required_sub_258 : ∀ j, childrenC_258 j ⊆ insert (0, 0) required_258 := by decide
theorem child_envelope_sub_258 : ∀ j, childrenD_258 j ⊆ envelope_258 := by decide
theorem pivot_mem_258 : (0, 0) ∈ envelope_258 := by decide
theorem children_work_258 : ∀ j, Template HasSnaky 8 (childrenC_258 j) (childrenD_258 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_227 0 (0, 1)).mono (by decide)
theorem row_works_258 : Template HasSnaky 9 required_258 envelope_258 := by
  refine compose HasSnaky 8 childrenC_258 childrenD_258 children_work_258 (0, 0)
    required_258 envelope_258 pivot_mem_258 child_required_sub_258 child_envelope_sub_258 ?_
  intro b hb; exact common_sub_258 (mem_commonEnvelope childrenD_258 b hb)
def required_261 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_261 : Finset Cell := ⟨(([(-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_261 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, 0) required_242)]
def childrenD_261 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, 0) envelope_242)]
theorem common_sub_261 : commonEnvelope childrenD_261 ⊆ insert (0, 0) required_261 := by decide
theorem child_required_sub_261 : ∀ j, childrenC_261 j ⊆ insert (0, 0) required_261 := by decide
theorem child_envelope_sub_261 : ∀ j, childrenD_261 j ⊆ envelope_261 := by decide
theorem pivot_mem_261 : (0, 0) ∈ envelope_261 := by decide
theorem children_work_261 : ∀ j, Template HasSnaky 8 (childrenC_261 j) (childrenD_261 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_242 0 (2, 0)).mono (by decide)
theorem row_works_261 : Template HasSnaky 9 required_261 envelope_261 := by
  refine compose HasSnaky 8 childrenC_261 childrenD_261 children_work_261 (0, 0)
    required_261 envelope_261 pivot_mem_261 child_required_sub_261 child_envelope_sub_261 ?_
  intro b hb; exact common_sub_261 (mem_commonEnvelope childrenD_261 b hb)
def required_262 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (0, -1), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_262 : Finset Cell := ⟨(([(-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_262 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 3) required_0), (placedSet 0 (-1, 0) required_213)]
def childrenD_262 : Fin 2 → Finset Cell := ![(placedSet 7 (1, 3) envelope_0), (placedSet 0 (-1, 0) envelope_213)]
theorem common_sub_262 : commonEnvelope childrenD_262 ⊆ insert (0, 0) required_262 := by decide
theorem child_required_sub_262 : ∀ j, childrenC_262 j ⊆ insert (0, 0) required_262 := by decide
theorem child_envelope_sub_262 : ∀ j, childrenD_262 j ⊆ envelope_262 := by decide
theorem pivot_mem_262 : (0, 0) ∈ envelope_262 := by decide
theorem children_work_262 : ∀ j, Template HasSnaky 8 (childrenC_262 j) (childrenD_262 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_213 0 (-1, 0)).mono (by decide)
theorem row_works_262 : Template HasSnaky 9 required_262 envelope_262 := by
  refine compose HasSnaky 8 childrenC_262 childrenD_262 children_work_262 (0, 0)
    required_262 envelope_262 pivot_mem_262 child_required_sub_262 child_envelope_sub_262 ?_
  intro b hb; exact common_sub_262 (mem_commonEnvelope childrenD_262 b hb)
def required_264 : Finset Cell := ⟨(([(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_264 : Finset Cell := ⟨(([(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_264 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 1 (3, 0) required_250)]
def childrenD_264 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 1 (3, 0) envelope_250)]
theorem common_sub_264 : commonEnvelope childrenD_264 ⊆ insert (0, 0) required_264 := by decide
theorem child_required_sub_264 : ∀ j, childrenC_264 j ⊆ insert (0, 0) required_264 := by decide
theorem child_envelope_sub_264 : ∀ j, childrenD_264 j ⊆ envelope_264 := by decide
theorem pivot_mem_264 : (0, 0) ∈ envelope_264 := by decide
theorem children_work_264 : ∀ j, Template HasSnaky 8 (childrenC_264 j) (childrenD_264 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_250 1 (3, 0)).mono (by decide)
theorem row_works_264 : Template HasSnaky 9 required_264 envelope_264 := by
  refine compose HasSnaky 8 childrenC_264 childrenD_264 children_work_264 (0, 0)
    required_264 envelope_264 pivot_mem_264 child_required_sub_264 child_envelope_sub_264 ?_
  intro b hb; exact common_sub_264 (mem_commonEnvelope childrenD_264 b hb)
def required_265 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_265 : Finset Cell := ⟨(([(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_265 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 0 (0, 2) required_247)]
def childrenD_265 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 0 (0, 2) envelope_247)]
theorem common_sub_265 : commonEnvelope childrenD_265 ⊆ insert (0, 0) required_265 := by decide
theorem child_required_sub_265 : ∀ j, childrenC_265 j ⊆ insert (0, 0) required_265 := by decide
theorem child_envelope_sub_265 : ∀ j, childrenD_265 j ⊆ envelope_265 := by decide
theorem pivot_mem_265 : (0, 0) ∈ envelope_265 := by decide
theorem children_work_265 : ∀ j, Template HasSnaky 8 (childrenC_265 j) (childrenD_265 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_247 0 (0, 2)).mono (by decide)
theorem row_works_265 : Template HasSnaky 9 required_265 envelope_265 := by
  refine compose HasSnaky 8 childrenC_265 childrenD_265 children_work_265 (0, 0)
    required_265 envelope_265 pivot_mem_265 child_required_sub_265 child_envelope_sub_265 ?_
  intro b hb; exact common_sub_265 (mem_commonEnvelope childrenD_265 b hb)
end SnakyConditional

end OAI
