import OAI.GameTheory.SnakyConditional.Templates.Level10Part01
import OAI.GameTheory.SnakyConditional.Templates.Level10Part02
import OAI.GameTheory.SnakyConditional.Templates.Level10Part03

namespace OAI

namespace SnakyConditional
def required_266 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_266 : Finset Cell := ⟨(([(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_266 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) required_6), (placedSet 0 (1, 0) required_242)]
def childrenD_266 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 1) envelope_6), (placedSet 0 (1, 0) envelope_242)]
theorem common_sub_266 : commonEnvelope childrenD_266 ⊆ insert (0, 0) required_266 := by decide
theorem child_required_sub_266 : ∀ j, childrenC_266 j ⊆ insert (0, 0) required_266 := by decide
theorem child_envelope_sub_266 : ∀ j, childrenD_266 j ⊆ envelope_266 := by decide
theorem pivot_mem_266 : (0, 0) ∈ envelope_266 := by decide
theorem children_work_266 : ∀ j, Template HasSnaky 8 (childrenC_266 j) (childrenD_266 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_242 0 (1, 0)).mono (by decide)
theorem row_works_266 : Template HasSnaky 9 required_266 envelope_266 := by
  refine compose HasSnaky 8 childrenC_266 childrenD_266 children_work_266 (0, 0)
    required_266 envelope_266 pivot_mem_266 child_required_sub_266 child_envelope_sub_266 ?_
  intro b hb; exact common_sub_266 (mem_commonEnvelope childrenD_266 b hb)
def required_268 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_268 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_268 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (0, -2) required_251)]
def childrenD_268 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (0, -2) envelope_251)]
theorem common_sub_268 : commonEnvelope childrenD_268 ⊆ insert (0, 0) required_268 := by decide
theorem child_required_sub_268 : ∀ j, childrenC_268 j ⊆ insert (0, 0) required_268 := by decide
theorem child_envelope_sub_268 : ∀ j, childrenD_268 j ⊆ envelope_268 := by decide
theorem pivot_mem_268 : (0, 0) ∈ envelope_268 := by decide
theorem children_work_268 : ∀ j, Template HasSnaky 8 (childrenC_268 j) (childrenD_268 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_251 0 (0, -2)).mono (by decide)
theorem row_works_268 : Template HasSnaky 9 required_268 envelope_268 := by
  refine compose HasSnaky 8 childrenC_268 childrenD_268 children_work_268 (0, 0)
    required_268 envelope_268 pivot_mem_268 child_required_sub_268 child_envelope_sub_268 ?_
  intro b hb; exact common_sub_268 (mem_commonEnvelope childrenD_268 b hb)
def required_272 : Finset Cell := ⟨(([(-2, -1), (-1, -4), (-1, -2), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_272 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_272 : Fin 2 → Finset Cell := ![(placedSet 1 (-1, -3) required_1), (placedSet 0 (0, 1) required_249)]
def childrenD_272 : Fin 2 → Finset Cell := ![(placedSet 1 (-1, -3) envelope_1), (placedSet 0 (0, 1) envelope_249)]
theorem common_sub_272 : commonEnvelope childrenD_272 ⊆ insert (0, 0) required_272 := by decide
theorem child_required_sub_272 : ∀ j, childrenC_272 j ⊆ insert (0, 0) required_272 := by decide
theorem child_envelope_sub_272 : ∀ j, childrenD_272 j ⊆ envelope_272 := by decide
theorem pivot_mem_272 : (0, 0) ∈ envelope_272 := by decide
theorem children_work_272 : ∀ j, Template HasSnaky 8 (childrenC_272 j) (childrenD_272 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_1 1 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_249 0 (0, 1)).mono (by decide)
theorem row_works_272 : Template HasSnaky 9 required_272 envelope_272 := by
  refine compose HasSnaky 8 childrenC_272 childrenD_272 children_work_272 (0, 0)
    required_272 envelope_272 pivot_mem_272 child_required_sub_272 child_envelope_sub_272 ?_
  intro b hb; exact common_sub_272 (mem_commonEnvelope childrenD_272 b hb)
def required_274 : Finset Cell := ⟨(([(-1, -2), (0, -2), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_274 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_274 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) required_6), (placedSet 0 (1, 1) required_240)]
def childrenD_274 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) envelope_6), (placedSet 0 (1, 1) envelope_240)]
theorem common_sub_274 : commonEnvelope childrenD_274 ⊆ insert (0, 0) required_274 := by decide
theorem child_required_sub_274 : ∀ j, childrenC_274 j ⊆ insert (0, 0) required_274 := by decide
theorem child_envelope_sub_274 : ∀ j, childrenD_274 j ⊆ envelope_274 := by decide
theorem pivot_mem_274 : (0, 0) ∈ envelope_274 := by decide
theorem children_work_274 : ∀ j, Template HasSnaky 8 (childrenC_274 j) (childrenD_274 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 7 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_240 0 (1, 1)).mono (by decide)
theorem row_works_274 : Template HasSnaky 9 required_274 envelope_274 := by
  refine compose HasSnaky 8 childrenC_274 childrenD_274 children_work_274 (0, 0)
    required_274 envelope_274 pivot_mem_274 child_required_sub_274 child_envelope_sub_274 ?_
  intro b hb; exact common_sub_274 (mem_commonEnvelope childrenD_274 b hb)
def required_277 : Finset Cell := ⟨(([(-1, -3), (-1, -1), (0, -1), (1, -3), (1, -2), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_277 : Finset Cell := ⟨(([(-2, -4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_277 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_14), (placedSet 2 (-1, -4) required_204), (placedSet 1 (-1, -2) required_33)]
def childrenD_277 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_14), (placedSet 2 (-1, -4) envelope_204), (placedSet 1 (-1, -2) envelope_33)]
theorem common_sub_277 : commonEnvelope childrenD_277 ⊆ insert (0, 0) required_277 := by decide
theorem child_required_sub_277 : ∀ j, childrenC_277 j ⊆ insert (0, 0) required_277 := by decide
theorem child_envelope_sub_277 : ∀ j, childrenD_277 j ⊆ envelope_277 := by decide
theorem pivot_mem_277 : (0, 0) ∈ envelope_277 := by decide
theorem children_work_277 : ∀ j, Template HasSnaky 8 (childrenC_277 j) (childrenD_277 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_14 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_204 2 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_33 1 (-1, -2)).mono (by decide)
theorem row_works_277 : Template HasSnaky 9 required_277 envelope_277 := by
  refine compose HasSnaky 8 childrenC_277 childrenD_277 children_work_277 (0, 0)
    required_277 envelope_277 pivot_mem_277 child_required_sub_277 child_envelope_sub_277 ?_
  intro b hb; exact common_sub_277 (mem_commonEnvelope childrenD_277 b hb)
def required_283 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_283 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_283 : Fin 3 → Finset Cell := ![(placedSet 0 (-3, -1) required_64), (placedSet 1 (0, -1) required_196), (placedSet 2 (1, 0) required_55)]
def childrenD_283 : Fin 3 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_64), (placedSet 1 (0, -1) envelope_196), (placedSet 2 (1, 0) envelope_55)]
theorem common_sub_283 : commonEnvelope childrenD_283 ⊆ insert (0, 0) required_283 := by decide
theorem child_required_sub_283 : ∀ j, childrenC_283 j ⊆ insert (0, 0) required_283 := by decide
theorem child_envelope_sub_283 : ∀ j, childrenD_283 j ⊆ envelope_283 := by decide
theorem pivot_mem_283 : (0, 0) ∈ envelope_283 := by decide
theorem children_work_283 : ∀ j, Template HasSnaky 8 (childrenC_283 j) (childrenD_283 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_196 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 2 (1, 0)).mono (by decide)
theorem row_works_283 : Template HasSnaky 9 required_283 envelope_283 := by
  refine compose HasSnaky 8 childrenC_283 childrenD_283 children_work_283 (0, 0)
    required_283 envelope_283 pivot_mem_283 child_required_sub_283 child_envelope_sub_283 ?_
  intro b hb; exact common_sub_283 (mem_commonEnvelope childrenD_283 b hb)
end SnakyConditional

end OAI
