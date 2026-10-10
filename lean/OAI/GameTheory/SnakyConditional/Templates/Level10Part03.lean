import OAI.GameTheory.SnakyConditional.Templates.Level09Part01
import OAI.GameTheory.SnakyConditional.Templates.Level09Part04
import OAI.GameTheory.SnakyConditional.Templates.Level09Part05

namespace OAI

namespace SnakyConditional
def required_248 : Finset Cell := ⟨(([(-1, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_248 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_248 : Fin 4 → Finset Cell := ![(placedSet 0 (3, 0) required_186), (placedSet 0 (-1, -1) required_143), (placedSet 2 (3, 0) required_175), (placedSet 6 (2, 1) required_64)]
def childrenD_248 : Fin 4 → Finset Cell := ![(placedSet 0 (3, 0) envelope_186), (placedSet 0 (-1, -1) envelope_143), (placedSet 2 (3, 0) envelope_175), (placedSet 6 (2, 1) envelope_64)]
theorem common_sub_248 : commonEnvelope childrenD_248 ⊆ insert (0, 0) required_248 := by decide
theorem child_required_sub_248 : ∀ j, childrenC_248 j ⊆ insert (0, 0) required_248 := by decide
theorem child_envelope_sub_248 : ∀ j, childrenD_248 j ⊆ envelope_248 := by decide
theorem pivot_mem_248 : (0, 0) ∈ envelope_248 := by decide
theorem children_work_248 : ∀ j, Template HasSnaky 7 (childrenC_248 j) (childrenD_248 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_186 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_143 0 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_175 2 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_64 6 (2, 1)).mono (by decide)
theorem row_works_248 : Template HasSnaky 8 required_248 envelope_248 := by
  refine compose HasSnaky 7 childrenC_248 childrenD_248 children_work_248 (0, 0)
    required_248 envelope_248 pivot_mem_248 child_required_sub_248 child_envelope_sub_248 ?_
  intro b hb; exact common_sub_248 (mem_commonEnvelope childrenD_248 b hb)
def required_249 : Finset Cell := ⟨(([(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_249 : Finset Cell := ⟨(([(-3, 0), (-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -1), (3, -3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_249 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 1) required_0), (placedSet 1 (0, -3) required_225)]
def childrenD_249 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 1) envelope_0), (placedSet 1 (0, -3) envelope_225)]
theorem common_sub_249 : commonEnvelope childrenD_249 ⊆ insert (0, 0) required_249 := by decide
theorem child_required_sub_249 : ∀ j, childrenC_249 j ⊆ insert (0, 0) required_249 := by decide
theorem child_envelope_sub_249 : ∀ j, childrenD_249 j ⊆ envelope_249 := by decide
theorem pivot_mem_249 : (0, 0) ∈ envelope_249 := by decide
theorem children_work_249 : ∀ j, Template HasSnaky 7 (childrenC_249 j) (childrenD_249 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_225 1 (0, -3)).mono (by decide)
theorem row_works_249 : Template HasSnaky 8 required_249 envelope_249 := by
  refine compose HasSnaky 7 childrenC_249 childrenD_249 children_work_249 (0, 0)
    required_249 envelope_249 pivot_mem_249 child_required_sub_249 child_envelope_sub_249 ?_
  intro b hb; exact common_sub_249 (mem_commonEnvelope childrenD_249 b hb)
def required_250 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_250 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_250 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (-2, 0) required_238)]
def childrenD_250 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (-2, 0) envelope_238)]
theorem common_sub_250 : commonEnvelope childrenD_250 ⊆ insert (0, 0) required_250 := by decide
theorem child_required_sub_250 : ∀ j, childrenC_250 j ⊆ insert (0, 0) required_250 := by decide
theorem child_envelope_sub_250 : ∀ j, childrenD_250 j ⊆ envelope_250 := by decide
theorem pivot_mem_250 : (0, 0) ∈ envelope_250 := by decide
theorem children_work_250 : ∀ j, Template HasSnaky 7 (childrenC_250 j) (childrenD_250 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_238 0 (-2, 0)).mono (by decide)
theorem row_works_250 : Template HasSnaky 8 required_250 envelope_250 := by
  refine compose HasSnaky 7 childrenC_250 childrenD_250 children_work_250 (0, 0)
    required_250 envelope_250 pivot_mem_250 child_required_sub_250 child_envelope_sub_250 ?_
  intro b hb; exact common_sub_250 (mem_commonEnvelope childrenD_250 b hb)
def required_251 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, 1), (0, 1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_251 : Finset Cell := ⟨(([(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 3), (1, 4), (1, 5), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_251 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) required_6), (placedSet 4 (-1, 2) required_239)]
def childrenD_251 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) envelope_6), (placedSet 4 (-1, 2) envelope_239)]
theorem common_sub_251 : commonEnvelope childrenD_251 ⊆ insert (0, 0) required_251 := by decide
theorem child_required_sub_251 : ∀ j, childrenC_251 j ⊆ insert (0, 0) required_251 := by decide
theorem child_envelope_sub_251 : ∀ j, childrenD_251 j ⊆ envelope_251 := by decide
theorem pivot_mem_251 : (0, 0) ∈ envelope_251 := by decide
theorem children_work_251 : ∀ j, Template HasSnaky 7 (childrenC_251 j) (childrenD_251 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_239 4 (-1, 2)).mono (by decide)
theorem row_works_251 : Template HasSnaky 8 required_251 envelope_251 := by
  refine compose HasSnaky 7 childrenC_251 childrenD_251 children_work_251 (0, 0)
    required_251 envelope_251 pivot_mem_251 child_required_sub_251 child_envelope_sub_251 ?_
  intro b hb; exact common_sub_251 (mem_commonEnvelope childrenD_251 b hb)
def required_256 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_256 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_256 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 1) required_0), (placedSet 0 (-1, 0) required_231)]
def childrenD_256 : Fin 2 → Finset Cell := ![(placedSet 5 (0, 1) envelope_0), (placedSet 0 (-1, 0) envelope_231)]
theorem common_sub_256 : commonEnvelope childrenD_256 ⊆ insert (0, 0) required_256 := by decide
theorem child_required_sub_256 : ∀ j, childrenC_256 j ⊆ insert (0, 0) required_256 := by decide
theorem child_envelope_sub_256 : ∀ j, childrenD_256 j ⊆ envelope_256 := by decide
theorem pivot_mem_256 : (0, 0) ∈ envelope_256 := by decide
theorem children_work_256 : ∀ j, Template HasSnaky 7 (childrenC_256 j) (childrenD_256 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_231 0 (-1, 0)).mono (by decide)
theorem row_works_256 : Template HasSnaky 8 required_256 envelope_256 := by
  refine compose HasSnaky 7 childrenC_256 childrenD_256 children_work_256 (0, 0)
    required_256 envelope_256 pivot_mem_256 child_required_sub_256 child_envelope_sub_256 ?_
  intro b hb; exact common_sub_256 (mem_commonEnvelope childrenD_256 b hb)
def required_257 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_257 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_257 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) required_4), (placedSet 0 (0, 1) required_235)]
def childrenD_257 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) envelope_4), (placedSet 0 (0, 1) envelope_235)]
theorem common_sub_257 : commonEnvelope childrenD_257 ⊆ insert (0, 0) required_257 := by decide
theorem child_required_sub_257 : ∀ j, childrenC_257 j ⊆ insert (0, 0) required_257 := by decide
theorem child_envelope_sub_257 : ∀ j, childrenD_257 j ⊆ envelope_257 := by decide
theorem pivot_mem_257 : (0, 0) ∈ envelope_257 := by decide
theorem children_work_257 : ∀ j, Template HasSnaky 7 (childrenC_257 j) (childrenD_257 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_235 0 (0, 1)).mono (by decide)
theorem row_works_257 : Template HasSnaky 8 required_257 envelope_257 := by
  refine compose HasSnaky 7 childrenC_257 childrenD_257 children_work_257 (0, 0)
    required_257 envelope_257 pivot_mem_257 child_required_sub_257 child_envelope_sub_257 ?_
  intro b hb; exact common_sub_257 (mem_commonEnvelope childrenD_257 b hb)
def required_259 : Finset Cell := ⟨(([(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_259 : Finset Cell := ⟨(([(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_259 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 1 (3, -2) required_231)]
def childrenD_259 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 1 (3, -2) envelope_231)]
theorem common_sub_259 : commonEnvelope childrenD_259 ⊆ insert (0, 0) required_259 := by decide
theorem child_required_sub_259 : ∀ j, childrenC_259 j ⊆ insert (0, 0) required_259 := by decide
theorem child_envelope_sub_259 : ∀ j, childrenD_259 j ⊆ envelope_259 := by decide
theorem pivot_mem_259 : (0, 0) ∈ envelope_259 := by decide
theorem children_work_259 : ∀ j, Template HasSnaky 7 (childrenC_259 j) (childrenD_259 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_231 1 (3, -2)).mono (by decide)
theorem row_works_259 : Template HasSnaky 8 required_259 envelope_259 := by
  refine compose HasSnaky 7 childrenC_259 childrenD_259 children_work_259 (0, 0)
    required_259 envelope_259 pivot_mem_259 child_required_sub_259 child_envelope_sub_259 ?_
  intro b hb; exact common_sub_259 (mem_commonEnvelope childrenD_259 b hb)
end SnakyConditional

end OAI
