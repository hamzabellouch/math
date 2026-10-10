import OAI.GameTheory.SnakyConditional.Templates.Level09Part01
import OAI.GameTheory.SnakyConditional.Templates.Level09Part02
import OAI.GameTheory.SnakyConditional.Templates.Level09Part03
import OAI.GameTheory.SnakyConditional.Templates.Level09Part04
import OAI.GameTheory.SnakyConditional.Templates.Level09Part05

namespace OAI

namespace SnakyConditional
def required_227 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, -2), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_227 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_227 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) required_6), (placedSet 0 (3, -1) required_212)]
def childrenD_227 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) envelope_6), (placedSet 0 (3, -1) envelope_212)]
theorem common_sub_227 : commonEnvelope childrenD_227 ⊆ insert (0, 0) required_227 := by decide
theorem child_required_sub_227 : ∀ j, childrenC_227 j ⊆ insert (0, 0) required_227 := by decide
theorem child_envelope_sub_227 : ∀ j, childrenD_227 j ⊆ envelope_227 := by decide
theorem pivot_mem_227 : (0, 0) ∈ envelope_227 := by decide
theorem children_work_227 : ∀ j, Template HasSnaky 7 (childrenC_227 j) (childrenD_227 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_212 0 (3, -1)).mono (by decide)
theorem row_works_227 : Template HasSnaky 8 required_227 envelope_227 := by
  refine compose HasSnaky 7 childrenC_227 childrenD_227 children_work_227 (0, 0)
    required_227 envelope_227 pivot_mem_227 child_required_sub_227 child_envelope_sub_227 ?_
  intro b hb; exact common_sub_227 (mem_commonEnvelope childrenD_227 b hb)
def required_230 : Finset Cell := ⟨(([(0, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_230 : Finset Cell := ⟨(([(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0), (7, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_230 : Fin 4 → Finset Cell := ![(placedSet 6 (-1, 0) required_10), (placedSet 0 (1, 1) required_193), (placedSet 0 (4, 1) required_203), (placedSet 0 (1, 0) required_33)]
def childrenD_230 : Fin 4 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_10), (placedSet 0 (1, 1) envelope_193), (placedSet 0 (4, 1) envelope_203), (placedSet 0 (1, 0) envelope_33)]
theorem common_sub_230 : commonEnvelope childrenD_230 ⊆ insert (0, 0) required_230 := by decide
theorem child_required_sub_230 : ∀ j, childrenC_230 j ⊆ insert (0, 0) required_230 := by decide
theorem child_envelope_sub_230 : ∀ j, childrenD_230 j ⊆ envelope_230 := by decide
theorem pivot_mem_230 : (0, 0) ∈ envelope_230 := by decide
theorem children_work_230 : ∀ j, Template HasSnaky 7 (childrenC_230 j) (childrenD_230 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_10 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_193 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_203 0 (4, 1)).mono (by decide)
  · exact (placed_template_map row_works_33 0 (1, 0)).mono (by decide)
theorem row_works_230 : Template HasSnaky 8 required_230 envelope_230 := by
  refine compose HasSnaky 7 childrenC_230 childrenD_230 children_work_230 (0, 0)
    required_230 envelope_230 pivot_mem_230 child_required_sub_230 child_envelope_sub_230 ?_
  intro b hb; exact common_sub_230 (mem_commonEnvelope childrenD_230 b hb)
def required_240 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_240 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_240 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (-2, 0) required_237)]
def childrenD_240 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (-2, 0) envelope_237)]
theorem common_sub_240 : commonEnvelope childrenD_240 ⊆ insert (0, 0) required_240 := by decide
theorem child_required_sub_240 : ∀ j, childrenC_240 j ⊆ insert (0, 0) required_240 := by decide
theorem child_envelope_sub_240 : ∀ j, childrenD_240 j ⊆ envelope_240 := by decide
theorem pivot_mem_240 : (0, 0) ∈ envelope_240 := by decide
theorem children_work_240 : ∀ j, Template HasSnaky 7 (childrenC_240 j) (childrenD_240 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_237 0 (-2, 0)).mono (by decide)
theorem row_works_240 : Template HasSnaky 8 required_240 envelope_240 := by
  refine compose HasSnaky 7 childrenC_240 childrenD_240 children_work_240 (0, 0)
    required_240 envelope_240 pivot_mem_240 child_required_sub_240 child_envelope_sub_240 ?_
  intro b hb; exact common_sub_240 (mem_commonEnvelope childrenD_240 b hb)
def required_242 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_242 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_242 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (1, 0) required_190)]
def childrenD_242 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (1, 0) envelope_190)]
theorem common_sub_242 : commonEnvelope childrenD_242 ⊆ insert (0, 0) required_242 := by decide
theorem child_required_sub_242 : ∀ j, childrenC_242 j ⊆ insert (0, 0) required_242 := by decide
theorem child_envelope_sub_242 : ∀ j, childrenD_242 j ⊆ envelope_242 := by decide
theorem pivot_mem_242 : (0, 0) ∈ envelope_242 := by decide
theorem children_work_242 : ∀ j, Template HasSnaky 7 (childrenC_242 j) (childrenD_242 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_190 0 (1, 0)).mono (by decide)
theorem row_works_242 : Template HasSnaky 8 required_242 envelope_242 := by
  refine compose HasSnaky 7 childrenC_242 childrenD_242 children_work_242 (0, 0)
    required_242 envelope_242 pivot_mem_242 child_required_sub_242 child_envelope_sub_242 ?_
  intro b hb; exact common_sub_242 (mem_commonEnvelope childrenD_242 b hb)
def required_245 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_245 : Finset Cell := ⟨(([(-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_245 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, -1) required_64), (placedSet 4 (-4, 0) required_175), (placedSet 6 (0, 1) required_143), (placedSet 6 (-4, 0) required_186)]
def childrenD_245 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_64), (placedSet 4 (-4, 0) envelope_175), (placedSet 6 (0, 1) envelope_143), (placedSet 6 (-4, 0) envelope_186)]
theorem common_sub_245 : commonEnvelope childrenD_245 ⊆ insert (0, 0) required_245 := by decide
theorem child_required_sub_245 : ∀ j, childrenC_245 j ⊆ insert (0, 0) required_245 := by decide
theorem child_envelope_sub_245 : ∀ j, childrenD_245 j ⊆ envelope_245 := by decide
theorem pivot_mem_245 : (0, 0) ∈ envelope_245 := by decide
theorem children_work_245 : ∀ j, Template HasSnaky 7 (childrenC_245 j) (childrenD_245 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_175 4 (-4, 0)).mono (by decide)
  · exact (placed_template_map row_works_143 6 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_186 6 (-4, 0)).mono (by decide)
theorem row_works_245 : Template HasSnaky 8 required_245 envelope_245 := by
  refine compose HasSnaky 7 childrenC_245 childrenD_245 children_work_245 (0, 0)
    required_245 envelope_245 pivot_mem_245 child_required_sub_245 child_envelope_sub_245 ?_
  intro b hb; exact common_sub_245 (mem_commonEnvelope childrenD_245 b hb)
def required_246 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_246 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_246 : Fin 4 → Finset Cell := ![(placedSet 6 (0, 1) required_64), (placedSet 2 (1, 0) required_175), (placedSet 0 (1, 0) required_186), (placedSet 0 (-3, -1) required_143)]
def childrenD_246 : Fin 4 → Finset Cell := ![(placedSet 6 (0, 1) envelope_64), (placedSet 2 (1, 0) envelope_175), (placedSet 0 (1, 0) envelope_186), (placedSet 0 (-3, -1) envelope_143)]
theorem common_sub_246 : commonEnvelope childrenD_246 ⊆ insert (0, 0) required_246 := by decide
theorem child_required_sub_246 : ∀ j, childrenC_246 j ⊆ insert (0, 0) required_246 := by decide
theorem child_envelope_sub_246 : ∀ j, childrenD_246 j ⊆ envelope_246 := by decide
theorem pivot_mem_246 : (0, 0) ∈ envelope_246 := by decide
theorem children_work_246 : ∀ j, Template HasSnaky 7 (childrenC_246 j) (childrenD_246 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 6 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_175 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_186 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_143 0 (-3, -1)).mono (by decide)
theorem row_works_246 : Template HasSnaky 8 required_246 envelope_246 := by
  refine compose HasSnaky 7 childrenC_246 childrenD_246 children_work_246 (0, 0)
    required_246 envelope_246 pivot_mem_246 child_required_sub_246 child_envelope_sub_246 ?_
  intro b hb; exact common_sub_246 (mem_commonEnvelope childrenD_246 b hb)
def required_247 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_247 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_247 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (0, 1) required_229)]
def childrenD_247 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (0, 1) envelope_229)]
theorem common_sub_247 : commonEnvelope childrenD_247 ⊆ insert (0, 0) required_247 := by decide
theorem child_required_sub_247 : ∀ j, childrenC_247 j ⊆ insert (0, 0) required_247 := by decide
theorem child_envelope_sub_247 : ∀ j, childrenD_247 j ⊆ envelope_247 := by decide
theorem pivot_mem_247 : (0, 0) ∈ envelope_247 := by decide
theorem children_work_247 : ∀ j, Template HasSnaky 7 (childrenC_247 j) (childrenD_247 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_229 0 (0, 1)).mono (by decide)
theorem row_works_247 : Template HasSnaky 8 required_247 envelope_247 := by
  refine compose HasSnaky 7 childrenC_247 childrenD_247 children_work_247 (0, 0)
    required_247 envelope_247 pivot_mem_247 child_required_sub_247 child_envelope_sub_247 ?_
  intro b hb; exact common_sub_247 (mem_commonEnvelope childrenD_247 b hb)
end SnakyConditional

end OAI
