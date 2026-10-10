import OAI.GameTheory.SnakyConditional.Templates.Level09Part01
import OAI.GameTheory.SnakyConditional.Templates.Level09Part02
import OAI.GameTheory.SnakyConditional.Templates.Level09Part03

namespace OAI

namespace SnakyConditional
def required_196 : Finset Cell := ⟨(([(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_196 : Finset Cell := ⟨(([(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_196 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 5 (2, 0) required_187)]
def childrenD_196 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 5 (2, 0) envelope_187)]
theorem common_sub_196 : commonEnvelope childrenD_196 ⊆ insert (0, 0) required_196 := by decide
theorem child_required_sub_196 : ∀ j, childrenC_196 j ⊆ insert (0, 0) required_196 := by decide
theorem child_envelope_sub_196 : ∀ j, childrenD_196 j ⊆ envelope_196 := by decide
theorem pivot_mem_196 : (0, 0) ∈ envelope_196 := by decide
theorem children_work_196 : ∀ j, Template HasSnaky 7 (childrenC_196 j) (childrenD_196 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_187 5 (2, 0)).mono (by decide)
theorem row_works_196 : Template HasSnaky 8 required_196 envelope_196 := by
  refine compose HasSnaky 7 childrenC_196 childrenD_196 children_work_196 (0, 0)
    required_196 envelope_196 pivot_mem_196 child_required_sub_196 child_envelope_sub_196 ?_
  intro b hb; exact common_sub_196 (mem_commonEnvelope childrenD_196 b hb)
def required_204 : Finset Cell := ⟨(([(0, -3), (0, -1), (1, -4), (1, -3), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_204 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_204 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -2) required_2), (placedSet 2 (1, -1) required_166)]
def childrenD_204 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -2) envelope_2), (placedSet 2 (1, -1) envelope_166)]
theorem common_sub_204 : commonEnvelope childrenD_204 ⊆ insert (0, 0) required_204 := by decide
theorem child_required_sub_204 : ∀ j, childrenC_204 j ⊆ insert (0, 0) required_204 := by decide
theorem child_envelope_sub_204 : ∀ j, childrenD_204 j ⊆ envelope_204 := by decide
theorem pivot_mem_204 : (0, 0) ∈ envelope_204 := by decide
theorem children_work_204 : ∀ j, Template HasSnaky 7 (childrenC_204 j) (childrenD_204 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 5 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_166 2 (1, -1)).mono (by decide)
theorem row_works_204 : Template HasSnaky 8 required_204 envelope_204 := by
  refine compose HasSnaky 7 childrenC_204 childrenD_204 children_work_204 (0, 0)
    required_204 envelope_204 pivot_mem_204 child_required_sub_204 child_envelope_sub_204 ?_
  intro b hb; exact common_sub_204 (mem_commonEnvelope childrenD_204 b hb)
def required_205 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_205 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_205 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_4), (placedSet 0 (-1, 0) required_168)]
def childrenD_205 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_4), (placedSet 0 (-1, 0) envelope_168)]
theorem common_sub_205 : commonEnvelope childrenD_205 ⊆ insert (0, 0) required_205 := by decide
theorem child_required_sub_205 : ∀ j, childrenC_205 j ⊆ insert (0, 0) required_205 := by decide
theorem child_envelope_sub_205 : ∀ j, childrenD_205 j ⊆ envelope_205 := by decide
theorem pivot_mem_205 : (0, 0) ∈ envelope_205 := by decide
theorem children_work_205 : ∀ j, Template HasSnaky 7 (childrenC_205 j) (childrenD_205 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_168 0 (-1, 0)).mono (by decide)
theorem row_works_205 : Template HasSnaky 8 required_205 envelope_205 := by
  refine compose HasSnaky 7 childrenC_205 childrenD_205 children_work_205 (0, 0)
    required_205 envelope_205 pivot_mem_205 child_required_sub_205 child_envelope_sub_205 ?_
  intro b hb; exact common_sub_205 (mem_commonEnvelope childrenD_205 b hb)
def required_213 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (0, -1), (1, 0), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_213 : Finset Cell := ⟨(([(-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_213 : Fin 2 → Finset Cell := ![(placedSet 0 (3, 1) required_6), (placedSet 0 (-1, 1) required_191)]
def childrenD_213 : Fin 2 → Finset Cell := ![(placedSet 0 (3, 1) envelope_6), (placedSet 0 (-1, 1) envelope_191)]
theorem common_sub_213 : commonEnvelope childrenD_213 ⊆ insert (0, 0) required_213 := by decide
theorem child_required_sub_213 : ∀ j, childrenC_213 j ⊆ insert (0, 0) required_213 := by decide
theorem child_envelope_sub_213 : ∀ j, childrenD_213 j ⊆ envelope_213 := by decide
theorem pivot_mem_213 : (0, 0) ∈ envelope_213 := by decide
theorem children_work_213 : ∀ j, Template HasSnaky 7 (childrenC_213 j) (childrenD_213 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_191 0 (-1, 1)).mono (by decide)
theorem row_works_213 : Template HasSnaky 8 required_213 envelope_213 := by
  refine compose HasSnaky 7 childrenC_213 childrenD_213 children_work_213 (0, 0)
    required_213 envelope_213 pivot_mem_213 child_required_sub_213 child_envelope_sub_213 ?_
  intro b hb; exact common_sub_213 (mem_commonEnvelope childrenD_213 b hb)
def required_219 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -1), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_219 : Finset Cell := ⟨(([(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_219 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) required_0), (placedSet 2 (2, 0) required_179)]
def childrenD_219 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) envelope_0), (placedSet 2 (2, 0) envelope_179)]
theorem common_sub_219 : commonEnvelope childrenD_219 ⊆ insert (0, 0) required_219 := by decide
theorem child_required_sub_219 : ∀ j, childrenC_219 j ⊆ insert (0, 0) required_219 := by decide
theorem child_envelope_sub_219 : ∀ j, childrenD_219 j ⊆ envelope_219 := by decide
theorem pivot_mem_219 : (0, 0) ∈ envelope_219 := by decide
theorem children_work_219 : ∀ j, Template HasSnaky 7 (childrenC_219 j) (childrenD_219 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_179 2 (2, 0)).mono (by decide)
theorem row_works_219 : Template HasSnaky 8 required_219 envelope_219 := by
  refine compose HasSnaky 7 childrenC_219 childrenD_219 children_work_219 (0, 0)
    required_219 envelope_219 pivot_mem_219 child_required_sub_219 child_envelope_sub_219 ?_
  intro b hb; exact common_sub_219 (mem_commonEnvelope childrenD_219 b hb)
def required_224 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (1, -2), (2, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_224 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_224 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (2, -1) required_212)]
def childrenD_224 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (2, -1) envelope_212)]
theorem common_sub_224 : commonEnvelope childrenD_224 ⊆ insert (0, 0) required_224 := by decide
theorem child_required_sub_224 : ∀ j, childrenC_224 j ⊆ insert (0, 0) required_224 := by decide
theorem child_envelope_sub_224 : ∀ j, childrenD_224 j ⊆ envelope_224 := by decide
theorem pivot_mem_224 : (0, 0) ∈ envelope_224 := by decide
theorem children_work_224 : ∀ j, Template HasSnaky 7 (childrenC_224 j) (childrenD_224 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_212 0 (2, -1)).mono (by decide)
theorem row_works_224 : Template HasSnaky 8 required_224 envelope_224 := by
  refine compose HasSnaky 7 childrenC_224 childrenD_224 children_work_224 (0, 0)
    required_224 envelope_224 pivot_mem_224 child_required_sub_224 child_envelope_sub_224 ?_
  intro b hb; exact common_sub_224 (mem_commonEnvelope childrenD_224 b hb)
def required_226 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_226 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_226 : Fin 4 → Finset Cell := ![(placedSet 6 (-4, -1) required_10), (placedSet 0 (1, 0) required_203), (placedSet 0 (-2, -1) required_33), (placedSet 0 (-2, 0) required_193)]
def childrenD_226 : Fin 4 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_10), (placedSet 0 (1, 0) envelope_203), (placedSet 0 (-2, -1) envelope_33), (placedSet 0 (-2, 0) envelope_193)]
theorem common_sub_226 : commonEnvelope childrenD_226 ⊆ insert (0, 0) required_226 := by decide
theorem child_required_sub_226 : ∀ j, childrenC_226 j ⊆ insert (0, 0) required_226 := by decide
theorem child_envelope_sub_226 : ∀ j, childrenD_226 j ⊆ envelope_226 := by decide
theorem pivot_mem_226 : (0, 0) ∈ envelope_226 := by decide
theorem children_work_226 : ∀ j, Template HasSnaky 7 (childrenC_226 j) (childrenD_226 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_10 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_203 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_33 0 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_193 0 (-2, 0)).mono (by decide)
theorem row_works_226 : Template HasSnaky 8 required_226 envelope_226 := by
  refine compose HasSnaky 7 childrenC_226 childrenD_226 children_work_226 (0, 0)
    required_226 envelope_226 pivot_mem_226 child_required_sub_226 child_envelope_sub_226 ?_
  intro b hb; exact common_sub_226 (mem_commonEnvelope childrenD_226 b hb)
end SnakyConditional

end OAI
