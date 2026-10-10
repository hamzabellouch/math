import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part03
import OAI.GameTheory.SnakyConditional.Templates.Level08Part04
import OAI.GameTheory.SnakyConditional.Templates.Level08Part05

namespace OAI

namespace SnakyConditional
def required_234 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_234 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_234 : Fin 4 → Finset Cell := ![(placedSet 4 (0, 1) required_180), (placedSet 0 (-1, 0) required_37), (placedSet 0 (1, -1) required_129), (placedSet 0 (-1, 1) required_63)]
def childrenD_234 : Fin 4 → Finset Cell := ![(placedSet 4 (0, 1) envelope_180), (placedSet 0 (-1, 0) envelope_37), (placedSet 0 (1, -1) envelope_129), (placedSet 0 (-1, 1) envelope_63)]
theorem common_sub_234 : commonEnvelope childrenD_234 ⊆ insert (0, 0) required_234 := by decide
theorem child_required_sub_234 : ∀ j, childrenC_234 j ⊆ insert (0, 0) required_234 := by decide
theorem child_envelope_sub_234 : ∀ j, childrenD_234 j ⊆ envelope_234 := by decide
theorem pivot_mem_234 : (0, 0) ∈ envelope_234 := by decide
theorem children_work_234 : ∀ j, Template HasSnaky 6 (childrenC_234 j) (childrenD_234 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_180 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_37 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_129 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
theorem row_works_234 : Template HasSnaky 7 required_234 envelope_234 := by
  refine compose HasSnaky 6 childrenC_234 childrenD_234 children_work_234 (0, 0)
    required_234 envelope_234 pivot_mem_234 child_required_sub_234 child_envelope_sub_234 ?_
  intro b hb; exact common_sub_234 (mem_commonEnvelope childrenD_234 b hb)
def required_235 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1), (1, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_235 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_235 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) required_7), (placedSet 0 (2, 0) required_110), (placedSet 0 (-1, 1) required_70)]
def childrenD_235 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) envelope_7), (placedSet 0 (2, 0) envelope_110), (placedSet 0 (-1, 1) envelope_70)]
theorem common_sub_235 : commonEnvelope childrenD_235 ⊆ insert (0, 0) required_235 := by decide
theorem child_required_sub_235 : ∀ j, childrenC_235 j ⊆ insert (0, 0) required_235 := by decide
theorem child_envelope_sub_235 : ∀ j, childrenD_235 j ⊆ envelope_235 := by decide
theorem pivot_mem_235 : (0, 0) ∈ envelope_235 := by decide
theorem children_work_235 : ∀ j, Template HasSnaky 6 (childrenC_235 j) (childrenD_235 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_110 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_70 0 (-1, 1)).mono (by decide)
theorem row_works_235 : Template HasSnaky 7 required_235 envelope_235 := by
  refine compose HasSnaky 6 childrenC_235 childrenD_235 children_work_235 (0, 0)
    required_235 envelope_235 pivot_mem_235 child_required_sub_235 child_envelope_sub_235 ?_
  intro b hb; exact common_sub_235 (mem_commonEnvelope childrenD_235 b hb)
def required_237 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_237 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_237 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (3, 0) required_172)]
def childrenD_237 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (3, 0) envelope_172)]
theorem common_sub_237 : commonEnvelope childrenD_237 ⊆ insert (0, 0) required_237 := by decide
theorem child_required_sub_237 : ∀ j, childrenC_237 j ⊆ insert (0, 0) required_237 := by decide
theorem child_envelope_sub_237 : ∀ j, childrenD_237 j ⊆ envelope_237 := by decide
theorem pivot_mem_237 : (0, 0) ∈ envelope_237 := by decide
theorem children_work_237 : ∀ j, Template HasSnaky 6 (childrenC_237 j) (childrenD_237 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_172 0 (3, 0)).mono (by decide)
theorem row_works_237 : Template HasSnaky 7 required_237 envelope_237 := by
  refine compose HasSnaky 6 childrenC_237 childrenD_237 children_work_237 (0, 0)
    required_237 envelope_237 pivot_mem_237 child_required_sub_237 child_envelope_sub_237 ?_
  intro b hb; exact common_sub_237 (mem_commonEnvelope childrenD_237 b hb)
def required_238 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_238 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_238 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 5 (3, 0) required_178)]
def childrenD_238 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 5 (3, 0) envelope_178)]
theorem common_sub_238 : commonEnvelope childrenD_238 ⊆ insert (0, 0) required_238 := by decide
theorem child_required_sub_238 : ∀ j, childrenC_238 j ⊆ insert (0, 0) required_238 := by decide
theorem child_envelope_sub_238 : ∀ j, childrenD_238 j ⊆ envelope_238 := by decide
theorem pivot_mem_238 : (0, 0) ∈ envelope_238 := by decide
theorem children_work_238 : ∀ j, Template HasSnaky 6 (childrenC_238 j) (childrenD_238 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_178 5 (3, 0)).mono (by decide)
theorem row_works_238 : Template HasSnaky 7 required_238 envelope_238 := by
  refine compose HasSnaky 6 childrenC_238 childrenD_238 children_work_238 (0, 0)
    required_238 envelope_238 pivot_mem_238 child_required_sub_238 child_envelope_sub_238 ?_
  intro b hb; exact common_sub_238 (mem_commonEnvelope childrenD_238 b hb)
def required_239 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_239 : Finset Cell := ⟨(([(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_239 : Fin 2 → Finset Cell := ![(placedSet 4 (3, -1) required_0), (placedSet 4 (-1, 1) required_174)]
def childrenD_239 : Fin 2 → Finset Cell := ![(placedSet 4 (3, -1) envelope_0), (placedSet 4 (-1, 1) envelope_174)]
theorem common_sub_239 : commonEnvelope childrenD_239 ⊆ insert (0, 0) required_239 := by decide
theorem child_required_sub_239 : ∀ j, childrenC_239 j ⊆ insert (0, 0) required_239 := by decide
theorem child_envelope_sub_239 : ∀ j, childrenD_239 j ⊆ envelope_239 := by decide
theorem pivot_mem_239 : (0, 0) ∈ envelope_239 := by decide
theorem children_work_239 : ∀ j, Template HasSnaky 6 (childrenC_239 j) (childrenD_239 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 4 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_174 4 (-1, 1)).mono (by decide)
theorem row_works_239 : Template HasSnaky 7 required_239 envelope_239 := by
  refine compose HasSnaky 6 childrenC_239 childrenD_239 children_work_239 (0, 0)
    required_239 envelope_239 pivot_mem_239 child_required_sub_239 child_envelope_sub_239 ?_
  intro b hb; exact common_sub_239 (mem_commonEnvelope childrenD_239 b hb)
def required_241 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_241 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_241 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 0) required_131), (placedSet 1 (1, 0) required_159), (placedSet 0 (0, 1) required_61)]
def childrenD_241 : Fin 3 → Finset Cell := ![(placedSet 1 (1, 0) envelope_131), (placedSet 1 (1, 0) envelope_159), (placedSet 0 (0, 1) envelope_61)]
theorem common_sub_241 : commonEnvelope childrenD_241 ⊆ insert (0, 0) required_241 := by decide
theorem child_required_sub_241 : ∀ j, childrenC_241 j ⊆ insert (0, 0) required_241 := by decide
theorem child_envelope_sub_241 : ∀ j, childrenD_241 j ⊆ envelope_241 := by decide
theorem pivot_mem_241 : (0, 0) ∈ envelope_241 := by decide
theorem children_work_241 : ∀ j, Template HasSnaky 6 (childrenC_241 j) (childrenD_241 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_131 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_159 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_61 0 (0, 1)).mono (by decide)
theorem row_works_241 : Template HasSnaky 7 required_241 envelope_241 := by
  refine compose HasSnaky 6 childrenC_241 childrenD_241 children_work_241 (0, 0)
    required_241 envelope_241 pivot_mem_241 child_required_sub_241 child_envelope_sub_241 ?_
  intro b hb; exact common_sub_241 (mem_commonEnvelope childrenD_241 b hb)
end SnakyConditional

end OAI
