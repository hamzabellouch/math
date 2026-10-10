import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part02
import OAI.GameTheory.SnakyConditional.Templates.Level08Part04
import OAI.GameTheory.SnakyConditional.Templates.Level08Part07

namespace OAI

namespace SnakyConditional
def required_243 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (0, -1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_243 : Finset Cell := ⟨(([(-4, -2), (-3, -2), (-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_243 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (-2, 1) required_233)]
def childrenD_243 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (-2, 1) envelope_233)]
theorem common_sub_243 : commonEnvelope childrenD_243 ⊆ insert (0, 0) required_243 := by decide
theorem child_required_sub_243 : ∀ j, childrenC_243 j ⊆ insert (0, 0) required_243 := by decide
theorem child_envelope_sub_243 : ∀ j, childrenD_243 j ⊆ envelope_243 := by decide
theorem pivot_mem_243 : (0, 0) ∈ envelope_243 := by decide
theorem children_work_243 : ∀ j, Template HasSnaky 6 (childrenC_243 j) (childrenD_243 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_233 0 (-2, 1)).mono (by decide)
theorem row_works_243 : Template HasSnaky 7 required_243 envelope_243 := by
  refine compose HasSnaky 6 childrenC_243 childrenD_243 children_work_243 (0, 0)
    required_243 envelope_243 pivot_mem_243 child_required_sub_243 child_envelope_sub_243 ?_
  intro b hb; exact common_sub_243 (mem_commonEnvelope childrenD_243 b hb)
def required_244 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_244 : Finset Cell := ⟨(([(-5, 1), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_244 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 1) required_99), (placedSet 0 (0, 1) required_99), (placedSet 7 (-1, -1) required_11), (placedSet 2 (1, 0) required_173)]
def childrenD_244 : Fin 4 → Finset Cell := ![(placedSet 4 (-2, 1) envelope_99), (placedSet 0 (0, 1) envelope_99), (placedSet 7 (-1, -1) envelope_11), (placedSet 2 (1, 0) envelope_173)]
theorem common_sub_244 : commonEnvelope childrenD_244 ⊆ insert (0, 0) required_244 := by decide
theorem child_required_sub_244 : ∀ j, childrenC_244 j ⊆ insert (0, 0) required_244 := by decide
theorem child_envelope_sub_244 : ∀ j, childrenD_244 j ⊆ envelope_244 := by decide
theorem pivot_mem_244 : (0, 0) ∈ envelope_244 := by decide
theorem children_work_244 : ∀ j, Template HasSnaky 6 (childrenC_244 j) (childrenD_244 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_99 4 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_99 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_11 7 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_173 2 (1, 0)).mono (by decide)
theorem row_works_244 : Template HasSnaky 7 required_244 envelope_244 := by
  refine compose HasSnaky 6 childrenC_244 childrenD_244 children_work_244 (0, 0)
    required_244 envelope_244 pivot_mem_244 child_required_sub_244 child_envelope_sub_244 ?_
  intro b hb; exact common_sub_244 (mem_commonEnvelope childrenD_244 b hb)
def required_252 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_252 : Finset Cell := ⟨(([(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_252 : Fin 5 → Finset Cell := ![(placedSet 3 (0, -1) required_111), (placedSet 6 (1, 0) required_154), (placedSet 2 (1, 0) required_144), (placedSet 1 (1, -1) required_63), (placedSet 1 (1, 0) required_155)]
def childrenD_252 : Fin 5 → Finset Cell := ![(placedSet 3 (0, -1) envelope_111), (placedSet 6 (1, 0) envelope_154), (placedSet 2 (1, 0) envelope_144), (placedSet 1 (1, -1) envelope_63), (placedSet 1 (1, 0) envelope_155)]
theorem common_sub_252 : commonEnvelope childrenD_252 ⊆ insert (0, 0) required_252 := by decide
theorem child_required_sub_252 : ∀ j, childrenC_252 j ⊆ insert (0, 0) required_252 := by decide
theorem child_envelope_sub_252 : ∀ j, childrenD_252 j ⊆ envelope_252 := by decide
theorem pivot_mem_252 : (0, 0) ∈ envelope_252 := by decide
theorem children_work_252 : ∀ j, Template HasSnaky 6 (childrenC_252 j) (childrenD_252 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_111 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_154 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_144 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_155 1 (1, 0)).mono (by decide)
theorem row_works_252 : Template HasSnaky 7 required_252 envelope_252 := by
  refine compose HasSnaky 6 childrenC_252 childrenD_252 children_work_252 (0, 0)
    required_252 envelope_252 pivot_mem_252 child_required_sub_252 child_envelope_sub_252 ?_
  intro b hb; exact common_sub_252 (mem_commonEnvelope childrenD_252 b hb)
def required_253 : Finset Cell := ⟨(([(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_253 : Finset Cell := ⟨(([(-2, -4), (-1, -4), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_253 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) required_29), (placedSet 1 (2, -2) required_177)]
def childrenD_253 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -4) envelope_29), (placedSet 1 (2, -2) envelope_177)]
theorem common_sub_253 : commonEnvelope childrenD_253 ⊆ insert (0, 0) required_253 := by decide
theorem child_required_sub_253 : ∀ j, childrenC_253 j ⊆ insert (0, 0) required_253 := by decide
theorem child_envelope_sub_253 : ∀ j, childrenD_253 j ⊆ envelope_253 := by decide
theorem pivot_mem_253 : (0, 0) ∈ envelope_253 := by decide
theorem children_work_253 : ∀ j, Template HasSnaky 6 (childrenC_253 j) (childrenD_253 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_29 3 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_177 1 (2, -2)).mono (by decide)
theorem row_works_253 : Template HasSnaky 7 required_253 envelope_253 := by
  refine compose HasSnaky 6 childrenC_253 childrenD_253 children_work_253 (0, 0)
    required_253 envelope_253 pivot_mem_253 child_required_sub_253 child_envelope_sub_253 ?_
  intro b hb; exact common_sub_253 (mem_commonEnvelope childrenD_253 b hb)
def required_254 : Finset Cell := ⟨(([(0, -2), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_254 : Finset Cell := ⟨(([(-2, 2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_254 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 1) required_96), (placedSet 0 (4, 1) required_108)]
def childrenD_254 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 1) envelope_96), (placedSet 0 (4, 1) envelope_108)]
theorem common_sub_254 : commonEnvelope childrenD_254 ⊆ insert (0, 0) required_254 := by decide
theorem child_required_sub_254 : ∀ j, childrenC_254 j ⊆ insert (0, 0) required_254 := by decide
theorem child_envelope_sub_254 : ∀ j, childrenD_254 j ⊆ envelope_254 := by decide
theorem pivot_mem_254 : (0, 0) ∈ envelope_254 := by decide
theorem children_work_254 : ∀ j, Template HasSnaky 6 (childrenC_254 j) (childrenD_254 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_96 7 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_108 0 (4, 1)).mono (by decide)
theorem row_works_254 : Template HasSnaky 7 required_254 envelope_254 := by
  refine compose HasSnaky 6 childrenC_254 childrenD_254 children_work_254 (0, 0)
    required_254 envelope_254 pivot_mem_254 child_required_sub_254 child_envelope_sub_254 ?_
  intro b hb; exact common_sub_254 (mem_commonEnvelope childrenD_254 b hb)
def required_271 : Finset Cell := ⟨(([(0, -1), (0, 1), (1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_271 : Finset Cell := ⟨(([(-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_271 : Fin 2 → Finset Cell := ![(placedSet 2 (3, -1) required_107), (placedSet 3 (0, 2) required_107)]
def childrenD_271 : Fin 2 → Finset Cell := ![(placedSet 2 (3, -1) envelope_107), (placedSet 3 (0, 2) envelope_107)]
theorem common_sub_271 : commonEnvelope childrenD_271 ⊆ insert (0, 0) required_271 := by decide
theorem child_required_sub_271 : ∀ j, childrenC_271 j ⊆ insert (0, 0) required_271 := by decide
theorem child_envelope_sub_271 : ∀ j, childrenD_271 j ⊆ envelope_271 := by decide
theorem pivot_mem_271 : (0, 0) ∈ envelope_271 := by decide
theorem children_work_271 : ∀ j, Template HasSnaky 6 (childrenC_271 j) (childrenD_271 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_107 2 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_107 3 (0, 2)).mono (by decide)
theorem row_works_271 : Template HasSnaky 7 required_271 envelope_271 := by
  refine compose HasSnaky 6 childrenC_271 childrenD_271 children_work_271 (0, 0)
    required_271 envelope_271 pivot_mem_271 child_required_sub_271 child_envelope_sub_271 ?_
  intro b hb; exact common_sub_271 (mem_commonEnvelope childrenD_271 b hb)
end SnakyConditional

end OAI
