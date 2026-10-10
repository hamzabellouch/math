import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part03
import OAI.GameTheory.SnakyConditional.Templates.Level08Part05
import OAI.GameTheory.SnakyConditional.Templates.Level08Part07

namespace OAI

namespace SnakyConditional
def required_221 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_221 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_221 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 5 (1, 0) required_180)]
def childrenD_221 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 5 (1, 0) envelope_180)]
theorem common_sub_221 : commonEnvelope childrenD_221 ⊆ insert (0, 0) required_221 := by decide
theorem child_required_sub_221 : ∀ j, childrenC_221 j ⊆ insert (0, 0) required_221 := by decide
theorem child_envelope_sub_221 : ∀ j, childrenD_221 j ⊆ envelope_221 := by decide
theorem pivot_mem_221 : (0, 0) ∈ envelope_221 := by decide
theorem children_work_221 : ∀ j, Template HasSnaky 6 (childrenC_221 j) (childrenD_221 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_180 5 (1, 0)).mono (by decide)
theorem row_works_221 : Template HasSnaky 7 required_221 envelope_221 := by
  refine compose HasSnaky 6 childrenC_221 childrenD_221 children_work_221 (0, 0)
    required_221 envelope_221 pivot_mem_221 child_required_sub_221 child_envelope_sub_221 ?_
  intro b hb; exact common_sub_221 (mem_commonEnvelope childrenD_221 b hb)
def required_223 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_223 : Finset Cell := ⟨(([(-5, 0), (-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_223 : Fin 5 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 2 (1, 0) required_135), (placedSet 0 (-1, -1) required_128), (placedSet 3 (0, -1) required_111), (placedSet 0 (1, 0) required_127)]
def childrenD_223 : Fin 5 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 2 (1, 0) envelope_135), (placedSet 0 (-1, -1) envelope_128), (placedSet 3 (0, -1) envelope_111), (placedSet 0 (1, 0) envelope_127)]
theorem common_sub_223 : commonEnvelope childrenD_223 ⊆ insert (0, 0) required_223 := by decide
theorem child_required_sub_223 : ∀ j, childrenC_223 j ⊆ insert (0, 0) required_223 := by decide
theorem child_envelope_sub_223 : ∀ j, childrenD_223 j ⊆ envelope_223 := by decide
theorem pivot_mem_223 : (0, 0) ∈ envelope_223 := by decide
theorem children_work_223 : ∀ j, Template HasSnaky 6 (childrenC_223 j) (childrenD_223 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_135 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_128 0 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_111 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_127 0 (1, 0)).mono (by decide)
theorem row_works_223 : Template HasSnaky 7 required_223 envelope_223 := by
  refine compose HasSnaky 6 childrenC_223 childrenD_223 children_work_223 (0, 0)
    required_223 envelope_223 pivot_mem_223 child_required_sub_223 child_envelope_sub_223 ?_
  intro b hb; exact common_sub_223 (mem_commonEnvelope childrenD_223 b hb)
def required_225 : Finset Cell := ⟨(([(1, -2), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_225 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (2, 2), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_225 : Fin 2 → Finset Cell := ![(placedSet 7 (3, 1) required_111), (placedSet 4 (0, 1) required_61)]
def childrenD_225 : Fin 2 → Finset Cell := ![(placedSet 7 (3, 1) envelope_111), (placedSet 4 (0, 1) envelope_61)]
theorem common_sub_225 : commonEnvelope childrenD_225 ⊆ insert (0, 0) required_225 := by decide
theorem child_required_sub_225 : ∀ j, childrenC_225 j ⊆ insert (0, 0) required_225 := by decide
theorem child_envelope_sub_225 : ∀ j, childrenD_225 j ⊆ envelope_225 := by decide
theorem pivot_mem_225 : (0, 0) ∈ envelope_225 := by decide
theorem children_work_225 : ∀ j, Template HasSnaky 6 (childrenC_225 j) (childrenD_225 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_111 7 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_61 4 (0, 1)).mono (by decide)
theorem row_works_225 : Template HasSnaky 7 required_225 envelope_225 := by
  refine compose HasSnaky 6 childrenC_225 childrenD_225 children_work_225 (0, 0)
    required_225 envelope_225 pivot_mem_225 child_required_sub_225 child_envelope_sub_225 ?_
  intro b hb; exact common_sub_225 (mem_commonEnvelope childrenD_225 b hb)
def required_229 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_229 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_229 : Fin 3 → Finset Cell := ![(placedSet 0 (3, -1) required_171), (placedSet 1 (0, 1) required_45), (placedSet 3 (0, 1) required_46)]
def childrenD_229 : Fin 3 → Finset Cell := ![(placedSet 0 (3, -1) envelope_171), (placedSet 1 (0, 1) envelope_45), (placedSet 3 (0, 1) envelope_46)]
theorem common_sub_229 : commonEnvelope childrenD_229 ⊆ insert (0, 0) required_229 := by decide
theorem child_required_sub_229 : ∀ j, childrenC_229 j ⊆ insert (0, 0) required_229 := by decide
theorem child_envelope_sub_229 : ∀ j, childrenD_229 j ⊆ envelope_229 := by decide
theorem pivot_mem_229 : (0, 0) ∈ envelope_229 := by decide
theorem children_work_229 : ∀ j, Template HasSnaky 6 (childrenC_229 j) (childrenD_229 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_171 0 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_45 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_46 3 (0, 1)).mono (by decide)
theorem row_works_229 : Template HasSnaky 7 required_229 envelope_229 := by
  refine compose HasSnaky 6 childrenC_229 childrenD_229 children_work_229 (0, 0)
    required_229 envelope_229 pivot_mem_229 child_required_sub_229 child_envelope_sub_229 ?_
  intro b hb; exact common_sub_229 (mem_commonEnvelope childrenD_229 b hb)
def required_231 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_231 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_231 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, 0) required_222)]
def childrenD_231 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, 0) envelope_222)]
theorem common_sub_231 : commonEnvelope childrenD_231 ⊆ insert (0, 0) required_231 := by decide
theorem child_required_sub_231 : ∀ j, childrenC_231 j ⊆ insert (0, 0) required_231 := by decide
theorem child_envelope_sub_231 : ∀ j, childrenD_231 j ⊆ envelope_231 := by decide
theorem pivot_mem_231 : (0, 0) ∈ envelope_231 := by decide
theorem children_work_231 : ∀ j, Template HasSnaky 6 (childrenC_231 j) (childrenD_231 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_222 0 (2, 0)).mono (by decide)
theorem row_works_231 : Template HasSnaky 7 required_231 envelope_231 := by
  refine compose HasSnaky 6 childrenC_231 childrenD_231 children_work_231 (0, 0)
    required_231 envelope_231 pivot_mem_231 child_required_sub_231 child_envelope_sub_231 ?_
  intro b hb; exact common_sub_231 (mem_commonEnvelope childrenD_231 b hb)
def required_232 : Finset Cell := ⟨(([(-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_232 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_232 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) required_24), (placedSet 1 (0, 2) required_107)]
def childrenD_232 : Fin 2 → Finset Cell := ![(placedSet 2 (1, 0) envelope_24), (placedSet 1 (0, 2) envelope_107)]
theorem common_sub_232 : commonEnvelope childrenD_232 ⊆ insert (0, 0) required_232 := by decide
theorem child_required_sub_232 : ∀ j, childrenC_232 j ⊆ insert (0, 0) required_232 := by decide
theorem child_envelope_sub_232 : ∀ j, childrenD_232 j ⊆ envelope_232 := by decide
theorem pivot_mem_232 : (0, 0) ∈ envelope_232 := by decide
theorem children_work_232 : ∀ j, Template HasSnaky 6 (childrenC_232 j) (childrenD_232 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_107 1 (0, 2)).mono (by decide)
theorem row_works_232 : Template HasSnaky 7 required_232 envelope_232 := by
  refine compose HasSnaky 6 childrenC_232 childrenD_232 children_work_232 (0, 0)
    required_232 envelope_232 pivot_mem_232 child_required_sub_232 child_envelope_sub_232 ?_
  intro b hb; exact common_sub_232 (mem_commonEnvelope childrenD_232 b hb)
end SnakyConditional

end OAI
