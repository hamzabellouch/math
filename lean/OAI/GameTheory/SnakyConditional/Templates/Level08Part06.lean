import OAI.GameTheory.SnakyConditional.Templates.Level07Part01
import OAI.GameTheory.SnakyConditional.Templates.Level07Part02
import OAI.GameTheory.SnakyConditional.Templates.Level07Part03
import OAI.GameTheory.SnakyConditional.Templates.Level07Part04
import OAI.GameTheory.SnakyConditional.Templates.Level07Part05

namespace OAI

namespace SnakyConditional
def required_198 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_198 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_198 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_7), (placedSet 1 (1, 0) required_131)]
def childrenD_198 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_7), (placedSet 1 (1, 0) envelope_131)]
theorem common_sub_198 : commonEnvelope childrenD_198 ⊆ insert (0, 0) required_198 := by decide
theorem child_required_sub_198 : ∀ j, childrenC_198 j ⊆ insert (0, 0) required_198 := by decide
theorem child_envelope_sub_198 : ∀ j, childrenD_198 j ⊆ envelope_198 := by decide
theorem pivot_mem_198 : (0, 0) ∈ envelope_198 := by decide
theorem children_work_198 : ∀ j, Template HasSnaky 5 (childrenC_198 j) (childrenD_198 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_131 1 (1, 0)).mono (by decide)
theorem row_works_198 : Template HasSnaky 6 required_198 envelope_198 := by
  refine compose HasSnaky 5 childrenC_198 childrenD_198 children_work_198 (0, 0)
    required_198 envelope_198 pivot_mem_198 child_required_sub_198 child_envelope_sub_198 ?_
  intro b hb; exact common_sub_198 (mem_commonEnvelope childrenD_198 b hb)
def required_199 : Finset Cell := ⟨(([(-1, -1), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_199 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_199 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) required_55), (placedSet 3 (1, -3) required_64), (placedSet 0 (-1, 0) required_84)]
def childrenD_199 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) envelope_55), (placedSet 3 (1, -3) envelope_64), (placedSet 0 (-1, 0) envelope_84)]
theorem common_sub_199 : commonEnvelope childrenD_199 ⊆ insert (0, 0) required_199 := by decide
theorem child_required_sub_199 : ∀ j, childrenC_199 j ⊆ insert (0, 0) required_199 := by decide
theorem child_envelope_sub_199 : ∀ j, childrenD_199 j ⊆ envelope_199 := by decide
theorem pivot_mem_199 : (0, 0) ∈ envelope_199 := by decide
theorem children_work_199 : ∀ j, Template HasSnaky 5 (childrenC_199 j) (childrenD_199 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_64 3 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_84 0 (-1, 0)).mono (by decide)
theorem row_works_199 : Template HasSnaky 6 required_199 envelope_199 := by
  refine compose HasSnaky 5 childrenC_199 childrenD_199 children_work_199 (0, 0)
    required_199 envelope_199 pivot_mem_199 child_required_sub_199 child_envelope_sub_199 ?_
  intro b hb; exact common_sub_199 (mem_commonEnvelope childrenD_199 b hb)
def required_200 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_200 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_200 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) required_103), (placedSet 3 (1, -3) required_64), (placedSet 1 (0, 1) required_55)]
def childrenD_200 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_103), (placedSet 3 (1, -3) envelope_64), (placedSet 1 (0, 1) envelope_55)]
theorem common_sub_200 : commonEnvelope childrenD_200 ⊆ insert (0, 0) required_200 := by decide
theorem child_required_sub_200 : ∀ j, childrenC_200 j ⊆ insert (0, 0) required_200 := by decide
theorem child_envelope_sub_200 : ∀ j, childrenD_200 j ⊆ envelope_200 := by decide
theorem pivot_mem_200 : (0, 0) ∈ envelope_200 := by decide
theorem children_work_200 : ∀ j, Template HasSnaky 5 (childrenC_200 j) (childrenD_200 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_103 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_64 3 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_55 1 (0, 1)).mono (by decide)
theorem row_works_200 : Template HasSnaky 6 required_200 envelope_200 := by
  refine compose HasSnaky 5 childrenC_200 childrenD_200 children_work_200 (0, 0)
    required_200 envelope_200 pivot_mem_200 child_required_sub_200 child_envelope_sub_200 ?_
  intro b hb; exact common_sub_200 (mem_commonEnvelope childrenD_200 b hb)
def required_206 : Finset Cell := ⟨(([(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_206 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_206 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_28), (placedSet 2 (4, 0) required_135)]
def childrenD_206 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_28), (placedSet 2 (4, 0) envelope_135)]
theorem common_sub_206 : commonEnvelope childrenD_206 ⊆ insert (0, 0) required_206 := by decide
theorem child_required_sub_206 : ∀ j, childrenC_206 j ⊆ insert (0, 0) required_206 := by decide
theorem child_envelope_sub_206 : ∀ j, childrenD_206 j ⊆ envelope_206 := by decide
theorem pivot_mem_206 : (0, 0) ∈ envelope_206 := by decide
theorem children_work_206 : ∀ j, Template HasSnaky 5 (childrenC_206 j) (childrenD_206 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_28 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_135 2 (4, 0)).mono (by decide)
theorem row_works_206 : Template HasSnaky 6 required_206 envelope_206 := by
  refine compose HasSnaky 5 childrenC_206 childrenD_206 children_work_206 (0, 0)
    required_206 envelope_206 pivot_mem_206 child_required_sub_206 child_envelope_sub_206 ?_
  intro b hb; exact common_sub_206 (mem_commonEnvelope childrenD_206 b hb)
def required_207 : Finset Cell := ⟨(([(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_207 : Finset Cell := ⟨(([(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_207 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_28), (placedSet 0 (4, 0) required_127)]
def childrenD_207 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_28), (placedSet 0 (4, 0) envelope_127)]
theorem common_sub_207 : commonEnvelope childrenD_207 ⊆ insert (0, 0) required_207 := by decide
theorem child_required_sub_207 : ∀ j, childrenC_207 j ⊆ insert (0, 0) required_207 := by decide
theorem child_envelope_sub_207 : ∀ j, childrenD_207 j ⊆ envelope_207 := by decide
theorem pivot_mem_207 : (0, 0) ∈ envelope_207 := by decide
theorem children_work_207 : ∀ j, Template HasSnaky 5 (childrenC_207 j) (childrenD_207 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_28 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_127 0 (4, 0)).mono (by decide)
theorem row_works_207 : Template HasSnaky 6 required_207 envelope_207 := by
  refine compose HasSnaky 5 childrenC_207 childrenD_207 children_work_207 (0, 0)
    required_207 envelope_207 pivot_mem_207 child_required_sub_207 child_envelope_sub_207 ?_
  intro b hb; exact common_sub_207 (mem_commonEnvelope childrenD_207 b hb)
def required_208 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_208 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_208 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) required_7), (placedSet 0 (1, 0) required_127)]
def childrenD_208 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 1) envelope_7), (placedSet 0 (1, 0) envelope_127)]
theorem common_sub_208 : commonEnvelope childrenD_208 ⊆ insert (0, 0) required_208 := by decide
theorem child_required_sub_208 : ∀ j, childrenC_208 j ⊆ insert (0, 0) required_208 := by decide
theorem child_envelope_sub_208 : ∀ j, childrenD_208 j ⊆ envelope_208 := by decide
theorem pivot_mem_208 : (0, 0) ∈ envelope_208 := by decide
theorem children_work_208 : ∀ j, Template HasSnaky 5 (childrenC_208 j) (childrenD_208 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 4 (-4, 1)).mono (by decide)
  · exact (placed_template_map row_works_127 0 (1, 0)).mono (by decide)
theorem row_works_208 : Template HasSnaky 6 required_208 envelope_208 := by
  refine compose HasSnaky 5 childrenC_208 childrenD_208 children_work_208 (0, 0)
    required_208 envelope_208 pivot_mem_208 child_required_sub_208 child_envelope_sub_208 ?_
  intro b hb; exact common_sub_208 (mem_commonEnvelope childrenD_208 b hb)
def required_210 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_210 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_210 : Fin 3 → Finset Cell := ![(placedSet 2 (1, 0) required_58), (placedSet 0 (1, 0) required_57), (placedSet 1 (0, 1) required_117)]
def childrenD_210 : Fin 3 → Finset Cell := ![(placedSet 2 (1, 0) envelope_58), (placedSet 0 (1, 0) envelope_57), (placedSet 1 (0, 1) envelope_117)]
theorem common_sub_210 : commonEnvelope childrenD_210 ⊆ insert (0, 0) required_210 := by decide
theorem child_required_sub_210 : ∀ j, childrenC_210 j ⊆ insert (0, 0) required_210 := by decide
theorem child_envelope_sub_210 : ∀ j, childrenD_210 j ⊆ envelope_210 := by decide
theorem pivot_mem_210 : (0, 0) ∈ envelope_210 := by decide
theorem children_work_210 : ∀ j, Template HasSnaky 5 (childrenC_210 j) (childrenD_210 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_58 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_57 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_117 1 (0, 1)).mono (by decide)
theorem row_works_210 : Template HasSnaky 6 required_210 envelope_210 := by
  refine compose HasSnaky 5 childrenC_210 childrenD_210 children_work_210 (0, 0)
    required_210 envelope_210 pivot_mem_210 child_required_sub_210 child_envelope_sub_210 ?_
  intro b hb; exact common_sub_210 (mem_commonEnvelope childrenD_210 b hb)
end SnakyConditional

end OAI
