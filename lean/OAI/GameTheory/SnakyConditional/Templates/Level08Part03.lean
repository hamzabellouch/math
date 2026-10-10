import OAI.GameTheory.SnakyConditional.Templates.Level07Part01
import OAI.GameTheory.SnakyConditional.Templates.Level07Part02
import OAI.GameTheory.SnakyConditional.Templates.Level07Part04
import OAI.GameTheory.SnakyConditional.Templates.Level07Part06

namespace OAI

namespace SnakyConditional
def required_159 : Finset Cell := ⟨(([(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_159 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_159 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_45), (placedSet 1 (0, 1) required_65), (placedSet 3 (-1, 0) required_7)]
def childrenD_159 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_45), (placedSet 1 (0, 1) envelope_65), (placedSet 3 (-1, 0) envelope_7)]
theorem common_sub_159 : commonEnvelope childrenD_159 ⊆ insert (0, 0) required_159 := by decide
theorem child_required_sub_159 : ∀ j, childrenC_159 j ⊆ insert (0, 0) required_159 := by decide
theorem child_envelope_sub_159 : ∀ j, childrenD_159 j ⊆ envelope_159 := by decide
theorem pivot_mem_159 : (0, 0) ∈ envelope_159 := by decide
theorem children_work_159 : ∀ j, Template HasSnaky 5 (childrenC_159 j) (childrenD_159 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_45 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_65 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
theorem row_works_159 : Template HasSnaky 6 required_159 envelope_159 := by
  refine compose HasSnaky 5 childrenC_159 childrenD_159 children_work_159 (0, 0)
    required_159 envelope_159 pivot_mem_159 child_required_sub_159 child_envelope_sub_159 ?_
  intro b hb; exact common_sub_159 (mem_commonEnvelope childrenD_159 b hb)
def required_160 : Finset Cell := ⟨(([(1, 0), (1, 1), (1, 2), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_160 : Finset Cell := ⟨(([(-1, -1), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_160 : Fin 2 → Finset Cell := ![(placedSet 1 (4, -1) required_63), (placedSet 3 (0, -1) required_32)]
def childrenD_160 : Fin 2 → Finset Cell := ![(placedSet 1 (4, -1) envelope_63), (placedSet 3 (0, -1) envelope_32)]
theorem common_sub_160 : commonEnvelope childrenD_160 ⊆ insert (0, 0) required_160 := by decide
theorem child_required_sub_160 : ∀ j, childrenC_160 j ⊆ insert (0, 0) required_160 := by decide
theorem child_envelope_sub_160 : ∀ j, childrenD_160 j ⊆ envelope_160 := by decide
theorem pivot_mem_160 : (0, 0) ∈ envelope_160 := by decide
theorem children_work_160 : ∀ j, Template HasSnaky 5 (childrenC_160 j) (childrenD_160 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (4, -1)).mono (by decide)
  · exact (placed_template_map row_works_32 3 (0, -1)).mono (by decide)
theorem row_works_160 : Template HasSnaky 6 required_160 envelope_160 := by
  refine compose HasSnaky 5 childrenC_160 childrenD_160 children_work_160 (0, 0)
    required_160 envelope_160 pivot_mem_160 child_required_sub_160 child_envelope_sub_160 ?_
  intro b hb; exact common_sub_160 (mem_commonEnvelope childrenD_160 b hb)
def required_161 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_161 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_161 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_15), (placedSet 0 (1, 0) required_86)]
def childrenD_161 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_15), (placedSet 0 (1, 0) envelope_86)]
theorem common_sub_161 : commonEnvelope childrenD_161 ⊆ insert (0, 0) required_161 := by decide
theorem child_required_sub_161 : ∀ j, childrenC_161 j ⊆ insert (0, 0) required_161 := by decide
theorem child_envelope_sub_161 : ∀ j, childrenD_161 j ⊆ envelope_161 := by decide
theorem pivot_mem_161 : (0, 0) ∈ envelope_161 := by decide
theorem children_work_161 : ∀ j, Template HasSnaky 5 (childrenC_161 j) (childrenD_161 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_15 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_86 0 (1, 0)).mono (by decide)
theorem row_works_161 : Template HasSnaky 6 required_161 envelope_161 := by
  refine compose HasSnaky 5 childrenC_161 childrenD_161 children_work_161 (0, 0)
    required_161 envelope_161 pivot_mem_161 child_required_sub_161 child_envelope_sub_161 ?_
  intro b hb; exact common_sub_161 (mem_commonEnvelope childrenD_161 b hb)
def required_162 : Finset Cell := ⟨(([(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_162 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_162 : Fin 4 → Finset Cell := ![(placedSet 3 (-1, 0) required_7), (placedSet 1 (0, 1) required_127), (placedSet 0 (-1, 1) required_63), (placedSet 0 (-1, -1) required_157)]
def childrenD_162 : Fin 4 → Finset Cell := ![(placedSet 3 (-1, 0) envelope_7), (placedSet 1 (0, 1) envelope_127), (placedSet 0 (-1, 1) envelope_63), (placedSet 0 (-1, -1) envelope_157)]
theorem common_sub_162 : commonEnvelope childrenD_162 ⊆ insert (0, 0) required_162 := by decide
theorem child_required_sub_162 : ∀ j, childrenC_162 j ⊆ insert (0, 0) required_162 := by decide
theorem child_envelope_sub_162 : ∀ j, childrenD_162 j ⊆ envelope_162 := by decide
theorem pivot_mem_162 : (0, 0) ∈ envelope_162 := by decide
theorem children_work_162 : ∀ j, Template HasSnaky 5 (childrenC_162 j) (childrenD_162 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_127 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_157 0 (-1, -1)).mono (by decide)
theorem row_works_162 : Template HasSnaky 6 required_162 envelope_162 := by
  refine compose HasSnaky 5 childrenC_162 childrenD_162 children_work_162 (0, 0)
    required_162 envelope_162 pivot_mem_162 child_required_sub_162 child_envelope_sub_162 ?_
  intro b hb; exact common_sub_162 (mem_commonEnvelope childrenD_162 b hb)
def required_169 : Finset Cell := ⟨(([(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_169 : Finset Cell := ⟨(([(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_169 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_28), (placedSet 1 (4, -1) required_63)]
def childrenD_169 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_28), (placedSet 1 (4, -1) envelope_63)]
theorem common_sub_169 : commonEnvelope childrenD_169 ⊆ insert (0, 0) required_169 := by decide
theorem child_required_sub_169 : ∀ j, childrenC_169 j ⊆ insert (0, 0) required_169 := by decide
theorem child_envelope_sub_169 : ∀ j, childrenD_169 j ⊆ envelope_169 := by decide
theorem pivot_mem_169 : (0, 0) ∈ envelope_169 := by decide
theorem children_work_169 : ∀ j, Template HasSnaky 5 (childrenC_169 j) (childrenD_169 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_28 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (4, -1)).mono (by decide)
theorem row_works_169 : Template HasSnaky 6 required_169 envelope_169 := by
  refine compose HasSnaky 5 childrenC_169 childrenD_169 children_work_169 (0, 0)
    required_169 envelope_169 pivot_mem_169 child_required_sub_169 child_envelope_sub_169 ?_
  intro b hb; exact common_sub_169 (mem_commonEnvelope childrenD_169 b hb)
def required_170 : Finset Cell := ⟨(([(-4, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_170 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_170 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) required_4), (placedSet 2 (1, 0) required_127)]
def childrenD_170 : Fin 2 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_4), (placedSet 2 (1, 0) envelope_127)]
theorem common_sub_170 : commonEnvelope childrenD_170 ⊆ insert (0, 0) required_170 := by decide
theorem child_required_sub_170 : ∀ j, childrenC_170 j ⊆ insert (0, 0) required_170 := by decide
theorem child_envelope_sub_170 : ∀ j, childrenD_170 j ⊆ envelope_170 := by decide
theorem pivot_mem_170 : (0, 0) ∈ envelope_170 := by decide
theorem children_work_170 : ∀ j, Template HasSnaky 5 (childrenC_170 j) (childrenD_170 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_127 2 (1, 0)).mono (by decide)
theorem row_works_170 : Template HasSnaky 6 required_170 envelope_170 := by
  refine compose HasSnaky 5 childrenC_170 childrenD_170 children_work_170 (0, 0)
    required_170 envelope_170 pivot_mem_170 child_required_sub_170 child_envelope_sub_170 ?_
  intro b hb; exact common_sub_170 (mem_commonEnvelope childrenD_170 b hb)
def required_171 : Finset Cell := ⟨(([(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_171 : Finset Cell := ⟨(([(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_171 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (-4, 1) required_91)]
def childrenD_171 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (-4, 1) envelope_91)]
theorem common_sub_171 : commonEnvelope childrenD_171 ⊆ insert (0, 0) required_171 := by decide
theorem child_required_sub_171 : ∀ j, childrenC_171 j ⊆ insert (0, 0) required_171 := by decide
theorem child_envelope_sub_171 : ∀ j, childrenD_171 j ⊆ envelope_171 := by decide
theorem pivot_mem_171 : (0, 0) ∈ envelope_171 := by decide
theorem children_work_171 : ∀ j, Template HasSnaky 5 (childrenC_171 j) (childrenD_171 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_91 0 (-4, 1)).mono (by decide)
theorem row_works_171 : Template HasSnaky 6 required_171 envelope_171 := by
  refine compose HasSnaky 5 childrenC_171 childrenD_171 children_work_171 (0, 0)
    required_171 envelope_171 pivot_mem_171 child_required_sub_171 child_envelope_sub_171 ?_
  intro b hb; exact common_sub_171 (mem_commonEnvelope childrenD_171 b hb)
end SnakyConditional

end OAI
