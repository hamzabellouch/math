import OAI.GameTheory.SnakyConditional.Templates.Level06Part04
import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part02
import OAI.GameTheory.SnakyConditional.Templates.Level08Part03

namespace OAI

namespace SnakyConditional
def required_187 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -3), (1, -1), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_187 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_187 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 3 (0, 1) required_108)]
def childrenD_187 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 3 (0, 1) envelope_108)]
theorem common_sub_187 : commonEnvelope childrenD_187 ⊆ insert (0, 0) required_187 := by decide
theorem child_required_sub_187 : ∀ j, childrenC_187 j ⊆ insert (0, 0) required_187 := by decide
theorem child_envelope_sub_187 : ∀ j, childrenD_187 j ⊆ envelope_187 := by decide
theorem pivot_mem_187 : (0, 0) ∈ envelope_187 := by decide
theorem children_work_187 : ∀ j, Template HasSnaky 6 (childrenC_187 j) (childrenD_187 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_108 3 (0, 1)).mono (by decide)
theorem row_works_187 : Template HasSnaky 7 required_187 envelope_187 := by
  refine compose HasSnaky 6 childrenC_187 childrenD_187 children_work_187 (0, 0)
    required_187 envelope_187 pivot_mem_187 child_required_sub_187 child_envelope_sub_187 ?_
  intro b hb; exact common_sub_187 (mem_commonEnvelope childrenD_187 b hb)
def required_190 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_190 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_190 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_46), (placedSet 2 (-1, -1) required_85), (placedSet 3 (0, -1) required_111)]
def childrenD_190 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_46), (placedSet 2 (-1, -1) envelope_85), (placedSet 3 (0, -1) envelope_111)]
theorem common_sub_190 : commonEnvelope childrenD_190 ⊆ insert (0, 0) required_190 := by decide
theorem child_required_sub_190 : ∀ j, childrenC_190 j ⊆ insert (0, 0) required_190 := by decide
theorem child_envelope_sub_190 : ∀ j, childrenD_190 j ⊆ envelope_190 := by decide
theorem pivot_mem_190 : (0, 0) ∈ envelope_190 := by decide
theorem children_work_190 : ∀ j, Template HasSnaky 6 (childrenC_190 j) (childrenD_190 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_46 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_85 2 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_111 3 (0, -1)).mono (by decide)
theorem row_works_190 : Template HasSnaky 7 required_190 envelope_190 := by
  refine compose HasSnaky 6 childrenC_190 childrenD_190 children_work_190 (0, 0)
    required_190 envelope_190 pivot_mem_190 child_required_sub_190 child_envelope_sub_190 ?_
  intro b hb; exact common_sub_190 (mem_commonEnvelope childrenD_190 b hb)
def required_191 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -2), (1, -1), (2, -1), (3, -1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_191 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_191 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) required_6), (placedSet 0 (0, 1) required_145)]
def childrenD_191 : Fin 2 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_6), (placedSet 0 (0, 1) envelope_145)]
theorem common_sub_191 : commonEnvelope childrenD_191 ⊆ insert (0, 0) required_191 := by decide
theorem child_required_sub_191 : ∀ j, childrenC_191 j ⊆ insert (0, 0) required_191 := by decide
theorem child_envelope_sub_191 : ∀ j, childrenD_191 j ⊆ envelope_191 := by decide
theorem pivot_mem_191 : (0, 0) ∈ envelope_191 := by decide
theorem children_work_191 : ∀ j, Template HasSnaky 6 (childrenC_191 j) (childrenD_191 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_145 0 (0, 1)).mono (by decide)
theorem row_works_191 : Template HasSnaky 7 required_191 envelope_191 := by
  refine compose HasSnaky 6 childrenC_191 childrenD_191 children_work_191 (0, 0)
    required_191 envelope_191 pivot_mem_191 child_required_sub_191 child_envelope_sub_191 ?_
  intro b hb; exact common_sub_191 (mem_commonEnvelope childrenD_191 b hb)
def required_193 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (1, -1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_193 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_193 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) required_6), (placedSet 1 (3, 0) required_162)]
def childrenD_193 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_6), (placedSet 1 (3, 0) envelope_162)]
theorem common_sub_193 : commonEnvelope childrenD_193 ⊆ insert (0, 0) required_193 := by decide
theorem child_required_sub_193 : ∀ j, childrenC_193 j ⊆ insert (0, 0) required_193 := by decide
theorem child_envelope_sub_193 : ∀ j, childrenD_193 j ⊆ envelope_193 := by decide
theorem pivot_mem_193 : (0, 0) ∈ envelope_193 := by decide
theorem children_work_193 : ∀ j, Template HasSnaky 6 (childrenC_193 j) (childrenD_193 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_162 1 (3, 0)).mono (by decide)
theorem row_works_193 : Template HasSnaky 7 required_193 envelope_193 := by
  refine compose HasSnaky 6 childrenC_193 childrenD_193 children_work_193 (0, 0)
    required_193 envelope_193 pivot_mem_193 child_required_sub_193 child_envelope_sub_193 ?_
  intro b hb; exact common_sub_193 (mem_commonEnvelope childrenD_193 b hb)
def required_195 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_195 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_195 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 1 (1, 0) required_162)]
def childrenD_195 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 1 (1, 0) envelope_162)]
theorem common_sub_195 : commonEnvelope childrenD_195 ⊆ insert (0, 0) required_195 := by decide
theorem child_required_sub_195 : ∀ j, childrenC_195 j ⊆ insert (0, 0) required_195 := by decide
theorem child_envelope_sub_195 : ∀ j, childrenD_195 j ⊆ envelope_195 := by decide
theorem pivot_mem_195 : (0, 0) ∈ envelope_195 := by decide
theorem children_work_195 : ∀ j, Template HasSnaky 6 (childrenC_195 j) (childrenD_195 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_162 1 (1, 0)).mono (by decide)
theorem row_works_195 : Template HasSnaky 7 required_195 envelope_195 := by
  refine compose HasSnaky 6 childrenC_195 childrenD_195 children_work_195 (0, 0)
    required_195 envelope_195 pivot_mem_195 child_required_sub_195 child_envelope_sub_195 ?_
  intro b hb; exact common_sub_195 (mem_commonEnvelope childrenD_195 b hb)
def required_202 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_202 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_202 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_150), (placedSet 0 (0, 1) required_7), (placedSet 0 (1, 0) required_108)]
def childrenD_202 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_150), (placedSet 0 (0, 1) envelope_7), (placedSet 0 (1, 0) envelope_108)]
theorem common_sub_202 : commonEnvelope childrenD_202 ⊆ insert (0, 0) required_202 := by decide
theorem child_required_sub_202 : ∀ j, childrenC_202 j ⊆ insert (0, 0) required_202 := by decide
theorem child_envelope_sub_202 : ∀ j, childrenD_202 j ⊆ envelope_202 := by decide
theorem pivot_mem_202 : (0, 0) ∈ envelope_202 := by decide
theorem children_work_202 : ∀ j, Template HasSnaky 6 (childrenC_202 j) (childrenD_202 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_150 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_108 0 (1, 0)).mono (by decide)
theorem row_works_202 : Template HasSnaky 7 required_202 envelope_202 := by
  refine compose HasSnaky 6 childrenC_202 childrenD_202 children_work_202 (0, 0)
    required_202 envelope_202 pivot_mem_202 child_required_sub_202 child_envelope_sub_202 ?_
  intro b hb; exact common_sub_202 (mem_commonEnvelope childrenD_202 b hb)
end SnakyConditional

end OAI
