import OAI.GameTheory.SnakyConditional.Templates.Level06Part07
import OAI.GameTheory.SnakyConditional.Templates.Level07Part01
import OAI.GameTheory.SnakyConditional.Templates.Level07Part02
import OAI.GameTheory.SnakyConditional.Templates.Level07Part05

namespace OAI

namespace SnakyConditional
def required_172 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_172 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_172 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 6 (-4, 0) required_55), (placedSet 0 (-3, -1) required_64)]
def childrenD_172 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 6 (-4, 0) envelope_55), (placedSet 0 (-3, -1) envelope_64)]
theorem common_sub_172 : commonEnvelope childrenD_172 ⊆ insert (0, 0) required_172 := by decide
theorem child_required_sub_172 : ∀ j, childrenC_172 j ⊆ insert (0, 0) required_172 := by decide
theorem child_envelope_sub_172 : ∀ j, childrenD_172 j ⊆ envelope_172 := by decide
theorem pivot_mem_172 : (0, 0) ∈ envelope_172 := by decide
theorem children_work_172 : ∀ j, Template HasSnaky 5 (childrenC_172 j) (childrenD_172 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 6 (-4, 0)).mono (by decide)
  · exact (placed_template_map row_works_64 0 (-3, -1)).mono (by decide)
theorem row_works_172 : Template HasSnaky 6 required_172 envelope_172 := by
  refine compose HasSnaky 5 childrenC_172 childrenD_172 children_work_172 (0, 0)
    required_172 envelope_172 pivot_mem_172 child_required_sub_172 child_envelope_sub_172 ?_
  intro b hb; exact common_sub_172 (mem_commonEnvelope childrenD_172 b hb)
def required_173 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_173 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_173 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 6 (0, 1) required_64), (placedSet 6 (-4, 0) required_55)]
def childrenD_173 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 6 (0, 1) envelope_64), (placedSet 6 (-4, 0) envelope_55)]
theorem common_sub_173 : commonEnvelope childrenD_173 ⊆ insert (0, 0) required_173 := by decide
theorem child_required_sub_173 : ∀ j, childrenC_173 j ⊆ insert (0, 0) required_173 := by decide
theorem child_envelope_sub_173 : ∀ j, childrenD_173 j ⊆ envelope_173 := by decide
theorem pivot_mem_173 : (0, 0) ∈ envelope_173 := by decide
theorem children_work_173 : ∀ j, Template HasSnaky 5 (childrenC_173 j) (childrenD_173 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_64 6 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 6 (-4, 0)).mono (by decide)
theorem row_works_173 : Template HasSnaky 6 required_173 envelope_173 := by
  refine compose HasSnaky 5 childrenC_173 childrenD_173 children_work_173 (0, 0)
    required_173 envelope_173 pivot_mem_173 child_required_sub_173 child_envelope_sub_173 ?_
  intro b hb; exact common_sub_173 (mem_commonEnvelope childrenD_173 b hb)
def required_174 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_174 : Finset Cell := ⟨(([(-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_174 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_58), (placedSet 1 (0, 1) required_57), (placedSet 0 (-1, 0) required_84)]
def childrenD_174 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_58), (placedSet 1 (0, 1) envelope_57), (placedSet 0 (-1, 0) envelope_84)]
theorem common_sub_174 : commonEnvelope childrenD_174 ⊆ insert (0, 0) required_174 := by decide
theorem child_required_sub_174 : ∀ j, childrenC_174 j ⊆ insert (0, 0) required_174 := by decide
theorem child_envelope_sub_174 : ∀ j, childrenD_174 j ⊆ envelope_174 := by decide
theorem pivot_mem_174 : (0, 0) ∈ envelope_174 := by decide
theorem children_work_174 : ∀ j, Template HasSnaky 5 (childrenC_174 j) (childrenD_174 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_58 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_57 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_84 0 (-1, 0)).mono (by decide)
theorem row_works_174 : Template HasSnaky 6 required_174 envelope_174 := by
  refine compose HasSnaky 5 childrenC_174 childrenD_174 children_work_174 (0, 0)
    required_174 envelope_174 pivot_mem_174 child_required_sub_174 child_envelope_sub_174 ?_
  intro b hb; exact common_sub_174 (mem_commonEnvelope childrenD_174 b hb)
def required_175 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_175 : Finset Cell := ⟨(([(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_175 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) required_141), (placedSet 2 (0, -1) required_7), (placedSet 1 (1, -1) required_63)]
def childrenD_175 : Fin 3 → Finset Cell := ![(placedSet 0 (1, 0) envelope_141), (placedSet 2 (0, -1) envelope_7), (placedSet 1 (1, -1) envelope_63)]
theorem common_sub_175 : commonEnvelope childrenD_175 ⊆ insert (0, 0) required_175 := by decide
theorem child_required_sub_175 : ∀ j, childrenC_175 j ⊆ insert (0, 0) required_175 := by decide
theorem child_envelope_sub_175 : ∀ j, childrenD_175 j ⊆ envelope_175 := by decide
theorem pivot_mem_175 : (0, 0) ∈ envelope_175 := by decide
theorem children_work_175 : ∀ j, Template HasSnaky 5 (childrenC_175 j) (childrenD_175 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_141 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_7 2 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
theorem row_works_175 : Template HasSnaky 6 required_175 envelope_175 := by
  refine compose HasSnaky 5 childrenC_175 childrenD_175 children_work_175 (0, 0)
    required_175 envelope_175 pivot_mem_175 child_required_sub_175 child_envelope_sub_175 ?_
  intro b hb; exact common_sub_175 (mem_commonEnvelope childrenD_175 b hb)
def required_176 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_176 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_176 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 6 (0, 1) required_64), (placedSet 2 (1, 0) required_55)]
def childrenD_176 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 6 (0, 1) envelope_64), (placedSet 2 (1, 0) envelope_55)]
theorem common_sub_176 : commonEnvelope childrenD_176 ⊆ insert (0, 0) required_176 := by decide
theorem child_required_sub_176 : ∀ j, childrenC_176 j ⊆ insert (0, 0) required_176 := by decide
theorem child_envelope_sub_176 : ∀ j, childrenD_176 j ⊆ envelope_176 := by decide
theorem pivot_mem_176 : (0, 0) ∈ envelope_176 := by decide
theorem children_work_176 : ∀ j, Template HasSnaky 5 (childrenC_176 j) (childrenD_176 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_64 6 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_55 2 (1, 0)).mono (by decide)
theorem row_works_176 : Template HasSnaky 6 required_176 envelope_176 := by
  refine compose HasSnaky 5 childrenC_176 childrenD_176 children_work_176 (0, 0)
    required_176 envelope_176 pivot_mem_176 child_required_sub_176 child_envelope_sub_176 ?_
  intro b hb; exact common_sub_176 (mem_commonEnvelope childrenD_176 b hb)
def required_177 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, -2), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_177 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_177 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 3 (1, 0) required_136)]
def childrenD_177 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 3 (1, 0) envelope_136)]
theorem common_sub_177 : commonEnvelope childrenD_177 ⊆ insert (0, 0) required_177 := by decide
theorem child_required_sub_177 : ∀ j, childrenC_177 j ⊆ insert (0, 0) required_177 := by decide
theorem child_envelope_sub_177 : ∀ j, childrenD_177 j ⊆ envelope_177 := by decide
theorem pivot_mem_177 : (0, 0) ∈ envelope_177 := by decide
theorem children_work_177 : ∀ j, Template HasSnaky 5 (childrenC_177 j) (childrenD_177 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_136 3 (1, 0)).mono (by decide)
theorem row_works_177 : Template HasSnaky 6 required_177 envelope_177 := by
  refine compose HasSnaky 5 childrenC_177 childrenD_177 children_work_177 (0, 0)
    required_177 envelope_177 pivot_mem_177 child_required_sub_177 child_envelope_sub_177 ?_
  intro b hb; exact common_sub_177 (mem_commonEnvelope childrenD_177 b hb)
def required_178 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_178 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_178 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) required_37), (placedSet 1 (0, 1) required_68), (placedSet 3 (0, 1) required_46)]
def childrenD_178 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_37), (placedSet 1 (0, 1) envelope_68), (placedSet 3 (0, 1) envelope_46)]
theorem common_sub_178 : commonEnvelope childrenD_178 ⊆ insert (0, 0) required_178 := by decide
theorem child_required_sub_178 : ∀ j, childrenC_178 j ⊆ insert (0, 0) required_178 := by decide
theorem child_envelope_sub_178 : ∀ j, childrenD_178 j ⊆ envelope_178 := by decide
theorem pivot_mem_178 : (0, 0) ∈ envelope_178 := by decide
theorem children_work_178 : ∀ j, Template HasSnaky 5 (childrenC_178 j) (childrenD_178 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_37 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_68 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_46 3 (0, 1)).mono (by decide)
theorem row_works_178 : Template HasSnaky 6 required_178 envelope_178 := by
  refine compose HasSnaky 5 childrenC_178 childrenD_178 children_work_178 (0, 0)
    required_178 envelope_178 pivot_mem_178 child_required_sub_178 child_envelope_sub_178 ?_
  intro b hb; exact common_sub_178 (mem_commonEnvelope childrenD_178 b hb)
end SnakyConditional

end OAI
