import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part02
import OAI.GameTheory.SnakyConditional.Templates.Level06Part04
import OAI.GameTheory.SnakyConditional.Templates.Level06Part07

namespace OAI

namespace SnakyConditional
def required_167 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_167 : Finset Cell := ⟨(([(-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_167 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_57), (placedSet 4 (-4, 0) required_57)]
def childrenD_167 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_57), (placedSet 4 (-4, 0) envelope_57)]
theorem common_sub_167 : commonEnvelope childrenD_167 ⊆ insert (0, 0) required_167 := by decide
theorem child_required_sub_167 : ∀ j, childrenC_167 j ⊆ insert (0, 0) required_167 := by decide
theorem child_envelope_sub_167 : ∀ j, childrenD_167 j ⊆ envelope_167 := by decide
theorem pivot_mem_167 : (0, 0) ∈ envelope_167 := by decide
theorem children_work_167 : ∀ j, Template HasSnaky 4 (childrenC_167 j) (childrenD_167 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_57 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_57 4 (-4, 0)).mono (by decide)
theorem row_works_167 : Template HasSnaky 5 required_167 envelope_167 := by
  refine compose HasSnaky 4 childrenC_167 childrenD_167 children_work_167 (0, 0)
    required_167 envelope_167 pivot_mem_167 child_required_sub_167 child_envelope_sub_167 ?_
  intro b hb; exact common_sub_167 (mem_commonEnvelope childrenD_167 b hb)
def required_181 : Finset Cell := ⟨(([(1, -2), (1, -1), (1, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_181 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_181 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_24), (placedSet 2 (2, 0) required_87), (placedSet 0 (3, 1) required_90)]
def childrenD_181 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_24), (placedSet 2 (2, 0) envelope_87), (placedSet 0 (3, 1) envelope_90)]
theorem common_sub_181 : commonEnvelope childrenD_181 ⊆ insert (0, 0) required_181 := by decide
theorem child_required_sub_181 : ∀ j, childrenC_181 j ⊆ insert (0, 0) required_181 := by decide
theorem child_envelope_sub_181 : ∀ j, childrenD_181 j ⊆ envelope_181 := by decide
theorem pivot_mem_181 : (0, 0) ∈ envelope_181 := by decide
theorem children_work_181 : ∀ j, Template HasSnaky 4 (childrenC_181 j) (childrenD_181 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_87 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_90 0 (3, 1)).mono (by decide)
theorem row_works_181 : Template HasSnaky 5 required_181 envelope_181 := by
  refine compose HasSnaky 4 childrenC_181 childrenD_181 children_work_181 (0, 0)
    required_181 envelope_181 pivot_mem_181 child_required_sub_181 child_envelope_sub_181 ?_
  intro b hb; exact common_sub_181 (mem_commonEnvelope childrenD_181 b hb)
def required_182 : Finset Cell := ⟨(([(1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_182 : Finset Cell := ⟨(([(-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_182 : Fin 2 → Finset Cell := ![(placedSet 2 (3, -1) required_12), (placedSet 0 (3, 0) required_139)]
def childrenD_182 : Fin 2 → Finset Cell := ![(placedSet 2 (3, -1) envelope_12), (placedSet 0 (3, 0) envelope_139)]
theorem common_sub_182 : commonEnvelope childrenD_182 ⊆ insert (0, 0) required_182 := by decide
theorem child_required_sub_182 : ∀ j, childrenC_182 j ⊆ insert (0, 0) required_182 := by decide
theorem child_envelope_sub_182 : ∀ j, childrenD_182 j ⊆ envelope_182 := by decide
theorem pivot_mem_182 : (0, 0) ∈ envelope_182 := by decide
theorem children_work_182 : ∀ j, Template HasSnaky 4 (childrenC_182 j) (childrenD_182 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_12 2 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_139 0 (3, 0)).mono (by decide)
theorem row_works_182 : Template HasSnaky 5 required_182 envelope_182 := by
  refine compose HasSnaky 4 childrenC_182 childrenD_182 children_work_182 (0, 0)
    required_182 envelope_182 pivot_mem_182 child_required_sub_182 child_envelope_sub_182 ?_
  intro b hb; exact common_sub_182 (mem_commonEnvelope childrenD_182 b hb)
def required_186 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_186 : Finset Cell := ⟨(([(-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_186 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_7), (placedSet 2 (1, 0) required_141)]
def childrenD_186 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_7), (placedSet 2 (1, 0) envelope_141)]
theorem common_sub_186 : commonEnvelope childrenD_186 ⊆ insert (0, 0) required_186 := by decide
theorem child_required_sub_186 : ∀ j, childrenC_186 j ⊆ insert (0, 0) required_186 := by decide
theorem child_envelope_sub_186 : ∀ j, childrenD_186 j ⊆ envelope_186 := by decide
theorem pivot_mem_186 : (0, 0) ∈ envelope_186 := by decide
theorem children_work_186 : ∀ j, Template HasSnaky 4 (childrenC_186 j) (childrenD_186 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_141 2 (1, 0)).mono (by decide)
theorem row_works_186 : Template HasSnaky 5 required_186 envelope_186 := by
  refine compose HasSnaky 4 childrenC_186 childrenD_186 children_work_186 (0, 0)
    required_186 envelope_186 pivot_mem_186 child_required_sub_186 child_envelope_sub_186 ?_
  intro b hb; exact common_sub_186 (mem_commonEnvelope childrenD_186 b hb)
def required_194 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_194 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 1), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_194 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) required_0), (placedSet 4 (-2, 1) required_146)]
def childrenD_194 : Fin 2 → Finset Cell := ![(placedSet 0 (-4, -1) envelope_0), (placedSet 4 (-2, 1) envelope_146)]
theorem common_sub_194 : commonEnvelope childrenD_194 ⊆ insert (0, 0) required_194 := by decide
theorem child_required_sub_194 : ∀ j, childrenC_194 j ⊆ insert (0, 0) required_194 := by decide
theorem child_envelope_sub_194 : ∀ j, childrenD_194 j ⊆ envelope_194 := by decide
theorem pivot_mem_194 : (0, 0) ∈ envelope_194 := by decide
theorem children_work_194 : ∀ j, Template HasSnaky 4 (childrenC_194 j) (childrenD_194 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_146 4 (-2, 1)).mono (by decide)
theorem row_works_194 : Template HasSnaky 5 required_194 envelope_194 := by
  refine compose HasSnaky 4 childrenC_194 childrenD_194 children_work_194 (0, 0)
    required_194 envelope_194 pivot_mem_194 child_required_sub_194 child_envelope_sub_194 ?_
  intro b hb; exact common_sub_194 (mem_commonEnvelope childrenD_194 b hb)
def required_201 : Finset Cell := ⟨(([(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_201 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_201 : Fin 2 → Finset Cell := ![(placedSet 3 (1, 3) required_45), (placedSet 0 (2, 1) required_82)]
def childrenD_201 : Fin 2 → Finset Cell := ![(placedSet 3 (1, 3) envelope_45), (placedSet 0 (2, 1) envelope_82)]
theorem common_sub_201 : commonEnvelope childrenD_201 ⊆ insert (0, 0) required_201 := by decide
theorem child_required_sub_201 : ∀ j, childrenC_201 j ⊆ insert (0, 0) required_201 := by decide
theorem child_envelope_sub_201 : ∀ j, childrenD_201 j ⊆ envelope_201 := by decide
theorem pivot_mem_201 : (0, 0) ∈ envelope_201 := by decide
theorem children_work_201 : ∀ j, Template HasSnaky 4 (childrenC_201 j) (childrenD_201 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_45 3 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_82 0 (2, 1)).mono (by decide)
theorem row_works_201 : Template HasSnaky 5 required_201 envelope_201 := by
  refine compose HasSnaky 4 childrenC_201 childrenD_201 children_work_201 (0, 0)
    required_201 envelope_201 pivot_mem_201 child_required_sub_201 child_envelope_sub_201 ?_
  intro b hb; exact common_sub_201 (mem_commonEnvelope childrenD_201 b hb)
def required_209 : Finset Cell := ⟨(([(-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 2), (0, -1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_209 : Finset Cell := ⟨(([(-3, -1), (-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 0), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 3), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_209 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_25), (placedSet 5 (1, 3) required_81)]
def childrenD_209 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_25), (placedSet 5 (1, 3) envelope_81)]
theorem common_sub_209 : commonEnvelope childrenD_209 ⊆ insert (0, 0) required_209 := by decide
theorem child_required_sub_209 : ∀ j, childrenC_209 j ⊆ insert (0, 0) required_209 := by decide
theorem child_envelope_sub_209 : ∀ j, childrenD_209 j ⊆ envelope_209 := by decide
theorem pivot_mem_209 : (0, 0) ∈ envelope_209 := by decide
theorem children_work_209 : ∀ j, Template HasSnaky 4 (childrenC_209 j) (childrenD_209 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_81 5 (1, 3)).mono (by decide)
theorem row_works_209 : Template HasSnaky 5 required_209 envelope_209 := by
  refine compose HasSnaky 4 childrenC_209 childrenD_209 children_work_209 (0, 0)
    required_209 envelope_209 pivot_mem_209 child_required_sub_209 child_envelope_sub_209 ?_
  intro b hb; exact common_sub_209 (mem_commonEnvelope childrenD_209 b hb)
end SnakyConditional

end OAI
