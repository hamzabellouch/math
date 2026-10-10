import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part02
import OAI.GameTheory.SnakyConditional.Templates.Level06Part05

namespace OAI

namespace SnakyConditional
def required_147 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_147 : Finset Cell := ⟨(([(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_147 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 1) required_53), (placedSet 2 (1, 0) required_44)]
def childrenD_147 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, 1) envelope_53), (placedSet 2 (1, 0) envelope_44)]
theorem common_sub_147 : commonEnvelope childrenD_147 ⊆ insert (0, 0) required_147 := by decide
theorem child_required_sub_147 : ∀ j, childrenC_147 j ⊆ insert (0, 0) required_147 := by decide
theorem child_envelope_sub_147 : ∀ j, childrenD_147 j ⊆ envelope_147 := by decide
theorem pivot_mem_147 : (0, 0) ∈ envelope_147 := by decide
theorem children_work_147 : ∀ j, Template HasSnaky 4 (childrenC_147 j) (childrenD_147 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_53 0 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_44 2 (1, 0)).mono (by decide)
theorem row_works_147 : Template HasSnaky 5 required_147 envelope_147 := by
  refine compose HasSnaky 4 childrenC_147 childrenD_147 children_work_147 (0, 0)
    required_147 envelope_147 pivot_mem_147 child_required_sub_147 child_envelope_sub_147 ?_
  intro b hb; exact common_sub_147 (mem_commonEnvelope childrenD_147 b hb)
def required_151 : Finset Cell := ⟨(([(0, -3), (0, -2), (1, 0), (1, 1), (2, -2), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_151 : Finset Cell := ⟨(([(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_151 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_2), (placedSet 2 (2, -1) required_101)]
def childrenD_151 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_2), (placedSet 2 (2, -1) envelope_101)]
theorem common_sub_151 : commonEnvelope childrenD_151 ⊆ insert (0, 0) required_151 := by decide
theorem child_required_sub_151 : ∀ j, childrenC_151 j ⊆ insert (0, 0) required_151 := by decide
theorem child_envelope_sub_151 : ∀ j, childrenD_151 j ⊆ envelope_151 := by decide
theorem pivot_mem_151 : (0, 0) ∈ envelope_151 := by decide
theorem children_work_151 : ∀ j, Template HasSnaky 4 (childrenC_151 j) (childrenD_151 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_101 2 (2, -1)).mono (by decide)
theorem row_works_151 : Template HasSnaky 5 required_151 envelope_151 := by
  refine compose HasSnaky 4 childrenC_151 childrenD_151 children_work_151 (0, 0)
    required_151 envelope_151 pivot_mem_151 child_required_sub_151 child_envelope_sub_151 ?_
  intro b hb; exact common_sub_151 (mem_commonEnvelope childrenD_151 b hb)
def required_153 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_153 : Finset Cell := ⟨(([(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_153 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 0) required_59), (placedSet 0 (1, 0) required_27)]
def childrenD_153 : Fin 2 → Finset Cell := ![(placedSet 4 (-4, 0) envelope_59), (placedSet 0 (1, 0) envelope_27)]
theorem common_sub_153 : commonEnvelope childrenD_153 ⊆ insert (0, 0) required_153 := by decide
theorem child_required_sub_153 : ∀ j, childrenC_153 j ⊆ insert (0, 0) required_153 := by decide
theorem child_envelope_sub_153 : ∀ j, childrenD_153 j ⊆ envelope_153 := by decide
theorem pivot_mem_153 : (0, 0) ∈ envelope_153 := by decide
theorem children_work_153 : ∀ j, Template HasSnaky 4 (childrenC_153 j) (childrenD_153 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_59 4 (-4, 0)).mono (by decide)
  · exact (placed_template_map row_works_27 0 (1, 0)).mono (by decide)
theorem row_works_153 : Template HasSnaky 5 required_153 envelope_153 := by
  refine compose HasSnaky 4 childrenC_153 childrenD_153 children_work_153 (0, 0)
    required_153 envelope_153 pivot_mem_153 child_required_sub_153 child_envelope_sub_153 ?_
  intro b hb; exact common_sub_153 (mem_commonEnvelope childrenD_153 b hb)
def required_155 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_155 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_155 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) required_7), (placedSet 3 (0, 1) required_55)]
def childrenD_155 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) envelope_7), (placedSet 3 (0, 1) envelope_55)]
theorem common_sub_155 : commonEnvelope childrenD_155 ⊆ insert (0, 0) required_155 := by decide
theorem child_required_sub_155 : ∀ j, childrenC_155 j ⊆ insert (0, 0) required_155 := by decide
theorem child_envelope_sub_155 : ∀ j, childrenD_155 j ⊆ envelope_155 := by decide
theorem pivot_mem_155 : (0, 0) ∈ envelope_155 := by decide
theorem children_work_155 : ∀ j, Template HasSnaky 4 (childrenC_155 j) (childrenD_155 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_55 3 (0, 1)).mono (by decide)
theorem row_works_155 : Template HasSnaky 5 required_155 envelope_155 := by
  refine compose HasSnaky 4 childrenC_155 childrenD_155 children_work_155 (0, 0)
    required_155 envelope_155 pivot_mem_155 child_required_sub_155 child_envelope_sub_155 ?_
  intro b hb; exact common_sub_155 (mem_commonEnvelope childrenD_155 b hb)
def required_157 : Finset Cell := ⟨(([(0, -1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_157 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_157 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 1 (1, 2) required_57)]
def childrenD_157 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 1 (1, 2) envelope_57)]
theorem common_sub_157 : commonEnvelope childrenD_157 ⊆ insert (0, 0) required_157 := by decide
theorem child_required_sub_157 : ∀ j, childrenC_157 j ⊆ insert (0, 0) required_157 := by decide
theorem child_envelope_sub_157 : ∀ j, childrenD_157 j ⊆ envelope_157 := by decide
theorem pivot_mem_157 : (0, 0) ∈ envelope_157 := by decide
theorem children_work_157 : ∀ j, Template HasSnaky 4 (childrenC_157 j) (childrenD_157 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_57 1 (1, 2)).mono (by decide)
theorem row_works_157 : Template HasSnaky 5 required_157 envelope_157 := by
  refine compose HasSnaky 4 childrenC_157 childrenD_157 children_work_157 (0, 0)
    required_157 envelope_157 pivot_mem_157 child_required_sub_157 child_envelope_sub_157 ?_
  intro b hb; exact common_sub_157 (mem_commonEnvelope childrenD_157 b hb)
def required_158 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_158 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_158 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) required_66), (placedSet 1 (0, 1) required_45), (placedSet 3 (0, 1) required_46)]
def childrenD_158 : Fin 3 → Finset Cell := ![(placedSet 0 (-1, 0) envelope_66), (placedSet 1 (0, 1) envelope_45), (placedSet 3 (0, 1) envelope_46)]
theorem common_sub_158 : commonEnvelope childrenD_158 ⊆ insert (0, 0) required_158 := by decide
theorem child_required_sub_158 : ∀ j, childrenC_158 j ⊆ insert (0, 0) required_158 := by decide
theorem child_envelope_sub_158 : ∀ j, childrenD_158 j ⊆ envelope_158 := by decide
theorem pivot_mem_158 : (0, 0) ∈ envelope_158 := by decide
theorem children_work_158 : ∀ j, Template HasSnaky 4 (childrenC_158 j) (childrenD_158 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_66 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_45 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_46 3 (0, 1)).mono (by decide)
theorem row_works_158 : Template HasSnaky 5 required_158 envelope_158 := by
  refine compose HasSnaky 4 childrenC_158 childrenD_158 children_work_158 (0, 0)
    required_158 envelope_158 pivot_mem_158 child_required_sub_158 child_envelope_sub_158 ?_
  intro b hb; exact common_sub_158 (mem_commonEnvelope childrenD_158 b hb)
def required_163 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_163 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_163 : Fin 3 → Finset Cell := ![(placedSet 2 (1, 0) required_44), (placedSet 1 (1, 0) required_49), (placedSet 4 (-4, 0) required_56)]
def childrenD_163 : Fin 3 → Finset Cell := ![(placedSet 2 (1, 0) envelope_44), (placedSet 1 (1, 0) envelope_49), (placedSet 4 (-4, 0) envelope_56)]
theorem common_sub_163 : commonEnvelope childrenD_163 ⊆ insert (0, 0) required_163 := by decide
theorem child_required_sub_163 : ∀ j, childrenC_163 j ⊆ insert (0, 0) required_163 := by decide
theorem child_envelope_sub_163 : ∀ j, childrenD_163 j ⊆ envelope_163 := by decide
theorem pivot_mem_163 : (0, 0) ∈ envelope_163 := by decide
theorem children_work_163 : ∀ j, Template HasSnaky 4 (childrenC_163 j) (childrenD_163 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_44 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_49 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_56 4 (-4, 0)).mono (by decide)
theorem row_works_163 : Template HasSnaky 5 required_163 envelope_163 := by
  refine compose HasSnaky 4 childrenC_163 childrenD_163 children_work_163 (0, 0)
    required_163 envelope_163 pivot_mem_163 child_required_sub_163 child_envelope_sub_163 ?_
  intro b hb; exact common_sub_163 (mem_commonEnvelope childrenD_163 b hb)
end SnakyConditional

end OAI
