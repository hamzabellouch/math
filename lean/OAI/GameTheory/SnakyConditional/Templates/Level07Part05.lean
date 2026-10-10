import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part03
import OAI.GameTheory.SnakyConditional.Templates.Level06Part04
import OAI.GameTheory.SnakyConditional.Templates.Level06Part05

namespace OAI

namespace SnakyConditional
def required_132 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_132 : Finset Cell := ⟨(([(0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_132 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (1, 2) required_89)]
def childrenD_132 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (1, 2) envelope_89)]
theorem common_sub_132 : commonEnvelope childrenD_132 ⊆ insert (0, 0) required_132 := by decide
theorem child_required_sub_132 : ∀ j, childrenC_132 j ⊆ insert (0, 0) required_132 := by decide
theorem child_envelope_sub_132 : ∀ j, childrenD_132 j ⊆ envelope_132 := by decide
theorem pivot_mem_132 : (0, 0) ∈ envelope_132 := by decide
theorem children_work_132 : ∀ j, Template HasSnaky 4 (childrenC_132 j) (childrenD_132 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_89 0 (1, 2)).mono (by decide)
theorem row_works_132 : Template HasSnaky 5 required_132 envelope_132 := by
  refine compose HasSnaky 4 childrenC_132 childrenD_132 children_work_132 (0, 0)
    required_132 envelope_132 pivot_mem_132 child_required_sub_132 child_envelope_sub_132 ?_
  intro b hb; exact common_sub_132 (mem_commonEnvelope childrenD_132 b hb)
def required_133 : Finset Cell := ⟨(([(-2, 0), (-1, -2), (0, -2), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_133 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_133 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) required_6), (placedSet 0 (1, 1) required_92)]
def childrenD_133 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) envelope_6), (placedSet 0 (1, 1) envelope_92)]
theorem common_sub_133 : commonEnvelope childrenD_133 ⊆ insert (0, 0) required_133 := by decide
theorem child_required_sub_133 : ∀ j, childrenC_133 j ⊆ insert (0, 0) required_133 := by decide
theorem child_envelope_sub_133 : ∀ j, childrenD_133 j ⊆ envelope_133 := by decide
theorem pivot_mem_133 : (0, 0) ∈ envelope_133 := by decide
theorem children_work_133 : ∀ j, Template HasSnaky 4 (childrenC_133 j) (childrenD_133 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 7 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_92 0 (1, 1)).mono (by decide)
theorem row_works_133 : Template HasSnaky 5 required_133 envelope_133 := by
  refine compose HasSnaky 4 childrenC_133 childrenD_133 children_work_133 (0, 0)
    required_133 envelope_133 pivot_mem_133 child_required_sub_133 child_envelope_sub_133 ?_
  intro b hb; exact common_sub_133 (mem_commonEnvelope childrenD_133 b hb)
def required_134 : Finset Cell := ⟨(([(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_134 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_134 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -4) required_6), (placedSet 0 (1, 0) required_82)]
def childrenD_134 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -4) envelope_6), (placedSet 0 (1, 0) envelope_82)]
theorem common_sub_134 : commonEnvelope childrenD_134 ⊆ insert (0, 0) required_134 := by decide
theorem child_required_sub_134 : ∀ j, childrenC_134 j ⊆ insert (0, 0) required_134 := by decide
theorem child_envelope_sub_134 : ∀ j, childrenD_134 j ⊆ envelope_134 := by decide
theorem pivot_mem_134 : (0, 0) ∈ envelope_134 := by decide
theorem children_work_134 : ∀ j, Template HasSnaky 4 (childrenC_134 j) (childrenD_134 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 7 (-1, -4)).mono (by decide)
  · exact (placed_template_map row_works_82 0 (1, 0)).mono (by decide)
theorem row_works_134 : Template HasSnaky 5 required_134 envelope_134 := by
  refine compose HasSnaky 4 childrenC_134 childrenD_134 children_work_134 (0, 0)
    required_134 envelope_134 pivot_mem_134 child_required_sub_134 child_envelope_sub_134 ?_
  intro b hb; exact common_sub_134 (mem_commonEnvelope childrenD_134 b hb)
def required_135 : Finset Cell := ⟨(([(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_135 : Finset Cell := ⟨(([(-6, 0), (-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_135 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 1) required_7), (placedSet 4 (-2, 1) required_75), (placedSet 0 (1, 0) required_44)]
def childrenD_135 : Fin 3 → Finset Cell := ![(placedSet 0 (0, 1) envelope_7), (placedSet 4 (-2, 1) envelope_75), (placedSet 0 (1, 0) envelope_44)]
theorem common_sub_135 : commonEnvelope childrenD_135 ⊆ insert (0, 0) required_135 := by decide
theorem child_required_sub_135 : ∀ j, childrenC_135 j ⊆ insert (0, 0) required_135 := by decide
theorem child_envelope_sub_135 : ∀ j, childrenD_135 j ⊆ envelope_135 := by decide
theorem pivot_mem_135 : (0, 0) ∈ envelope_135 := by decide
theorem children_work_135 : ∀ j, Template HasSnaky 4 (childrenC_135 j) (childrenD_135 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_75 4 (-2, 1)).mono (by decide)
  · exact (placed_template_map row_works_44 0 (1, 0)).mono (by decide)
theorem row_works_135 : Template HasSnaky 5 required_135 envelope_135 := by
  refine compose HasSnaky 4 childrenC_135 childrenD_135 children_work_135 (0, 0)
    required_135 envelope_135 pivot_mem_135 child_required_sub_135 child_envelope_sub_135 ?_
  intro b hb; exact common_sub_135 (mem_commonEnvelope childrenD_135 b hb)
def required_136 : Finset Cell := ⟨(([(-2, -1), (-1, 2), (0, -1), (0, 1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_136 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_136 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 3) required_6), (placedSet 2 (-1, -1) required_102)]
def childrenD_136 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 3) envelope_6), (placedSet 2 (-1, -1) envelope_102)]
theorem common_sub_136 : commonEnvelope childrenD_136 ⊆ insert (0, 0) required_136 := by decide
theorem child_required_sub_136 : ∀ j, childrenC_136 j ⊆ insert (0, 0) required_136 := by decide
theorem child_envelope_sub_136 : ∀ j, childrenD_136 j ⊆ envelope_136 := by decide
theorem pivot_mem_136 : (0, 0) ∈ envelope_136 := by decide
theorem children_work_136 : ∀ j, Template HasSnaky 4 (childrenC_136 j) (childrenD_136 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_102 2 (-1, -1)).mono (by decide)
theorem row_works_136 : Template HasSnaky 5 required_136 envelope_136 := by
  refine compose HasSnaky 4 childrenC_136 childrenD_136 children_work_136 (0, 0)
    required_136 envelope_136 pivot_mem_136 child_required_sub_136 child_envelope_sub_136 ?_
  intro b hb; exact common_sub_136 (mem_commonEnvelope childrenD_136 b hb)
def required_140 : Finset Cell := ⟨(([(-1, -1), (-1, 1), (0, -1), (0, 1), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_140 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_140 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -2) required_6), (placedSet 0 (1, 2) required_82)]
def childrenD_140 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -2) envelope_6), (placedSet 0 (1, 2) envelope_82)]
theorem common_sub_140 : commonEnvelope childrenD_140 ⊆ insert (0, 0) required_140 := by decide
theorem child_required_sub_140 : ∀ j, childrenC_140 j ⊆ insert (0, 0) required_140 := by decide
theorem child_envelope_sub_140 : ∀ j, childrenD_140 j ⊆ envelope_140 := by decide
theorem pivot_mem_140 : (0, 0) ∈ envelope_140 := by decide
theorem children_work_140 : ∀ j, Template HasSnaky 4 (childrenC_140 j) (childrenD_140 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 7 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_82 0 (1, 2)).mono (by decide)
theorem row_works_140 : Template HasSnaky 5 required_140 envelope_140 := by
  refine compose HasSnaky 4 childrenC_140 childrenD_140 children_work_140 (0, 0)
    required_140 envelope_140 pivot_mem_140 child_required_sub_140 child_envelope_sub_140 ?_
  intro b hb; exact common_sub_140 (mem_commonEnvelope childrenD_140 b hb)
def required_142 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_142 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_142 : Fin 3 → Finset Cell := ![(placedSet 4 (-2, -1) required_72), (placedSet 1 (0, -1) required_32), (placedSet 2 (1, 0) required_55)]
def childrenD_142 : Fin 3 → Finset Cell := ![(placedSet 4 (-2, -1) envelope_72), (placedSet 1 (0, -1) envelope_32), (placedSet 2 (1, 0) envelope_55)]
theorem common_sub_142 : commonEnvelope childrenD_142 ⊆ insert (0, 0) required_142 := by decide
theorem child_required_sub_142 : ∀ j, childrenC_142 j ⊆ insert (0, 0) required_142 := by decide
theorem child_envelope_sub_142 : ∀ j, childrenD_142 j ⊆ envelope_142 := by decide
theorem pivot_mem_142 : (0, 0) ∈ envelope_142 := by decide
theorem children_work_142 : ∀ j, Template HasSnaky 4 (childrenC_142 j) (childrenD_142 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_72 4 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_32 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 2 (1, 0)).mono (by decide)
theorem row_works_142 : Template HasSnaky 5 required_142 envelope_142 := by
  refine compose HasSnaky 4 childrenC_142 childrenD_142 children_work_142 (0, 0)
    required_142 envelope_142 pivot_mem_142 child_required_sub_142 child_envelope_sub_142 ?_
  intro b hb; exact common_sub_142 (mem_commonEnvelope childrenD_142 b hb)
end SnakyConditional

end OAI
