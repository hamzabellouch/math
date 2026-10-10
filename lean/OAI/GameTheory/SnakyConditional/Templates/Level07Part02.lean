import OAI.GameTheory.SnakyConditional.Templates.Level06Part01
import OAI.GameTheory.SnakyConditional.Templates.Level06Part02
import OAI.GameTheory.SnakyConditional.Templates.Level06Part03

namespace OAI

namespace SnakyConditional
def required_84 : Finset Cell := ⟨(([(0, -1), (1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_84 : Finset Cell := ⟨(([(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, 0), (4, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_84 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, 0) required_67)]
def childrenD_84 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, 0) envelope_67)]
theorem common_sub_84 : commonEnvelope childrenD_84 ⊆ insert (0, 0) required_84 := by decide
theorem child_required_sub_84 : ∀ j, childrenC_84 j ⊆ insert (0, 0) required_84 := by decide
theorem child_envelope_sub_84 : ∀ j, childrenD_84 j ⊆ envelope_84 := by decide
theorem pivot_mem_84 : (0, 0) ∈ envelope_84 := by decide
theorem children_work_84 : ∀ j, Template HasSnaky 4 (childrenC_84 j) (childrenD_84 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_67 0 (2, 0)).mono (by decide)
theorem row_works_84 : Template HasSnaky 5 required_84 envelope_84 := by
  refine compose HasSnaky 4 childrenC_84 childrenD_84 children_work_84 (0, 0)
    required_84 envelope_84 pivot_mem_84 child_required_sub_84 child_envelope_sub_84 ?_
  intro b hb; exact common_sub_84 (mem_commonEnvelope childrenD_84 b hb)
def required_86 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_86 : Finset Cell := ⟨(([(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_86 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 3 (-3, 1) required_67)]
def childrenD_86 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 3 (-3, 1) envelope_67)]
theorem common_sub_86 : commonEnvelope childrenD_86 ⊆ insert (0, 0) required_86 := by decide
theorem child_required_sub_86 : ∀ j, childrenC_86 j ⊆ insert (0, 0) required_86 := by decide
theorem child_envelope_sub_86 : ∀ j, childrenD_86 j ⊆ envelope_86 := by decide
theorem pivot_mem_86 : (0, 0) ∈ envelope_86 := by decide
theorem children_work_86 : ∀ j, Template HasSnaky 4 (childrenC_86 j) (childrenD_86 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_67 3 (-3, 1)).mono (by decide)
theorem row_works_86 : Template HasSnaky 5 required_86 envelope_86 := by
  refine compose HasSnaky 4 childrenC_86 childrenD_86 children_work_86 (0, 0)
    required_86 envelope_86 pivot_mem_86 child_required_sub_86 child_envelope_sub_86 ?_
  intro b hb; exact common_sub_86 (mem_commonEnvelope childrenD_86 b hb)
def required_88 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_88 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_88 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) required_0), (placedSet 3 (-2, 1) required_67)]
def childrenD_88 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) envelope_0), (placedSet 3 (-2, 1) envelope_67)]
theorem common_sub_88 : commonEnvelope childrenD_88 ⊆ insert (0, 0) required_88 := by decide
theorem child_required_sub_88 : ∀ j, childrenC_88 j ⊆ insert (0, 0) required_88 := by decide
theorem child_envelope_sub_88 : ∀ j, childrenD_88 j ⊆ envelope_88 := by decide
theorem pivot_mem_88 : (0, 0) ∈ envelope_88 := by decide
theorem children_work_88 : ∀ j, Template HasSnaky 4 (childrenC_88 j) (childrenD_88 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_67 3 (-2, 1)).mono (by decide)
theorem row_works_88 : Template HasSnaky 5 required_88 envelope_88 := by
  refine compose HasSnaky 4 childrenC_88 childrenD_88 children_work_88 (0, 0)
    required_88 envelope_88 pivot_mem_88 child_required_sub_88 child_envelope_sub_88 ?_
  intro b hb; exact common_sub_88 (mem_commonEnvelope childrenD_88 b hb)
def required_91 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_91 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_91 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 5 (3, -1) required_74)]
def childrenD_91 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 5 (3, -1) envelope_74)]
theorem common_sub_91 : commonEnvelope childrenD_91 ⊆ insert (0, 0) required_91 := by decide
theorem child_required_sub_91 : ∀ j, childrenC_91 j ⊆ insert (0, 0) required_91 := by decide
theorem child_envelope_sub_91 : ∀ j, childrenD_91 j ⊆ envelope_91 := by decide
theorem pivot_mem_91 : (0, 0) ∈ envelope_91 := by decide
theorem children_work_91 : ∀ j, Template HasSnaky 4 (childrenC_91 j) (childrenD_91 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_74 5 (3, -1)).mono (by decide)
theorem row_works_91 : Template HasSnaky 5 required_91 envelope_91 := by
  refine compose HasSnaky 4 childrenC_91 childrenD_91 children_work_91 (0, 0)
    required_91 envelope_91 pivot_mem_91 child_required_sub_91 child_envelope_sub_91 ?_
  intro b hb; exact common_sub_91 (mem_commonEnvelope childrenD_91 b hb)
def required_96 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_96 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_96 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) required_6), (placedSet 0 (-1, 1) required_70)]
def childrenD_96 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) envelope_6), (placedSet 0 (-1, 1) envelope_70)]
theorem common_sub_96 : commonEnvelope childrenD_96 ⊆ insert (0, 0) required_96 := by decide
theorem child_required_sub_96 : ∀ j, childrenC_96 j ⊆ insert (0, 0) required_96 := by decide
theorem child_envelope_sub_96 : ∀ j, childrenD_96 j ⊆ envelope_96 := by decide
theorem pivot_mem_96 : (0, 0) ∈ envelope_96 := by decide
theorem children_work_96 : ∀ j, Template HasSnaky 4 (childrenC_96 j) (childrenD_96 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_70 0 (-1, 1)).mono (by decide)
theorem row_works_96 : Template HasSnaky 5 required_96 envelope_96 := by
  refine compose HasSnaky 4 childrenC_96 childrenD_96 children_work_96 (0, 0)
    required_96 envelope_96 pivot_mem_96 child_required_sub_96 child_envelope_sub_96 ?_
  intro b hb; exact common_sub_96 (mem_commonEnvelope childrenD_96 b hb)
def required_97 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_97 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_97 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) required_6), (placedSet 0 (1, 0) required_44)]
def childrenD_97 : Fin 2 → Finset Cell := ![(placedSet 6 (-4, -1) envelope_6), (placedSet 0 (1, 0) envelope_44)]
theorem common_sub_97 : commonEnvelope childrenD_97 ⊆ insert (0, 0) required_97 := by decide
theorem child_required_sub_97 : ∀ j, childrenC_97 j ⊆ insert (0, 0) required_97 := by decide
theorem child_envelope_sub_97 : ∀ j, childrenD_97 j ⊆ envelope_97 := by decide
theorem pivot_mem_97 : (0, 0) ∈ envelope_97 := by decide
theorem children_work_97 : ∀ j, Template HasSnaky 4 (childrenC_97 j) (childrenD_97 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_44 0 (1, 0)).mono (by decide)
theorem row_works_97 : Template HasSnaky 5 required_97 envelope_97 := by
  refine compose HasSnaky 4 childrenC_97 childrenD_97 children_work_97 (0, 0)
    required_97 envelope_97 pivot_mem_97 child_required_sub_97 child_envelope_sub_97 ?_
  intro b hb; exact common_sub_97 (mem_commonEnvelope childrenD_97 b hb)
def required_98 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_98 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_98 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) required_6), (placedSet 0 (3, 0) required_44)]
def childrenD_98 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_6), (placedSet 0 (3, 0) envelope_44)]
theorem common_sub_98 : commonEnvelope childrenD_98 ⊆ insert (0, 0) required_98 := by decide
theorem child_required_sub_98 : ∀ j, childrenC_98 j ⊆ insert (0, 0) required_98 := by decide
theorem child_envelope_sub_98 : ∀ j, childrenD_98 j ⊆ envelope_98 := by decide
theorem pivot_mem_98 : (0, 0) ∈ envelope_98 := by decide
theorem children_work_98 : ∀ j, Template HasSnaky 4 (childrenC_98 j) (childrenD_98 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_44 0 (3, 0)).mono (by decide)
theorem row_works_98 : Template HasSnaky 5 required_98 envelope_98 := by
  refine compose HasSnaky 4 childrenC_98 childrenD_98 children_work_98 (0, 0)
    required_98 envelope_98 pivot_mem_98 child_required_sub_98 child_envelope_sub_98 ?_
  intro b hb; exact common_sub_98 (mem_commonEnvelope childrenD_98 b hb)
end SnakyConditional

end OAI
