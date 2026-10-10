import OAI.GameTheory.SnakyConditional.Templates.Level05Part01
import OAI.GameTheory.SnakyConditional.Templates.Level05Part04
import OAI.GameTheory.SnakyConditional.Templates.Level05Part06
import OAI.GameTheory.SnakyConditional.Templates.Level05Part07

namespace OAI

namespace SnakyConditional
def required_69 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_69 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 1), (2, 2), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_69 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, 1) required_34)]
def childrenD_69 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, 1) envelope_34)]
theorem common_sub_69 : commonEnvelope childrenD_69 ⊆ insert (0, 0) required_69 := by decide
theorem child_required_sub_69 : ∀ j, childrenC_69 j ⊆ insert (0, 0) required_69 := by decide
theorem child_envelope_sub_69 : ∀ j, childrenD_69 j ⊆ envelope_69 := by decide
theorem pivot_mem_69 : (0, 0) ∈ envelope_69 := by decide
theorem children_work_69 : ∀ j, Template HasSnaky 3 (childrenC_69 j) (childrenD_69 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_34 0 (2, 1)).mono (by decide)
theorem row_works_69 : Template HasSnaky 4 required_69 envelope_69 := by
  refine compose HasSnaky 3 childrenC_69 childrenD_69 children_work_69 (0, 0)
    required_69 envelope_69 pivot_mem_69 child_required_sub_69 child_envelope_sub_69 ?_
  intro b hb; exact common_sub_69 (mem_commonEnvelope childrenD_69 b hb)
def required_70 : Finset Cell := ⟨(([(1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_70 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_70 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) required_4), (placedSet 0 (1, 0) required_41)]
def childrenD_70 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) envelope_4), (placedSet 0 (1, 0) envelope_41)]
theorem common_sub_70 : commonEnvelope childrenD_70 ⊆ insert (0, 0) required_70 := by decide
theorem child_required_sub_70 : ∀ j, childrenC_70 j ⊆ insert (0, 0) required_70 := by decide
theorem child_envelope_sub_70 : ∀ j, childrenD_70 j ⊆ envelope_70 := by decide
theorem pivot_mem_70 : (0, 0) ∈ envelope_70 := by decide
theorem children_work_70 : ∀ j, Template HasSnaky 3 (childrenC_70 j) (childrenD_70 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_41 0 (1, 0)).mono (by decide)
theorem row_works_70 : Template HasSnaky 4 required_70 envelope_70 := by
  refine compose HasSnaky 3 childrenC_70 childrenD_70 children_work_70 (0, 0)
    required_70 envelope_70 pivot_mem_70 child_required_sub_70 child_envelope_sub_70 ?_
  intro b hb; exact common_sub_70 (mem_commonEnvelope childrenD_70 b hb)
def required_72 : Finset Cell := ⟨(([(-2, 1), (-1, 1), (-1, 2), (-1, 3), (0, 1), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_72 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_72 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 4) required_0), (placedSet 6 (1, 0) required_8)]
def childrenD_72 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 4) envelope_0), (placedSet 6 (1, 0) envelope_8)]
theorem common_sub_72 : commonEnvelope childrenD_72 ⊆ insert (0, 0) required_72 := by decide
theorem child_required_sub_72 : ∀ j, childrenC_72 j ⊆ insert (0, 0) required_72 := by decide
theorem child_envelope_sub_72 : ∀ j, childrenD_72 j ⊆ envelope_72 := by decide
theorem pivot_mem_72 : (0, 0) ∈ envelope_72 := by decide
theorem children_work_72 : ∀ j, Template HasSnaky 3 (childrenC_72 j) (childrenD_72 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (-1, 4)).mono (by decide)
  · exact (placed_template_map row_works_8 6 (1, 0)).mono (by decide)
theorem row_works_72 : Template HasSnaky 4 required_72 envelope_72 := by
  refine compose HasSnaky 3 childrenC_72 childrenD_72 children_work_72 (0, 0)
    required_72 envelope_72 pivot_mem_72 child_required_sub_72 child_envelope_sub_72 ?_
  intro b hb; exact common_sub_72 (mem_commonEnvelope childrenD_72 b hb)
def required_74 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2), (2, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_74 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (2, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_74 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) required_2), (placedSet 0 (-1, -1) required_53)]
def childrenD_74 : Fin 2 → Finset Cell := ![(placedSet 7 (0, -1) envelope_2), (placedSet 0 (-1, -1) envelope_53)]
theorem common_sub_74 : commonEnvelope childrenD_74 ⊆ insert (0, 0) required_74 := by decide
theorem child_required_sub_74 : ∀ j, childrenC_74 j ⊆ insert (0, 0) required_74 := by decide
theorem child_envelope_sub_74 : ∀ j, childrenD_74 j ⊆ envelope_74 := by decide
theorem pivot_mem_74 : (0, 0) ∈ envelope_74 := by decide
theorem children_work_74 : ∀ j, Template HasSnaky 3 (childrenC_74 j) (childrenD_74 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 7 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_53 0 (-1, -1)).mono (by decide)
theorem row_works_74 : Template HasSnaky 4 required_74 envelope_74 := by
  refine compose HasSnaky 3 childrenC_74 childrenD_74 children_work_74 (0, 0)
    required_74 envelope_74 pivot_mem_74 child_required_sub_74 child_envelope_sub_74 ?_
  intro b hb; exact common_sub_74 (mem_commonEnvelope childrenD_74 b hb)
def required_75 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_75 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_75 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) required_0), (placedSet 0 (3, -1) required_9)]
def childrenD_75 : Fin 2 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_0), (placedSet 0 (3, -1) envelope_9)]
theorem common_sub_75 : commonEnvelope childrenD_75 ⊆ insert (0, 0) required_75 := by decide
theorem child_required_sub_75 : ∀ j, childrenC_75 j ⊆ insert (0, 0) required_75 := by decide
theorem child_envelope_sub_75 : ∀ j, childrenD_75 j ⊆ envelope_75 := by decide
theorem pivot_mem_75 : (0, 0) ∈ envelope_75 := by decide
theorem children_work_75 : ∀ j, Template HasSnaky 3 (childrenC_75 j) (childrenD_75 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_9 0 (3, -1)).mono (by decide)
theorem row_works_75 : Template HasSnaky 4 required_75 envelope_75 := by
  refine compose HasSnaky 3 childrenC_75 childrenD_75 children_work_75 (0, 0)
    required_75 envelope_75 pivot_mem_75 child_required_sub_75 child_envelope_sub_75 ?_
  intro b hb; exact common_sub_75 (mem_commonEnvelope childrenD_75 b hb)
def required_79 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_79 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_79 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) required_6), (placedSet 0 (-1, 0) required_48)]
def childrenD_79 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) envelope_6), (placedSet 0 (-1, 0) envelope_48)]
theorem common_sub_79 : commonEnvelope childrenD_79 ⊆ insert (0, 0) required_79 := by decide
theorem child_required_sub_79 : ∀ j, childrenC_79 j ⊆ insert (0, 0) required_79 := by decide
theorem child_envelope_sub_79 : ∀ j, childrenD_79 j ⊆ envelope_79 := by decide
theorem pivot_mem_79 : (0, 0) ∈ envelope_79 := by decide
theorem children_work_79 : ∀ j, Template HasSnaky 3 (childrenC_79 j) (childrenD_79 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_48 0 (-1, 0)).mono (by decide)
theorem row_works_79 : Template HasSnaky 4 required_79 envelope_79 := by
  refine compose HasSnaky 3 childrenC_79 childrenD_79 children_work_79 (0, 0)
    required_79 envelope_79 pivot_mem_79 child_required_sub_79 child_envelope_sub_79 ?_
  intro b hb; exact common_sub_79 (mem_commonEnvelope childrenD_79 b hb)
def required_80 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_80 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_80 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) required_0), (placedSet 4 (-2, 0) required_13)]
def childrenD_80 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) envelope_0), (placedSet 4 (-2, 0) envelope_13)]
theorem common_sub_80 : commonEnvelope childrenD_80 ⊆ insert (0, 0) required_80 := by decide
theorem child_required_sub_80 : ∀ j, childrenC_80 j ⊆ insert (0, 0) required_80 := by decide
theorem child_envelope_sub_80 : ∀ j, childrenD_80 j ⊆ envelope_80 := by decide
theorem pivot_mem_80 : (0, 0) ∈ envelope_80 := by decide
theorem children_work_80 : ∀ j, Template HasSnaky 3 (childrenC_80 j) (childrenD_80 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_13 4 (-2, 0)).mono (by decide)
theorem row_works_80 : Template HasSnaky 4 required_80 envelope_80 := by
  refine compose HasSnaky 3 childrenC_80 childrenD_80 children_work_80 (0, 0)
    required_80 envelope_80 pivot_mem_80 child_required_sub_80 child_envelope_sub_80 ?_
  intro b hb; exact common_sub_80 (mem_commonEnvelope childrenD_80 b hb)
end SnakyConditional

end OAI
