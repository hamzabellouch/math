import OAI.GameTheory.SnakyConditional.Templates.Level05Part01
import OAI.GameTheory.SnakyConditional.Templates.Level05Part02
import OAI.GameTheory.SnakyConditional.Templates.Level05Part04
import OAI.GameTheory.SnakyConditional.Templates.Level05Part05
import OAI.GameTheory.SnakyConditional.Templates.Level05Part06
import OAI.GameTheory.SnakyConditional.Templates.Level05Part07

namespace OAI

namespace SnakyConditional
def required_81 : Finset Cell := ⟨(([(1, -4), (1, -3), (1, -2), (1, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_81 : Finset Cell := ⟨(([(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_81 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) required_4), (placedSet 0 (1, 0) required_43)]
def childrenD_81 : Fin 2 → Finset Cell := ![(placedSet 3 (0, -1) envelope_4), (placedSet 0 (1, 0) envelope_43)]
theorem common_sub_81 : commonEnvelope childrenD_81 ⊆ insert (0, 0) required_81 := by decide
theorem child_required_sub_81 : ∀ j, childrenC_81 j ⊆ insert (0, 0) required_81 := by decide
theorem child_envelope_sub_81 : ∀ j, childrenD_81 j ⊆ envelope_81 := by decide
theorem pivot_mem_81 : (0, 0) ∈ envelope_81 := by decide
theorem children_work_81 : ∀ j, Template HasSnaky 3 (childrenC_81 j) (childrenD_81 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_43 0 (1, 0)).mono (by decide)
theorem row_works_81 : Template HasSnaky 4 required_81 envelope_81 := by
  refine compose HasSnaky 3 childrenC_81 childrenD_81 children_work_81 (0, 0)
    required_81 envelope_81 pivot_mem_81 child_required_sub_81 child_envelope_sub_81 ?_
  intro b hb; exact common_sub_81 (mem_commonEnvelope childrenD_81 b hb)
def required_82 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_82 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_82 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (-3, -1) required_36)]
def childrenD_82 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (-3, -1) envelope_36)]
theorem common_sub_82 : commonEnvelope childrenD_82 ⊆ insert (0, 0) required_82 := by decide
theorem child_required_sub_82 : ∀ j, childrenC_82 j ⊆ insert (0, 0) required_82 := by decide
theorem child_envelope_sub_82 : ∀ j, childrenD_82 j ⊆ envelope_82 := by decide
theorem pivot_mem_82 : (0, 0) ∈ envelope_82 := by decide
theorem children_work_82 : ∀ j, Template HasSnaky 3 (childrenC_82 j) (childrenD_82 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_36 0 (-3, -1)).mono (by decide)
theorem row_works_82 : Template HasSnaky 4 required_82 envelope_82 := by
  refine compose HasSnaky 3 childrenC_82 childrenD_82 children_work_82 (0, 0)
    required_82 envelope_82 pivot_mem_82 child_required_sub_82 child_envelope_sub_82 ?_
  intro b hb; exact common_sub_82 (mem_commonEnvelope childrenD_82 b hb)
def required_85 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_85 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_85 : Fin 2 → Finset Cell := ![(placedSet 0 (2, -1) required_9), (placedSet 4 (1, 0) required_8)]
def childrenD_85 : Fin 2 → Finset Cell := ![(placedSet 0 (2, -1) envelope_9), (placedSet 4 (1, 0) envelope_8)]
theorem common_sub_85 : commonEnvelope childrenD_85 ⊆ insert (0, 0) required_85 := by decide
theorem child_required_sub_85 : ∀ j, childrenC_85 j ⊆ insert (0, 0) required_85 := by decide
theorem child_envelope_sub_85 : ∀ j, childrenD_85 j ⊆ envelope_85 := by decide
theorem pivot_mem_85 : (0, 0) ∈ envelope_85 := by decide
theorem children_work_85 : ∀ j, Template HasSnaky 3 (childrenC_85 j) (childrenD_85 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_9 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_8 4 (1, 0)).mono (by decide)
theorem row_works_85 : Template HasSnaky 4 required_85 envelope_85 := by
  refine compose HasSnaky 3 childrenC_85 childrenD_85 children_work_85 (0, 0)
    required_85 envelope_85 pivot_mem_85 child_required_sub_85 child_envelope_sub_85 ?_
  intro b hb; exact common_sub_85 (mem_commonEnvelope childrenD_85 b hb)
def required_87 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_87 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_87 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) required_0), (placedSet 2 (1, -1) required_24)]
def childrenD_87 : Fin 2 → Finset Cell := ![(placedSet 5 (-1, 3) envelope_0), (placedSet 2 (1, -1) envelope_24)]
theorem common_sub_87 : commonEnvelope childrenD_87 ⊆ insert (0, 0) required_87 := by decide
theorem child_required_sub_87 : ∀ j, childrenC_87 j ⊆ insert (0, 0) required_87 := by decide
theorem child_envelope_sub_87 : ∀ j, childrenD_87 j ⊆ envelope_87 := by decide
theorem pivot_mem_87 : (0, 0) ∈ envelope_87 := by decide
theorem children_work_87 : ∀ j, Template HasSnaky 3 (childrenC_87 j) (childrenD_87 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 5 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_24 2 (1, -1)).mono (by decide)
theorem row_works_87 : Template HasSnaky 4 required_87 envelope_87 := by
  refine compose HasSnaky 3 childrenC_87 childrenD_87 children_work_87 (0, 0)
    required_87 envelope_87 pivot_mem_87 child_required_sub_87 child_envelope_sub_87 ?_
  intro b hb; exact common_sub_87 (mem_commonEnvelope childrenD_87 b hb)
def required_89 : Finset Cell := ⟨(([(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_89 : Finset Cell := ⟨(([(-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_89 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -3) required_8), (placedSet 1 (1, 0) required_7)]
def childrenD_89 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -3) envelope_8), (placedSet 1 (1, 0) envelope_7)]
theorem common_sub_89 : commonEnvelope childrenD_89 ⊆ insert (0, 0) required_89 := by decide
theorem child_required_sub_89 : ∀ j, childrenC_89 j ⊆ insert (0, 0) required_89 := by decide
theorem child_envelope_sub_89 : ∀ j, childrenD_89 j ⊆ envelope_89 := by decide
theorem pivot_mem_89 : (0, 0) ∈ envelope_89 := by decide
theorem children_work_89 : ∀ j, Template HasSnaky 3 (childrenC_89 j) (childrenD_89 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_8 3 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
theorem row_works_89 : Template HasSnaky 4 required_89 envelope_89 := by
  refine compose HasSnaky 3 childrenC_89 childrenD_89 children_work_89 (0, 0)
    required_89 envelope_89 pivot_mem_89 child_required_sub_89 child_envelope_sub_89 ?_
  intro b hb; exact common_sub_89 (mem_commonEnvelope childrenD_89 b hb)
def required_90 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_90 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_90 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, -1) required_31), (placedSet 6 (-4, -1) required_54), (placedSet 0 (1, 0) required_54), (placedSet 6 (-2, 0) required_31)]
def childrenD_90 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, -1) envelope_31), (placedSet 6 (-4, -1) envelope_54), (placedSet 0 (1, 0) envelope_54), (placedSet 6 (-2, 0) envelope_31)]
theorem common_sub_90 : commonEnvelope childrenD_90 ⊆ insert (0, 0) required_90 := by decide
theorem child_required_sub_90 : ∀ j, childrenC_90 j ⊆ insert (0, 0) required_90 := by decide
theorem child_envelope_sub_90 : ∀ j, childrenD_90 j ⊆ envelope_90 := by decide
theorem pivot_mem_90 : (0, 0) ∈ envelope_90 := by decide
theorem children_work_90 : ∀ j, Template HasSnaky 3 (childrenC_90 j) (childrenD_90 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_31 0 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_54 6 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_54 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_31 6 (-2, 0)).mono (by decide)
theorem row_works_90 : Template HasSnaky 4 required_90 envelope_90 := by
  refine compose HasSnaky 3 childrenC_90 childrenD_90 children_work_90 (0, 0)
    required_90 envelope_90 pivot_mem_90 child_required_sub_90 child_envelope_sub_90 ?_
  intro b hb; exact common_sub_90 (mem_commonEnvelope childrenD_90 b hb)
def required_92 : Finset Cell := ⟨(([(-3, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_92 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_92 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 0 (-2, -1) required_33)]
def childrenD_92 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 0 (-2, -1) envelope_33)]
theorem common_sub_92 : commonEnvelope childrenD_92 ⊆ insert (0, 0) required_92 := by decide
theorem child_required_sub_92 : ∀ j, childrenC_92 j ⊆ insert (0, 0) required_92 := by decide
theorem child_envelope_sub_92 : ∀ j, childrenD_92 j ⊆ envelope_92 := by decide
theorem pivot_mem_92 : (0, 0) ∈ envelope_92 := by decide
theorem children_work_92 : ∀ j, Template HasSnaky 3 (childrenC_92 j) (childrenD_92 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_33 0 (-2, -1)).mono (by decide)
theorem row_works_92 : Template HasSnaky 4 required_92 envelope_92 := by
  refine compose HasSnaky 3 childrenC_92 childrenD_92 children_work_92 (0, 0)
    required_92 envelope_92 pivot_mem_92 child_required_sub_92 child_envelope_sub_92 ?_
  intro b hb; exact common_sub_92 (mem_commonEnvelope childrenD_92 b hb)
end SnakyConditional

end OAI
