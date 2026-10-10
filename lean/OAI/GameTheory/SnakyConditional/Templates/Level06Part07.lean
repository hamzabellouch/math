import OAI.GameTheory.SnakyConditional.Templates.Level05Part01
import OAI.GameTheory.SnakyConditional.Templates.Level05Part02
import OAI.GameTheory.SnakyConditional.Templates.Level05Part03
import OAI.GameTheory.SnakyConditional.Templates.Level05Part04
import OAI.GameTheory.SnakyConditional.Templates.Level05Part05
import OAI.GameTheory.SnakyConditional.Templates.Level05Part08

namespace OAI

namespace SnakyConditional
def required_124 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_124 : Finset Cell := ⟨(([(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_124 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 2 (1, 0) required_31)]
def childrenD_124 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 2 (1, 0) envelope_31)]
theorem common_sub_124 : commonEnvelope childrenD_124 ⊆ insert (0, 0) required_124 := by decide
theorem child_required_sub_124 : ∀ j, childrenC_124 j ⊆ insert (0, 0) required_124 := by decide
theorem child_envelope_sub_124 : ∀ j, childrenD_124 j ⊆ envelope_124 := by decide
theorem pivot_mem_124 : (0, 0) ∈ envelope_124 := by decide
theorem children_work_124 : ∀ j, Template HasSnaky 3 (childrenC_124 j) (childrenD_124 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_31 2 (1, 0)).mono (by decide)
theorem row_works_124 : Template HasSnaky 4 required_124 envelope_124 := by
  refine compose HasSnaky 3 childrenC_124 childrenD_124 children_work_124 (0, 0)
    required_124 envelope_124 pivot_mem_124 child_required_sub_124 child_envelope_sub_124 ?_
  intro b hb; exact common_sub_124 (mem_commonEnvelope childrenD_124 b hb)
def required_125 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_125 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_125 : Fin 2 → Finset Cell := ![(placedSet 0 (0, -1) required_3), (placedSet 2 (0, 1) required_31)]
def childrenD_125 : Fin 2 → Finset Cell := ![(placedSet 0 (0, -1) envelope_3), (placedSet 2 (0, 1) envelope_31)]
theorem common_sub_125 : commonEnvelope childrenD_125 ⊆ insert (0, 0) required_125 := by decide
theorem child_required_sub_125 : ∀ j, childrenC_125 j ⊆ insert (0, 0) required_125 := by decide
theorem child_envelope_sub_125 : ∀ j, childrenD_125 j ⊆ envelope_125 := by decide
theorem pivot_mem_125 : (0, 0) ∈ envelope_125 := by decide
theorem children_work_125 : ∀ j, Template HasSnaky 3 (childrenC_125 j) (childrenD_125 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_3 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_31 2 (0, 1)).mono (by decide)
theorem row_works_125 : Template HasSnaky 4 required_125 envelope_125 := by
  refine compose HasSnaky 3 childrenC_125 childrenD_125 children_work_125 (0, 0)
    required_125 envelope_125 pivot_mem_125 child_required_sub_125 child_envelope_sub_125 ?_
  intro b hb; exact common_sub_125 (mem_commonEnvelope childrenD_125 b hb)
def required_138 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 2), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_138 : Finset Cell := ⟨(([(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_138 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_27), (placedSet 1 (0, 3) required_10)]
def childrenD_138 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_27), (placedSet 1 (0, 3) envelope_10)]
theorem common_sub_138 : commonEnvelope childrenD_138 ⊆ insert (0, 0) required_138 := by decide
theorem child_required_sub_138 : ∀ j, childrenC_138 j ⊆ insert (0, 0) required_138 := by decide
theorem child_envelope_sub_138 : ∀ j, childrenD_138 j ⊆ envelope_138 := by decide
theorem pivot_mem_138 : (0, 0) ∈ envelope_138 := by decide
theorem children_work_138 : ∀ j, Template HasSnaky 3 (childrenC_138 j) (childrenD_138 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_27 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_10 1 (0, 3)).mono (by decide)
theorem row_works_138 : Template HasSnaky 4 required_138 envelope_138 := by
  refine compose HasSnaky 3 childrenC_138 childrenD_138 children_work_138 (0, 0)
    required_138 envelope_138 pivot_mem_138 child_required_sub_138 child_envelope_sub_138 ?_
  intro b hb; exact common_sub_138 (mem_commonEnvelope childrenD_138 b hb)
def required_139 : Finset Cell := ⟨(([(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_139 : Finset Cell := ⟨(([(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_139 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_28), (placedSet 0 (1, 0) required_27)]
def childrenD_139 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_28), (placedSet 0 (1, 0) envelope_27)]
theorem common_sub_139 : commonEnvelope childrenD_139 ⊆ insert (0, 0) required_139 := by decide
theorem child_required_sub_139 : ∀ j, childrenC_139 j ⊆ insert (0, 0) required_139 := by decide
theorem child_envelope_sub_139 : ∀ j, childrenD_139 j ⊆ envelope_139 := by decide
theorem pivot_mem_139 : (0, 0) ∈ envelope_139 := by decide
theorem children_work_139 : ∀ j, Template HasSnaky 3 (childrenC_139 j) (childrenD_139 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_28 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_27 0 (1, 0)).mono (by decide)
theorem row_works_139 : Template HasSnaky 4 required_139 envelope_139 := by
  refine compose HasSnaky 3 childrenC_139 childrenD_139 children_work_139 (0, 0)
    required_139 envelope_139 pivot_mem_139 child_required_sub_139 child_envelope_sub_139 ?_
  intro b hb; exact common_sub_139 (mem_commonEnvelope childrenD_139 b hb)
def required_141 : Finset Cell := ⟨(([(-5, 0), (-4, 0), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_141 : Finset Cell := ⟨(([(-6, 0), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_141 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) required_7), (placedSet 2 (-3, -1) required_78)]
def childrenD_141 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 1) envelope_7), (placedSet 2 (-3, -1) envelope_78)]
theorem common_sub_141 : commonEnvelope childrenD_141 ⊆ insert (0, 0) required_141 := by decide
theorem child_required_sub_141 : ∀ j, childrenC_141 j ⊆ insert (0, 0) required_141 := by decide
theorem child_envelope_sub_141 : ∀ j, childrenD_141 j ⊆ envelope_141 := by decide
theorem pivot_mem_141 : (0, 0) ∈ envelope_141 := by decide
theorem children_work_141 : ∀ j, Template HasSnaky 3 (childrenC_141 j) (childrenD_141 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_78 2 (-3, -1)).mono (by decide)
theorem row_works_141 : Template HasSnaky 4 required_141 envelope_141 := by
  refine compose HasSnaky 3 childrenC_141 childrenD_141 children_work_141 (0, 0)
    required_141 envelope_141 pivot_mem_141 child_required_sub_141 child_envelope_sub_141 ?_
  intro b hb; exact common_sub_141 (mem_commonEnvelope childrenD_141 b hb)
def required_146 : Finset Cell := ⟨(([(-2, -1), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_146 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_146 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_36), (placedSet 1 (0, 1) required_24)]
def childrenD_146 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_36), (placedSet 1 (0, 1) envelope_24)]
theorem common_sub_146 : commonEnvelope childrenD_146 ⊆ insert (0, 0) required_146 := by decide
theorem child_required_sub_146 : ∀ j, childrenC_146 j ⊆ insert (0, 0) required_146 := by decide
theorem child_envelope_sub_146 : ∀ j, childrenD_146 j ⊆ envelope_146 := by decide
theorem pivot_mem_146 : (0, 0) ∈ envelope_146 := by decide
theorem children_work_146 : ∀ j, Template HasSnaky 3 (childrenC_146 j) (childrenD_146 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_36 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_24 1 (0, 1)).mono (by decide)
theorem row_works_146 : Template HasSnaky 4 required_146 envelope_146 := by
  refine compose HasSnaky 3 childrenC_146 childrenD_146 children_work_146 (0, 0)
    required_146 envelope_146 pivot_mem_146 child_required_sub_146 child_envelope_sub_146 ?_
  intro b hb; exact common_sub_146 (mem_commonEnvelope childrenD_146 b hb)
def required_149 : Finset Cell := ⟨(([(-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_149 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_149 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) required_16), (placedSet 2 (1, 0) required_24)]
def childrenD_149 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -1) envelope_16), (placedSet 2 (1, 0) envelope_24)]
theorem common_sub_149 : commonEnvelope childrenD_149 ⊆ insert (0, 0) required_149 := by decide
theorem child_required_sub_149 : ∀ j, childrenC_149 j ⊆ insert (0, 0) required_149 := by decide
theorem child_envelope_sub_149 : ∀ j, childrenD_149 j ⊆ envelope_149 := by decide
theorem pivot_mem_149 : (0, 0) ∈ envelope_149 := by decide
theorem children_work_149 : ∀ j, Template HasSnaky 3 (childrenC_149 j) (childrenD_149 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_16 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_24 2 (1, 0)).mono (by decide)
theorem row_works_149 : Template HasSnaky 4 required_149 envelope_149 := by
  refine compose HasSnaky 3 childrenC_149 childrenD_149 children_work_149 (0, 0)
    required_149 envelope_149 pivot_mem_149 child_required_sub_149 child_envelope_sub_149 ?_
  intro b hb; exact common_sub_149 (mem_commonEnvelope childrenD_149 b hb)
end SnakyConditional

end OAI
