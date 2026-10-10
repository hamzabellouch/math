import OAI.GameTheory.SnakyConditional.Templates.Level06Part06
import OAI.GameTheory.SnakyConditional.Templates.Level07Part01
import OAI.GameTheory.SnakyConditional.Templates.Level07Part02
import OAI.GameTheory.SnakyConditional.Templates.Level07Part03
import OAI.GameTheory.SnakyConditional.Templates.Level07Part05
import OAI.GameTheory.SnakyConditional.Templates.Level07Part06

namespace OAI

namespace SnakyConditional
def required_180 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_180 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_180 : Fin 4 → Finset Cell := ![(placedSet 3 (-1, 0) required_7), (placedSet 0 (-1, 1) required_63), (placedSet 0 (0, 1) required_155), (placedSet 0 (-1, -1) required_132)]
def childrenD_180 : Fin 4 → Finset Cell := ![(placedSet 3 (-1, 0) envelope_7), (placedSet 0 (-1, 1) envelope_63), (placedSet 0 (0, 1) envelope_155), (placedSet 0 (-1, -1) envelope_132)]
theorem common_sub_180 : commonEnvelope childrenD_180 ⊆ insert (0, 0) required_180 := by decide
theorem child_required_sub_180 : ∀ j, childrenC_180 j ⊆ insert (0, 0) required_180 := by decide
theorem child_envelope_sub_180 : ∀ j, childrenD_180 j ⊆ envelope_180 := by decide
theorem pivot_mem_180 : (0, 0) ∈ envelope_180 := by decide
theorem children_work_180 : ∀ j, Template HasSnaky 5 (childrenC_180 j) (childrenD_180 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_155 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_132 0 (-1, -1)).mono (by decide)
theorem row_works_180 : Template HasSnaky 6 required_180 envelope_180 := by
  refine compose HasSnaky 5 childrenC_180 childrenD_180 children_work_180 (0, 0)
    required_180 envelope_180 pivot_mem_180 child_required_sub_180 child_envelope_sub_180 ?_
  intro b hb; exact common_sub_180 (mem_commonEnvelope childrenD_180 b hb)
def required_183 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_183 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_183 : Fin 3 → Finset Cell := ![(placedSet 2 (-3, 1) required_64), (placedSet 3 (-4, -1) required_63), (placedSet 2 (1, 0) required_55)]
def childrenD_183 : Fin 3 → Finset Cell := ![(placedSet 2 (-3, 1) envelope_64), (placedSet 3 (-4, -1) envelope_63), (placedSet 2 (1, 0) envelope_55)]
theorem common_sub_183 : commonEnvelope childrenD_183 ⊆ insert (0, 0) required_183 := by decide
theorem child_required_sub_183 : ∀ j, childrenC_183 j ⊆ insert (0, 0) required_183 := by decide
theorem child_envelope_sub_183 : ∀ j, childrenD_183 j ⊆ envelope_183 := by decide
theorem pivot_mem_183 : (0, 0) ∈ envelope_183 := by decide
theorem children_work_183 : ∀ j, Template HasSnaky 5 (childrenC_183 j) (childrenD_183 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 2 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_63 3 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 2 (1, 0)).mono (by decide)
theorem row_works_183 : Template HasSnaky 6 required_183 envelope_183 := by
  refine compose HasSnaky 5 childrenC_183 childrenD_183 children_work_183 (0, 0)
    required_183 envelope_183 pivot_mem_183 child_required_sub_183 child_envelope_sub_183 ?_
  intro b hb; exact common_sub_183 (mem_commonEnvelope childrenD_183 b hb)
def required_185 : Finset Cell := ⟨(([(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_185 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_185 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) required_44), (placedSet 0 (0, 1) required_49), (placedSet 0 (-1, 0) required_84)]
def childrenD_185 : Fin 3 → Finset Cell := ![(placedSet 3 (0, 1) envelope_44), (placedSet 0 (0, 1) envelope_49), (placedSet 0 (-1, 0) envelope_84)]
theorem common_sub_185 : commonEnvelope childrenD_185 ⊆ insert (0, 0) required_185 := by decide
theorem child_required_sub_185 : ∀ j, childrenC_185 j ⊆ insert (0, 0) required_185 := by decide
theorem child_envelope_sub_185 : ∀ j, childrenD_185 j ⊆ envelope_185 := by decide
theorem pivot_mem_185 : (0, 0) ∈ envelope_185 := by decide
theorem children_work_185 : ∀ j, Template HasSnaky 5 (childrenC_185 j) (childrenD_185 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_44 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_49 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_84 0 (-1, 0)).mono (by decide)
theorem row_works_185 : Template HasSnaky 6 required_185 envelope_185 := by
  refine compose HasSnaky 5 childrenC_185 childrenD_185 children_work_185 (0, 0)
    required_185 envelope_185 pivot_mem_185 child_required_sub_185 child_envelope_sub_185 ?_
  intro b hb; exact common_sub_185 (mem_commonEnvelope childrenD_185 b hb)
def required_188 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -2), (4, -2), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_188 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_188 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 5 (3, 0) required_112)]
def childrenD_188 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 5 (3, 0) envelope_112)]
theorem common_sub_188 : commonEnvelope childrenD_188 ⊆ insert (0, 0) required_188 := by decide
theorem child_required_sub_188 : ∀ j, childrenC_188 j ⊆ insert (0, 0) required_188 := by decide
theorem child_envelope_sub_188 : ∀ j, childrenD_188 j ⊆ envelope_188 := by decide
theorem pivot_mem_188 : (0, 0) ∈ envelope_188 := by decide
theorem children_work_188 : ∀ j, Template HasSnaky 5 (childrenC_188 j) (childrenD_188 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_112 5 (3, 0)).mono (by decide)
theorem row_works_188 : Template HasSnaky 6 required_188 envelope_188 := by
  refine compose HasSnaky 5 childrenC_188 childrenD_188 children_work_188 (0, 0)
    required_188 envelope_188 pivot_mem_188 child_required_sub_188 child_envelope_sub_188 ?_
  intro b hb; exact common_sub_188 (mem_commonEnvelope childrenD_188 b hb)
def required_189 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_189 : Finset Cell := ⟨(([(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_189 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_12), (placedSet 4 (-3, 0) required_86)]
def childrenD_189 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_12), (placedSet 4 (-3, 0) envelope_86)]
theorem common_sub_189 : commonEnvelope childrenD_189 ⊆ insert (0, 0) required_189 := by decide
theorem child_required_sub_189 : ∀ j, childrenC_189 j ⊆ insert (0, 0) required_189 := by decide
theorem child_envelope_sub_189 : ∀ j, childrenD_189 j ⊆ envelope_189 := by decide
theorem pivot_mem_189 : (0, 0) ∈ envelope_189 := by decide
theorem children_work_189 : ∀ j, Template HasSnaky 5 (childrenC_189 j) (childrenD_189 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_12 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_86 4 (-3, 0)).mono (by decide)
theorem row_works_189 : Template HasSnaky 6 required_189 envelope_189 := by
  refine compose HasSnaky 5 childrenC_189 childrenD_189 children_work_189 (0, 0)
    required_189 envelope_189 pivot_mem_189 child_required_sub_189 child_envelope_sub_189 ?_
  intro b hb; exact common_sub_189 (mem_commonEnvelope childrenD_189 b hb)
def required_192 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_192 : Finset Cell := ⟨(([(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_192 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, -3) required_64), (placedSet 0 (-1, 0) required_103), (placedSet 3 (0, 1) required_55)]
def childrenD_192 : Fin 3 → Finset Cell := ![(placedSet 1 (-1, -3) envelope_64), (placedSet 0 (-1, 0) envelope_103), (placedSet 3 (0, 1) envelope_55)]
theorem common_sub_192 : commonEnvelope childrenD_192 ⊆ insert (0, 0) required_192 := by decide
theorem child_required_sub_192 : ∀ j, childrenC_192 j ⊆ insert (0, 0) required_192 := by decide
theorem child_envelope_sub_192 : ∀ j, childrenD_192 j ⊆ envelope_192 := by decide
theorem pivot_mem_192 : (0, 0) ∈ envelope_192 := by decide
theorem children_work_192 : ∀ j, Template HasSnaky 5 (childrenC_192 j) (childrenD_192 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 1 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_103 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_55 3 (0, 1)).mono (by decide)
theorem row_works_192 : Template HasSnaky 6 required_192 envelope_192 := by
  refine compose HasSnaky 5 childrenC_192 childrenD_192 children_work_192 (0, 0)
    required_192 envelope_192 pivot_mem_192 child_required_sub_192 child_envelope_sub_192 ?_
  intro b hb; exact common_sub_192 (mem_commonEnvelope childrenD_192 b hb)
def required_197 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_197 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_197 : Fin 2 → Finset Cell := ![(placedSet 3 (-4, -1) required_63), (placedSet 1 (1, -1) required_63)]
def childrenD_197 : Fin 2 → Finset Cell := ![(placedSet 3 (-4, -1) envelope_63), (placedSet 1 (1, -1) envelope_63)]
theorem common_sub_197 : commonEnvelope childrenD_197 ⊆ insert (0, 0) required_197 := by decide
theorem child_required_sub_197 : ∀ j, childrenC_197 j ⊆ insert (0, 0) required_197 := by decide
theorem child_envelope_sub_197 : ∀ j, childrenD_197 j ⊆ envelope_197 := by decide
theorem pivot_mem_197 : (0, 0) ∈ envelope_197 := by decide
theorem children_work_197 : ∀ j, Template HasSnaky 5 (childrenC_197 j) (childrenD_197 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 3 (-4, -1)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
theorem row_works_197 : Template HasSnaky 6 required_197 envelope_197 := by
  refine compose HasSnaky 5 childrenC_197 childrenD_197 children_work_197 (0, 0)
    required_197 envelope_197 pivot_mem_197 child_required_sub_197 child_envelope_sub_197 ?_
  intro b hb; exact common_sub_197 (mem_commonEnvelope childrenD_197 b hb)
end SnakyConditional

end OAI
