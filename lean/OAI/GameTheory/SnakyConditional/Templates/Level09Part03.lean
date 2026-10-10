import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part02
import OAI.GameTheory.SnakyConditional.Templates.Level08Part05

namespace OAI

namespace SnakyConditional
def required_203 : Finset Cell := ⟨(([(-4, -1), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_203 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_203 : Fin 3 → Finset Cell := ![(placedSet 6 (-3, -1) required_18), (placedSet 0 (1, 0) required_107), (placedSet 0 (1, 0) required_163)]
def childrenD_203 : Fin 3 → Finset Cell := ![(placedSet 6 (-3, -1) envelope_18), (placedSet 0 (1, 0) envelope_107), (placedSet 0 (1, 0) envelope_163)]
theorem common_sub_203 : commonEnvelope childrenD_203 ⊆ insert (0, 0) required_203 := by decide
theorem child_required_sub_203 : ∀ j, childrenC_203 j ⊆ insert (0, 0) required_203 := by decide
theorem child_envelope_sub_203 : ∀ j, childrenD_203 j ⊆ envelope_203 := by decide
theorem pivot_mem_203 : (0, 0) ∈ envelope_203 := by decide
theorem children_work_203 : ∀ j, Template HasSnaky 6 (childrenC_203 j) (childrenD_203 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_18 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_107 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_163 0 (1, 0)).mono (by decide)
theorem row_works_203 : Template HasSnaky 7 required_203 envelope_203 := by
  refine compose HasSnaky 6 childrenC_203 childrenD_203 children_work_203 (0, 0)
    required_203 envelope_203 pivot_mem_203 child_required_sub_203 child_envelope_sub_203 ?_
  intro b hb; exact common_sub_203 (mem_commonEnvelope childrenD_203 b hb)
def required_212 : Finset Cell := ⟨(([(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_212 : Finset Cell := ⟨(([(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_212 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (-4, 1) required_188)]
def childrenD_212 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (-4, 1) envelope_188)]
theorem common_sub_212 : commonEnvelope childrenD_212 ⊆ insert (0, 0) required_212 := by decide
theorem child_required_sub_212 : ∀ j, childrenC_212 j ⊆ insert (0, 0) required_212 := by decide
theorem child_envelope_sub_212 : ∀ j, childrenD_212 j ⊆ envelope_212 := by decide
theorem pivot_mem_212 : (0, 0) ∈ envelope_212 := by decide
theorem children_work_212 : ∀ j, Template HasSnaky 6 (childrenC_212 j) (childrenD_212 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_188 0 (-4, 1)).mono (by decide)
theorem row_works_212 : Template HasSnaky 7 required_212 envelope_212 := by
  refine compose HasSnaky 6 childrenC_212 childrenD_212 children_work_212 (0, 0)
    required_212 envelope_212 pivot_mem_212 child_required_sub_212 child_envelope_sub_212 ?_
  intro b hb; exact common_sub_212 (mem_commonEnvelope childrenD_212 b hb)
def required_214 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_214 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 1), (1, 2), (1, 3), (2, -2), (3, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_214 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) required_7), (placedSet 3 (0, 1) required_108), (placedSet 0 (1, -2) required_95)]
def childrenD_214 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) envelope_7), (placedSet 3 (0, 1) envelope_108), (placedSet 0 (1, -2) envelope_95)]
theorem common_sub_214 : commonEnvelope childrenD_214 ⊆ insert (0, 0) required_214 := by decide
theorem child_required_sub_214 : ∀ j, childrenC_214 j ⊆ insert (0, 0) required_214 := by decide
theorem child_envelope_sub_214 : ∀ j, childrenD_214 j ⊆ envelope_214 := by decide
theorem pivot_mem_214 : (0, 0) ∈ envelope_214 := by decide
theorem children_work_214 : ∀ j, Template HasSnaky 6 (childrenC_214 j) (childrenD_214 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_108 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_95 0 (1, -2)).mono (by decide)
theorem row_works_214 : Template HasSnaky 7 required_214 envelope_214 := by
  refine compose HasSnaky 6 childrenC_214 childrenD_214 children_work_214 (0, 0)
    required_214 envelope_214 pivot_mem_214 child_required_sub_214 child_envelope_sub_214 ?_
  intro b hb; exact common_sub_214 (mem_commonEnvelope childrenD_214 b hb)
def required_215 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_215 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_215 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 2) required_107), (placedSet 0 (1, 0) required_24)]
def childrenD_215 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 2) envelope_107), (placedSet 0 (1, 0) envelope_24)]
theorem common_sub_215 : commonEnvelope childrenD_215 ⊆ insert (0, 0) required_215 := by decide
theorem child_required_sub_215 : ∀ j, childrenC_215 j ⊆ insert (0, 0) required_215 := by decide
theorem child_envelope_sub_215 : ∀ j, childrenD_215 j ⊆ envelope_215 := by decide
theorem pivot_mem_215 : (0, 0) ∈ envelope_215 := by decide
theorem children_work_215 : ∀ j, Template HasSnaky 6 (childrenC_215 j) (childrenD_215 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_107 1 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_24 0 (1, 0)).mono (by decide)
theorem row_works_215 : Template HasSnaky 7 required_215 envelope_215 := by
  refine compose HasSnaky 6 childrenC_215 childrenD_215 children_work_215 (0, 0)
    required_215 envelope_215 pivot_mem_215 child_required_sub_215 child_envelope_sub_215 ?_
  intro b hb; exact common_sub_215 (mem_commonEnvelope childrenD_215 b hb)
def required_217 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_217 : Finset Cell := ⟨(([(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_217 : Fin 3 → Finset Cell := ![(placedSet 1 (-3, -1) required_111), (placedSet 4 (-4, 0) required_55), (placedSet 0 (-3, -1) required_64)]
def childrenD_217 : Fin 3 → Finset Cell := ![(placedSet 1 (-3, -1) envelope_111), (placedSet 4 (-4, 0) envelope_55), (placedSet 0 (-3, -1) envelope_64)]
theorem common_sub_217 : commonEnvelope childrenD_217 ⊆ insert (0, 0) required_217 := by decide
theorem child_required_sub_217 : ∀ j, childrenC_217 j ⊆ insert (0, 0) required_217 := by decide
theorem child_envelope_sub_217 : ∀ j, childrenD_217 j ⊆ envelope_217 := by decide
theorem pivot_mem_217 : (0, 0) ∈ envelope_217 := by decide
theorem children_work_217 : ∀ j, Template HasSnaky 6 (childrenC_217 j) (childrenD_217 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_111 1 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_55 4 (-4, 0)).mono (by decide)
  · exact (placed_template_map row_works_64 0 (-3, -1)).mono (by decide)
theorem row_works_217 : Template HasSnaky 7 required_217 envelope_217 := by
  refine compose HasSnaky 6 childrenC_217 childrenD_217 children_work_217 (0, 0)
    required_217 envelope_217 pivot_mem_217 child_required_sub_217 child_envelope_sub_217 ?_
  intro b hb; exact common_sub_217 (mem_commonEnvelope childrenD_217 b hb)
def required_220 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_220 : Finset Cell := ⟨(([(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_220 : Fin 5 → Finset Cell := ![(placedSet 4 (-4, 0) required_56), (placedSet 1 (1, -1) required_63), (placedSet 2 (1, 0) required_144), (placedSet 6 (1, 0) required_154), (placedSet 1 (1, 0) required_155)]
def childrenD_220 : Fin 5 → Finset Cell := ![(placedSet 4 (-4, 0) envelope_56), (placedSet 1 (1, -1) envelope_63), (placedSet 2 (1, 0) envelope_144), (placedSet 6 (1, 0) envelope_154), (placedSet 1 (1, 0) envelope_155)]
theorem common_sub_220 : commonEnvelope childrenD_220 ⊆ insert (0, 0) required_220 := by decide
theorem child_required_sub_220 : ∀ j, childrenC_220 j ⊆ insert (0, 0) required_220 := by decide
theorem child_envelope_sub_220 : ∀ j, childrenD_220 j ⊆ envelope_220 := by decide
theorem pivot_mem_220 : (0, 0) ∈ envelope_220 := by decide
theorem children_work_220 : ∀ j, Template HasSnaky 6 (childrenC_220 j) (childrenD_220 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_56 4 (-4, 0)).mono (by decide)
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_144 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_154 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_155 1 (1, 0)).mono (by decide)
theorem row_works_220 : Template HasSnaky 7 required_220 envelope_220 := by
  refine compose HasSnaky 6 childrenC_220 childrenD_220 children_work_220 (0, 0)
    required_220 envelope_220 pivot_mem_220 child_required_sub_220 child_envelope_sub_220 ?_
  intro b hb; exact common_sub_220 (mem_commonEnvelope childrenD_220 b hb)
end SnakyConditional

end OAI
