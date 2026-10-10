import OAI.GameTheory.SnakyConditional.Templates.Level10Part01
import OAI.GameTheory.SnakyConditional.Templates.Level10Part02
import OAI.GameTheory.SnakyConditional.Templates.Level10Part05

namespace OAI

namespace SnakyConditional
def required_324 : Finset Cell := ⟨(([(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_324 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_324 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (-1, 0) required_298)]
def childrenD_324 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (-1, 0) envelope_298)]
theorem common_sub_324 : commonEnvelope childrenD_324 ⊆ insert (0, 0) required_324 := by decide
theorem child_required_sub_324 : ∀ j, childrenC_324 j ⊆ insert (0, 0) required_324 := by decide
theorem child_envelope_sub_324 : ∀ j, childrenD_324 j ⊆ envelope_324 := by decide
theorem pivot_mem_324 : (0, 0) ∈ envelope_324 := by decide
theorem children_work_324 : ∀ j, Template HasSnaky 8 (childrenC_324 j) (childrenD_324 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_298 0 (-1, 0)).mono (by decide)
theorem row_works_324 : Template HasSnaky 9 required_324 envelope_324 := by
  refine compose HasSnaky 8 childrenC_324 childrenD_324 children_work_324 (0, 0)
    required_324 envelope_324 pivot_mem_324 child_required_sub_324 child_envelope_sub_324 ?_
  intro b hb; exact common_sub_324 (mem_commonEnvelope childrenD_324 b hb)
def required_329 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_329 : Finset Cell := ⟨(([(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_329 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) required_0), (placedSet 0 (1, 1) required_305)]
def childrenD_329 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) envelope_0), (placedSet 0 (1, 1) envelope_305)]
theorem common_sub_329 : commonEnvelope childrenD_329 ⊆ insert (0, 0) required_329 := by decide
theorem child_required_sub_329 : ∀ j, childrenC_329 j ⊆ insert (0, 0) required_329 := by decide
theorem child_envelope_sub_329 : ∀ j, childrenD_329 j ⊆ envelope_329 := by decide
theorem pivot_mem_329 : (0, 0) ∈ envelope_329 := by decide
theorem children_work_329 : ∀ j, Template HasSnaky 8 (childrenC_329 j) (childrenD_329 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_305 0 (1, 1)).mono (by decide)
theorem row_works_329 : Template HasSnaky 9 required_329 envelope_329 := by
  refine compose HasSnaky 8 childrenC_329 childrenD_329 children_work_329 (0, 0)
    required_329 envelope_329 pivot_mem_329 child_required_sub_329 child_envelope_sub_329 ?_
  intro b hb; exact common_sub_329 (mem_commonEnvelope childrenD_329 b hb)
def required_331 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_331 : Finset Cell := ⟨(([(-7, 0), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_331 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, 0) required_113), (placedSet 0 (-1, 0) required_15), (placedSet 4 (0, 1) required_298), (placedSet 2 (1, 0) required_90)]
def childrenD_331 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, 0) envelope_113), (placedSet 0 (-1, 0) envelope_15), (placedSet 4 (0, 1) envelope_298), (placedSet 2 (1, 0) envelope_90)]
theorem common_sub_331 : commonEnvelope childrenD_331 ⊆ insert (0, 0) required_331 := by decide
theorem child_required_sub_331 : ∀ j, childrenC_331 j ⊆ insert (0, 0) required_331 := by decide
theorem child_envelope_sub_331 : ∀ j, childrenD_331 j ⊆ envelope_331 := by decide
theorem pivot_mem_331 : (0, 0) ∈ envelope_331 := by decide
theorem children_work_331 : ∀ j, Template HasSnaky 8 (childrenC_331 j) (childrenD_331 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_113 0 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_15 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_298 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_90 2 (1, 0)).mono (by decide)
theorem row_works_331 : Template HasSnaky 9 required_331 envelope_331 := by
  refine compose HasSnaky 8 childrenC_331 childrenD_331 children_work_331 (0, 0)
    required_331 envelope_331 pivot_mem_331 child_required_sub_331 child_envelope_sub_331 ?_
  intro b hb; exact common_sub_331 (mem_commonEnvelope childrenD_331 b hb)
def required_335 : Finset Cell := ⟨(([(-3, 0), (-2, -2), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_335 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_335 : Fin 2 → Finset Cell := ![(placedSet 3 (-3, -1) required_196), (placedSet 1 (1, 0) required_162)]
def childrenD_335 : Fin 2 → Finset Cell := ![(placedSet 3 (-3, -1) envelope_196), (placedSet 1 (1, 0) envelope_162)]
theorem common_sub_335 : commonEnvelope childrenD_335 ⊆ insert (0, 0) required_335 := by decide
theorem child_required_sub_335 : ∀ j, childrenC_335 j ⊆ insert (0, 0) required_335 := by decide
theorem child_envelope_sub_335 : ∀ j, childrenD_335 j ⊆ envelope_335 := by decide
theorem pivot_mem_335 : (0, 0) ∈ envelope_335 := by decide
theorem children_work_335 : ∀ j, Template HasSnaky 8 (childrenC_335 j) (childrenD_335 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_196 3 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_162 1 (1, 0)).mono (by decide)
theorem row_works_335 : Template HasSnaky 9 required_335 envelope_335 := by
  refine compose HasSnaky 8 childrenC_335 childrenD_335 children_work_335 (0, 0)
    required_335 envelope_335 pivot_mem_335 child_required_sub_335 child_envelope_sub_335 ?_
  intro b hb; exact common_sub_335 (mem_commonEnvelope childrenD_335 b hb)
def required_336 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_336 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_336 : Fin 4 → Finset Cell := ![(placedSet 6 (-2, -1) required_25), (placedSet 3 (-2, 0) required_199), (placedSet 0 (2, 0) required_65), (placedSet 0 (-2, 0) required_304)]
def childrenD_336 : Fin 4 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_25), (placedSet 3 (-2, 0) envelope_199), (placedSet 0 (2, 0) envelope_65), (placedSet 0 (-2, 0) envelope_304)]
theorem common_sub_336 : commonEnvelope childrenD_336 ⊆ insert (0, 0) required_336 := by decide
theorem child_required_sub_336 : ∀ j, childrenC_336 j ⊆ insert (0, 0) required_336 := by decide
theorem child_envelope_sub_336 : ∀ j, childrenD_336 j ⊆ envelope_336 := by decide
theorem pivot_mem_336 : (0, 0) ∈ envelope_336 := by decide
theorem children_work_336 : ∀ j, Template HasSnaky 8 (childrenC_336 j) (childrenD_336 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_25 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_199 3 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_65 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_304 0 (-2, 0)).mono (by decide)
theorem row_works_336 : Template HasSnaky 9 required_336 envelope_336 := by
  refine compose HasSnaky 8 childrenC_336 childrenD_336 children_work_336 (0, 0)
    required_336 envelope_336 pivot_mem_336 child_required_sub_336 child_envelope_sub_336 ?_
  intro b hb; exact common_sub_336 (mem_commonEnvelope childrenD_336 b hb)
def required_337 : Finset Cell := ⟨(([(-3, 0), (-1, 0), (-1, 1), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_337 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_337 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 3) required_107), (placedSet 2 (-3, 1) required_230)]
def childrenD_337 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, 3) envelope_107), (placedSet 2 (-3, 1) envelope_230)]
theorem common_sub_337 : commonEnvelope childrenD_337 ⊆ insert (0, 0) required_337 := by decide
theorem child_required_sub_337 : ∀ j, childrenC_337 j ⊆ insert (0, 0) required_337 := by decide
theorem child_envelope_sub_337 : ∀ j, childrenD_337 j ⊆ envelope_337 := by decide
theorem pivot_mem_337 : (0, 0) ∈ envelope_337 := by decide
theorem children_work_337 : ∀ j, Template HasSnaky 8 (childrenC_337 j) (childrenD_337 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_107 3 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_230 2 (-3, 1)).mono (by decide)
theorem row_works_337 : Template HasSnaky 9 required_337 envelope_337 := by
  refine compose HasSnaky 8 childrenC_337 childrenD_337 children_work_337 (0, 0)
    required_337 envelope_337 pivot_mem_337 child_required_sub_337 child_envelope_sub_337 ?_
  intro b hb; exact common_sub_337 (mem_commonEnvelope childrenD_337 b hb)
end SnakyConditional

end OAI
