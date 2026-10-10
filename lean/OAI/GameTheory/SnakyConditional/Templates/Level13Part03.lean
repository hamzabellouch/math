import OAI.GameTheory.SnakyConditional.Templates.Level12Part01
import OAI.GameTheory.SnakyConditional.Templates.Level12Part03
import OAI.GameTheory.SnakyConditional.Templates.Level12Part04
import OAI.GameTheory.SnakyConditional.Templates.Level12Part06

namespace OAI

namespace SnakyConditional
def required_370 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_370 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_370 : Fin 4 → Finset Cell := ![(placedSet 3 (-3, 0) required_199), (placedSet 1 (1, 0) required_286), (placedSet 6 (-3, -1) required_24), (placedSet 0 (1, -1) required_319)]
def childrenD_370 : Fin 4 → Finset Cell := ![(placedSet 3 (-3, 0) envelope_199), (placedSet 1 (1, 0) envelope_286), (placedSet 6 (-3, -1) envelope_24), (placedSet 0 (1, -1) envelope_319)]
theorem common_sub_370 : commonEnvelope childrenD_370 ⊆ insert (0, 0) required_370 := by decide
theorem child_required_sub_370 : ∀ j, childrenC_370 j ⊆ insert (0, 0) required_370 := by decide
theorem child_envelope_sub_370 : ∀ j, childrenD_370 j ⊆ envelope_370 := by decide
theorem pivot_mem_370 : (0, 0) ∈ envelope_370 := by decide
theorem children_work_370 : ∀ j, Template HasSnaky 10 (childrenC_370 j) (childrenD_370 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_199 3 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_286 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_24 6 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_319 0 (1, -1)).mono (by decide)
theorem row_works_370 : Template HasSnaky 11 required_370 envelope_370 := by
  refine compose HasSnaky 10 childrenC_370 childrenD_370 children_work_370 (0, 0)
    required_370 envelope_370 pivot_mem_370 child_required_sub_370 child_envelope_sub_370 ?_
  intro b hb; exact common_sub_370 (mem_commonEnvelope childrenD_370 b hb)
def required_372 : Finset Cell := ⟨(([(-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_372 : Finset Cell := ⟨(([(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_372 : Fin 4 → Finset Cell := ![(placedSet 1 (0, -1) required_40), (placedSet 0 (-2, 0) required_333), (placedSet 1 (-1, -1) required_120), (placedSet 0 (0, -2) required_161)]
def childrenD_372 : Fin 4 → Finset Cell := ![(placedSet 1 (0, -1) envelope_40), (placedSet 0 (-2, 0) envelope_333), (placedSet 1 (-1, -1) envelope_120), (placedSet 0 (0, -2) envelope_161)]
theorem common_sub_372 : commonEnvelope childrenD_372 ⊆ insert (0, 0) required_372 := by decide
theorem child_required_sub_372 : ∀ j, childrenC_372 j ⊆ insert (0, 0) required_372 := by decide
theorem child_envelope_sub_372 : ∀ j, childrenD_372 j ⊆ envelope_372 := by decide
theorem pivot_mem_372 : (0, 0) ∈ envelope_372 := by decide
theorem children_work_372 : ∀ j, Template HasSnaky 10 (childrenC_372 j) (childrenD_372 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_40 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_333 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_120 1 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_161 0 (0, -2)).mono (by decide)
theorem row_works_372 : Template HasSnaky 11 required_372 envelope_372 := by
  refine compose HasSnaky 10 childrenC_372 childrenD_372 children_work_372 (0, 0)
    required_372 envelope_372 pivot_mem_372 child_required_sub_372 child_envelope_sub_372 ?_
  intro b hb; exact common_sub_372 (mem_commonEnvelope childrenD_372 b hb)
def required_378 : Finset Cell := ⟨(([(-2, 0), (-1, -2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_378 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_378 : Fin 5 → Finset Cell := ![(placedSet 0 (1, 0) required_295), (placedSet 4 (-3, 0) required_176), (placedSet 4 (-3, 0) required_183), (placedSet 6 (-3, 0) required_172), (placedSet 4 (-3, 0) required_294)]
def childrenD_378 : Fin 5 → Finset Cell := ![(placedSet 0 (1, 0) envelope_295), (placedSet 4 (-3, 0) envelope_176), (placedSet 4 (-3, 0) envelope_183), (placedSet 6 (-3, 0) envelope_172), (placedSet 4 (-3, 0) envelope_294)]
theorem common_sub_378 : commonEnvelope childrenD_378 ⊆ insert (0, 0) required_378 := by decide
theorem child_required_sub_378 : ∀ j, childrenC_378 j ⊆ insert (0, 0) required_378 := by decide
theorem child_envelope_sub_378 : ∀ j, childrenD_378 j ⊆ envelope_378 := by decide
theorem pivot_mem_378 : (0, 0) ∈ envelope_378 := by decide
theorem children_work_378 : ∀ j, Template HasSnaky 10 (childrenC_378 j) (childrenD_378 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_295 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_176 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_183 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_172 6 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_294 4 (-3, 0)).mono (by decide)
theorem row_works_378 : Template HasSnaky 11 required_378 envelope_378 := by
  refine compose HasSnaky 10 childrenC_378 childrenD_378 children_work_378 (0, 0)
    required_378 envelope_378 pivot_mem_378 child_required_sub_378 child_envelope_sub_378 ?_
  intro b hb; exact common_sub_378 (mem_commonEnvelope childrenD_378 b hb)
def required_384 : Finset Cell := ⟨(([(-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_384 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_384 : Fin 7 → Finset Cell := ![(placedSet 2 (2, 0) required_173), (placedSet 4 (-2, 0) required_282), (placedSet 2 (2, 0) required_220), (placedSet 2 (2, 0) required_246), (placedSet 2 (2, 0) required_263), (placedSet 6 (-2, 0) required_183), (placedSet 0 (2, 0) required_295)]
def childrenD_384 : Fin 7 → Finset Cell := ![(placedSet 2 (2, 0) envelope_173), (placedSet 4 (-2, 0) envelope_282), (placedSet 2 (2, 0) envelope_220), (placedSet 2 (2, 0) envelope_246), (placedSet 2 (2, 0) envelope_263), (placedSet 6 (-2, 0) envelope_183), (placedSet 0 (2, 0) envelope_295)]
theorem common_sub_384 : commonEnvelope childrenD_384 ⊆ insert (0, 0) required_384 := by decide
theorem child_required_sub_384 : ∀ j, childrenC_384 j ⊆ insert (0, 0) required_384 := by decide
theorem child_envelope_sub_384 : ∀ j, childrenD_384 j ⊆ envelope_384 := by decide
theorem pivot_mem_384 : (0, 0) ∈ envelope_384 := by decide
theorem children_work_384 : ∀ j, Template HasSnaky 10 (childrenC_384 j) (childrenD_384 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_173 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_282 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_220 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_246 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_263 2 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_183 6 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_295 0 (2, 0)).mono (by decide)
theorem row_works_384 : Template HasSnaky 11 required_384 envelope_384 := by
  refine compose HasSnaky 10 childrenC_384 childrenD_384 children_work_384 (0, 0)
    required_384 envelope_384 pivot_mem_384 child_required_sub_384 child_envelope_sub_384 ?_
  intro b hb; exact common_sub_384 (mem_commonEnvelope childrenD_384 b hb)
def required_388 : Finset Cell := ⟨(([(0, -2), (1, -3), (1, -2), (1, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_388 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_388 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (-1, 0) required_374)]
def childrenD_388 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (-1, 0) envelope_374)]
theorem common_sub_388 : commonEnvelope childrenD_388 ⊆ insert (0, 0) required_388 := by decide
theorem child_required_sub_388 : ∀ j, childrenC_388 j ⊆ insert (0, 0) required_388 := by decide
theorem child_envelope_sub_388 : ∀ j, childrenD_388 j ⊆ envelope_388 := by decide
theorem pivot_mem_388 : (0, 0) ∈ envelope_388 := by decide
theorem children_work_388 : ∀ j, Template HasSnaky 10 (childrenC_388 j) (childrenD_388 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_374 0 (-1, 0)).mono (by decide)
theorem row_works_388 : Template HasSnaky 11 required_388 envelope_388 := by
  refine compose HasSnaky 10 childrenC_388 childrenD_388 children_work_388 (0, 0)
    required_388 envelope_388 pivot_mem_388 child_required_sub_388 child_envelope_sub_388 ?_
  intro b hb; exact common_sub_388 (mem_commonEnvelope childrenD_388 b hb)
end SnakyConditional

end OAI
