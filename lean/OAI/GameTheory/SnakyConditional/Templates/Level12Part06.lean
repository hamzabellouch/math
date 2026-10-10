import OAI.GameTheory.SnakyConditional.Templates.Level07Part08
import OAI.GameTheory.SnakyConditional.Templates.Level11Part03
import OAI.GameTheory.SnakyConditional.Templates.Level11Part04
import OAI.GameTheory.SnakyConditional.Templates.Level11Part05
import OAI.GameTheory.SnakyConditional.Templates.Level11Part06

namespace OAI

namespace SnakyConditional
def required_360 : Finset Cell := ⟨(([(-2, -2), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_360 : Finset Cell := ⟨(([(-3, -1), (-2, -2), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_360 : Fin 4 → Finset Cell := ![(placedSet 4 (0, 1) required_155), (placedSet 3 (-1, 0) required_7), (placedSet 0 (1, -2) required_337), (placedSet 4 (1, -2) required_228)]
def childrenD_360 : Fin 4 → Finset Cell := ![(placedSet 4 (0, 1) envelope_155), (placedSet 3 (-1, 0) envelope_7), (placedSet 0 (1, -2) envelope_337), (placedSet 4 (1, -2) envelope_228)]
theorem common_sub_360 : commonEnvelope childrenD_360 ⊆ insert (0, 0) required_360 := by decide
theorem child_required_sub_360 : ∀ j, childrenC_360 j ⊆ insert (0, 0) required_360 := by decide
theorem child_envelope_sub_360 : ∀ j, childrenD_360 j ⊆ envelope_360 := by decide
theorem pivot_mem_360 : (0, 0) ∈ envelope_360 := by decide
theorem children_work_360 : ∀ j, Template HasSnaky 9 (childrenC_360 j) (childrenD_360 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_155 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_337 0 (1, -2)).mono (by decide)
  · exact (placed_template_map row_works_228 4 (1, -2)).mono (by decide)
theorem row_works_360 : Template HasSnaky 10 required_360 envelope_360 := by
  refine compose HasSnaky 9 childrenC_360 childrenD_360 children_work_360 (0, 0)
    required_360 envelope_360 pivot_mem_360 child_required_sub_360 child_envelope_sub_360 ?_
  intro b hb; exact common_sub_360 (mem_commonEnvelope childrenD_360 b hb)
def required_364 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_364 : Finset Cell := ⟨(([(-4, -4), (-4, -2), (-3, -4), (-3, -3), (-3, -2), (-2, -4), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_364 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 1) required_63), (placedSet 2 (-1, -3) required_314)]
def childrenD_364 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 1) envelope_63), (placedSet 2 (-1, -3) envelope_314)]
theorem common_sub_364 : commonEnvelope childrenD_364 ⊆ insert (0, 0) required_364 := by decide
theorem child_required_sub_364 : ∀ j, childrenC_364 j ⊆ insert (0, 0) required_364 := by decide
theorem child_envelope_sub_364 : ∀ j, childrenD_364 j ⊆ envelope_364 := by decide
theorem pivot_mem_364 : (0, 0) ∈ envelope_364 := by decide
theorem children_work_364 : ∀ j, Template HasSnaky 9 (childrenC_364 j) (childrenD_364 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_314 2 (-1, -3)).mono (by decide)
theorem row_works_364 : Template HasSnaky 10 required_364 envelope_364 := by
  refine compose HasSnaky 9 childrenC_364 childrenD_364 children_work_364 (0, 0)
    required_364 envelope_364 pivot_mem_364 child_required_sub_364 child_envelope_sub_364 ?_
  intro b hb; exact common_sub_364 (mem_commonEnvelope childrenD_364 b hb)
def required_374 : Finset Cell := ⟨(([(1, -2), (1, 0), (2, -1), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_374 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_374 : Fin 4 → Finset Cell := ![(placedSet 4 (-1, 0) required_65), (placedSet 0 (3, 0) required_335), (placedSet 2 (3, -1) required_24), (placedSet 4 (-1, 0) required_163)]
def childrenD_374 : Fin 4 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_65), (placedSet 0 (3, 0) envelope_335), (placedSet 2 (3, -1) envelope_24), (placedSet 4 (-1, 0) envelope_163)]
theorem common_sub_374 : commonEnvelope childrenD_374 ⊆ insert (0, 0) required_374 := by decide
theorem child_required_sub_374 : ∀ j, childrenC_374 j ⊆ insert (0, 0) required_374 := by decide
theorem child_envelope_sub_374 : ∀ j, childrenD_374 j ⊆ envelope_374 := by decide
theorem pivot_mem_374 : (0, 0) ∈ envelope_374 := by decide
theorem children_work_374 : ∀ j, Template HasSnaky 9 (childrenC_374 j) (childrenD_374 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_65 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_335 0 (3, 0)).mono (by decide)
  · exact (placed_template_map row_works_24 2 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_163 4 (-1, 0)).mono (by decide)
theorem row_works_374 : Template HasSnaky 10 required_374 envelope_374 := by
  refine compose HasSnaky 9 childrenC_374 childrenD_374 children_work_374 (0, 0)
    required_374 envelope_374 pivot_mem_374 child_required_sub_374 child_envelope_sub_374 ?_
  intro b hb; exact common_sub_374 (mem_commonEnvelope childrenD_374 b hb)
def required_376 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_376 : Finset Cell := ⟨(([(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_376 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) required_162), (placedSet 3 (-3, -1) required_285)]
def childrenD_376 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 0) envelope_162), (placedSet 3 (-3, -1) envelope_285)]
theorem common_sub_376 : commonEnvelope childrenD_376 ⊆ insert (0, 0) required_376 := by decide
theorem child_required_sub_376 : ∀ j, childrenC_376 j ⊆ insert (0, 0) required_376 := by decide
theorem child_envelope_sub_376 : ∀ j, childrenD_376 j ⊆ envelope_376 := by decide
theorem pivot_mem_376 : (0, 0) ∈ envelope_376 := by decide
theorem children_work_376 : ∀ j, Template HasSnaky 9 (childrenC_376 j) (childrenD_376 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_162 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_285 3 (-3, -1)).mono (by decide)
theorem row_works_376 : Template HasSnaky 10 required_376 envelope_376 := by
  refine compose HasSnaky 9 childrenC_376 childrenD_376 children_work_376 (0, 0)
    required_376 envelope_376 pivot_mem_376 child_required_sub_376 child_envelope_sub_376 ?_
  intro b hb; exact common_sub_376 (mem_commonEnvelope childrenD_376 b hb)
def required_381 : Finset Cell := ⟨(([(1, 0), (2, -1), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_381 : Finset Cell := ⟨(([(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_381 : Fin 4 → Finset Cell := ![(placedSet 6 (-1, 0) required_211), (placedSet 0 (3, 1) required_24), (placedSet 4 (-1, 0) required_163), (placedSet 0 (3, 0) required_341)]
def childrenD_381 : Fin 4 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_211), (placedSet 0 (3, 1) envelope_24), (placedSet 4 (-1, 0) envelope_163), (placedSet 0 (3, 0) envelope_341)]
theorem common_sub_381 : commonEnvelope childrenD_381 ⊆ insert (0, 0) required_381 := by decide
theorem child_required_sub_381 : ∀ j, childrenC_381 j ⊆ insert (0, 0) required_381 := by decide
theorem child_envelope_sub_381 : ∀ j, childrenD_381 j ⊆ envelope_381 := by decide
theorem pivot_mem_381 : (0, 0) ∈ envelope_381 := by decide
theorem children_work_381 : ∀ j, Template HasSnaky 9 (childrenC_381 j) (childrenD_381 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_211 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_24 0 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_163 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_341 0 (3, 0)).mono (by decide)
theorem row_works_381 : Template HasSnaky 10 required_381 envelope_381 := by
  refine compose HasSnaky 9 childrenC_381 childrenD_381 children_work_381 (0, 0)
    required_381 envelope_381 pivot_mem_381 child_required_sub_381 child_envelope_sub_381 ?_
  intro b hb; exact common_sub_381 (mem_commonEnvelope childrenD_381 b hb)
end SnakyConditional

end OAI
