import OAI.GameTheory.SnakyConditional.Templates.Level11Part02
import OAI.GameTheory.SnakyConditional.Templates.Level11Part03
import OAI.GameTheory.SnakyConditional.Templates.Level11Part04
import OAI.GameTheory.SnakyConditional.Templates.Level11Part06
import OAI.GameTheory.SnakyConditional.Templates.Level11Part07

namespace OAI

namespace SnakyConditional
def required_386 : Finset Cell := ⟨(([(-2, 0), (-1, -2), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_386 : Finset Cell := ⟨(([(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_386 : Fin 6 → Finset Cell := ![(placedSet 4 (-3, 0) required_217), (placedSet 0 (1, 0) required_172), (placedSet 4 (-3, 0) required_173), (placedSet 0 (1, 0) required_217), (placedSet 0 (1, 0) required_294), (placedSet 4 (-3, 0) required_294)]
def childrenD_386 : Fin 6 → Finset Cell := ![(placedSet 4 (-3, 0) envelope_217), (placedSet 0 (1, 0) envelope_172), (placedSet 4 (-3, 0) envelope_173), (placedSet 0 (1, 0) envelope_217), (placedSet 0 (1, 0) envelope_294), (placedSet 4 (-3, 0) envelope_294)]
theorem common_sub_386 : commonEnvelope childrenD_386 ⊆ insert (0, 0) required_386 := by decide
theorem child_required_sub_386 : ∀ j, childrenC_386 j ⊆ insert (0, 0) required_386 := by decide
theorem child_envelope_sub_386 : ∀ j, childrenD_386 j ⊆ envelope_386 := by decide
theorem pivot_mem_386 : (0, 0) ∈ envelope_386 := by decide
theorem children_work_386 : ∀ j, Template HasSnaky 9 (childrenC_386 j) (childrenD_386 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_217 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_172 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_173 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_217 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_294 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_294 4 (-3, 0)).mono (by decide)
theorem row_works_386 : Template HasSnaky 10 required_386 envelope_386 := by
  refine compose HasSnaky 9 childrenC_386 childrenD_386 children_work_386 (0, 0)
    required_386 envelope_386 pivot_mem_386 child_required_sub_386 child_envelope_sub_386 ?_
  intro b hb; exact common_sub_386 (mem_commonEnvelope childrenD_386 b hb)
def required_398 : Finset Cell := ⟨(([(-3, -4), (-3, -3), (-3, -2), (-2, -3), (-2, 0), (-1, -3), (0, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_398 : Finset Cell := ⟨(([(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_398 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, -1) required_257), (placedSet 0 (1, 0) required_363), (placedSet 1 (0, -2) required_130), (placedSet 1 (0, -2) required_177)]
def childrenD_398 : Fin 4 → Finset Cell := ![(placedSet 0 (-3, -1) envelope_257), (placedSet 0 (1, 0) envelope_363), (placedSet 1 (0, -2) envelope_130), (placedSet 1 (0, -2) envelope_177)]
theorem common_sub_398 : commonEnvelope childrenD_398 ⊆ insert (0, 0) required_398 := by decide
theorem child_required_sub_398 : ∀ j, childrenC_398 j ⊆ insert (0, 0) required_398 := by decide
theorem child_envelope_sub_398 : ∀ j, childrenD_398 j ⊆ envelope_398 := by decide
theorem pivot_mem_398 : (0, 0) ∈ envelope_398 := by decide
theorem children_work_398 : ∀ j, Template HasSnaky 9 (childrenC_398 j) (childrenD_398 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_257 0 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_363 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_130 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_177 1 (0, -2)).mono (by decide)
theorem row_works_398 : Template HasSnaky 10 required_398 envelope_398 := by
  refine compose HasSnaky 9 childrenC_398 childrenD_398 children_work_398 (0, 0)
    required_398 envelope_398 pivot_mem_398 child_required_sub_398 child_envelope_sub_398 ?_
  intro b hb; exact common_sub_398 (mem_commonEnvelope childrenD_398 b hb)
def required_400 : Finset Cell := ⟨(([(-1, -2), (-1, 0), (1, -2), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_400 : Finset Cell := ⟨(([(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_400 : Fin 6 → Finset Cell := ![(placedSet 4 (-2, 0) required_283), (placedSet 4 (-2, 0) required_252), (placedSet 4 (-2, 0) required_176), (placedSet 0 (2, 0) required_197), (placedSet 0 (2, 0) required_283), (placedSet 4 (-2, 0) required_245)]
def childrenD_400 : Fin 6 → Finset Cell := ![(placedSet 4 (-2, 0) envelope_283), (placedSet 4 (-2, 0) envelope_252), (placedSet 4 (-2, 0) envelope_176), (placedSet 0 (2, 0) envelope_197), (placedSet 0 (2, 0) envelope_283), (placedSet 4 (-2, 0) envelope_245)]
theorem common_sub_400 : commonEnvelope childrenD_400 ⊆ insert (0, 0) required_400 := by decide
theorem child_required_sub_400 : ∀ j, childrenC_400 j ⊆ insert (0, 0) required_400 := by decide
theorem child_envelope_sub_400 : ∀ j, childrenD_400 j ⊆ envelope_400 := by decide
theorem pivot_mem_400 : (0, 0) ∈ envelope_400 := by decide
theorem children_work_400 : ∀ j, Template HasSnaky 9 (childrenC_400 j) (childrenD_400 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_283 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_252 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_176 4 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_197 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_283 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_245 4 (-2, 0)).mono (by decide)
theorem row_works_400 : Template HasSnaky 10 required_400 envelope_400 := by
  refine compose HasSnaky 9 childrenC_400 childrenD_400 children_work_400 (0, 0)
    required_400 envelope_400 pivot_mem_400 child_required_sub_400 child_envelope_sub_400 ?_
  intro b hb; exact common_sub_400 (mem_commonEnvelope childrenD_400 b hb)
def required_407 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_407 : Finset Cell := ⟨(([(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_407 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 3) required_285), (placedSet 6 (1, 0) required_314)]
def childrenD_407 : Fin 2 → Finset Cell := ![(placedSet 0 (-1, 3) envelope_285), (placedSet 6 (1, 0) envelope_314)]
theorem common_sub_407 : commonEnvelope childrenD_407 ⊆ insert (0, 0) required_407 := by decide
theorem child_required_sub_407 : ∀ j, childrenC_407 j ⊆ insert (0, 0) required_407 := by decide
theorem child_envelope_sub_407 : ∀ j, childrenD_407 j ⊆ envelope_407 := by decide
theorem pivot_mem_407 : (0, 0) ∈ envelope_407 := by decide
theorem children_work_407 : ∀ j, Template HasSnaky 9 (childrenC_407 j) (childrenD_407 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_285 0 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_314 6 (1, 0)).mono (by decide)
theorem row_works_407 : Template HasSnaky 10 required_407 envelope_407 := by
  refine compose HasSnaky 9 childrenC_407 childrenD_407 children_work_407 (0, 0)
    required_407 envelope_407 pivot_mem_407 child_required_sub_407 child_envelope_sub_407 ?_
  intro b hb; exact common_sub_407 (mem_commonEnvelope childrenD_407 b hb)
def required_424 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_424 : Finset Cell := ⟨(([(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_424 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) required_55), (placedSet 0 (2, 0) required_394), (placedSet 3 (0, 1) required_216)]
def childrenD_424 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) envelope_55), (placedSet 0 (2, 0) envelope_394), (placedSet 3 (0, 1) envelope_216)]
theorem common_sub_424 : commonEnvelope childrenD_424 ⊆ insert (0, 0) required_424 := by decide
theorem child_required_sub_424 : ∀ j, childrenC_424 j ⊆ insert (0, 0) required_424 := by decide
theorem child_envelope_sub_424 : ∀ j, childrenD_424 j ⊆ envelope_424 := by decide
theorem pivot_mem_424 : (0, 0) ∈ envelope_424 := by decide
theorem children_work_424 : ∀ j, Template HasSnaky 9 (childrenC_424 j) (childrenD_424 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_394 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_216 3 (0, 1)).mono (by decide)
theorem row_works_424 : Template HasSnaky 10 required_424 envelope_424 := by
  refine compose HasSnaky 9 childrenC_424 childrenD_424 children_work_424 (0, 0)
    required_424 envelope_424 pivot_mem_424 child_required_sub_424 child_envelope_sub_424 ?_
  intro b hb; exact common_sub_424 (mem_commonEnvelope childrenD_424 b hb)
end SnakyConditional

end OAI
