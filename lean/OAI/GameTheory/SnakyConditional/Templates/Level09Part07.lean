import OAI.GameTheory.SnakyConditional.Templates.Level07Part07
import OAI.GameTheory.SnakyConditional.Templates.Level08Part01
import OAI.GameTheory.SnakyConditional.Templates.Level08Part03
import OAI.GameTheory.SnakyConditional.Templates.Level08Part04
import OAI.GameTheory.SnakyConditional.Templates.Level08Part05
import OAI.GameTheory.SnakyConditional.Templates.Level08Part06

namespace OAI

namespace SnakyConditional
def required_275 : Finset Cell := ⟨(([(-3, -1), (-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_275 : Finset Cell := ⟨(([(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_275 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) required_63), (placedSet 4 (-4, 0) required_198), (placedSet 2 (1, 0) required_44)]
def childrenD_275 : Fin 3 → Finset Cell := ![(placedSet 1 (1, -1) envelope_63), (placedSet 4 (-4, 0) envelope_198), (placedSet 2 (1, 0) envelope_44)]
theorem common_sub_275 : commonEnvelope childrenD_275 ⊆ insert (0, 0) required_275 := by decide
theorem child_required_sub_275 : ∀ j, childrenC_275 j ⊆ insert (0, 0) required_275 := by decide
theorem child_envelope_sub_275 : ∀ j, childrenD_275 j ⊆ envelope_275 := by decide
theorem pivot_mem_275 : (0, 0) ∈ envelope_275 := by decide
theorem children_work_275 : ∀ j, Template HasSnaky 6 (childrenC_275 j) (childrenD_275 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 1 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_198 4 (-4, 0)).mono (by decide)
  · exact (placed_template_map row_works_44 2 (1, 0)).mono (by decide)
theorem row_works_275 : Template HasSnaky 7 required_275 envelope_275 := by
  refine compose HasSnaky 6 childrenC_275 childrenD_275 children_work_275 (0, 0)
    required_275 envelope_275 pivot_mem_275 child_required_sub_275 child_envelope_sub_275 ?_
  intro b hb; exact common_sub_275 (mem_commonEnvelope childrenD_275 b hb)
def required_276 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1), (3, -2), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_276 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_276 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) required_7), (placedSet 0 (1, 0) required_177), (placedSet 0 (-1, 1) required_63)]
def childrenD_276 : Fin 3 → Finset Cell := ![(placedSet 3 (-1, 0) envelope_7), (placedSet 0 (1, 0) envelope_177), (placedSet 0 (-1, 1) envelope_63)]
theorem common_sub_276 : commonEnvelope childrenD_276 ⊆ insert (0, 0) required_276 := by decide
theorem child_required_sub_276 : ∀ j, childrenC_276 j ⊆ insert (0, 0) required_276 := by decide
theorem child_envelope_sub_276 : ∀ j, childrenD_276 j ⊆ envelope_276 := by decide
theorem pivot_mem_276 : (0, 0) ∈ envelope_276 := by decide
theorem children_work_276 : ∀ j, Template HasSnaky 6 (childrenC_276 j) (childrenD_276 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_7 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_177 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
theorem row_works_276 : Template HasSnaky 7 required_276 envelope_276 := by
  refine compose HasSnaky 6 childrenC_276 childrenD_276 children_work_276 (0, 0)
    required_276 envelope_276 pivot_mem_276 child_required_sub_276 child_envelope_sub_276 ?_
  intro b hb; exact common_sub_276 (mem_commonEnvelope childrenD_276 b hb)
def required_278 : Finset Cell := ⟨(([(1, 0), (2, -1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_278 : Finset Cell := ⟨(([(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_278 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -1) required_63), (placedSet 1 (4, 0) required_162)]
def childrenD_278 : Fin 2 → Finset Cell := ![(placedSet 3 (-1, -1) envelope_63), (placedSet 1 (4, 0) envelope_162)]
theorem common_sub_278 : commonEnvelope childrenD_278 ⊆ insert (0, 0) required_278 := by decide
theorem child_required_sub_278 : ∀ j, childrenC_278 j ⊆ insert (0, 0) required_278 := by decide
theorem child_envelope_sub_278 : ∀ j, childrenD_278 j ⊆ envelope_278 := by decide
theorem pivot_mem_278 : (0, 0) ∈ envelope_278 := by decide
theorem children_work_278 : ∀ j, Template HasSnaky 6 (childrenC_278 j) (childrenD_278 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 3 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_162 1 (4, 0)).mono (by decide)
theorem row_works_278 : Template HasSnaky 7 required_278 envelope_278 := by
  refine compose HasSnaky 6 childrenC_278 childrenD_278 children_work_278 (0, 0)
    required_278 envelope_278 pivot_mem_278 child_required_sub_278 child_envelope_sub_278 ?_
  intro b hb; exact common_sub_278 (mem_commonEnvelope childrenD_278 b hb)
def required_281 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0), (-1, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_281 : Finset Cell := ⟨(([(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_281 : Fin 3 → Finset Cell := ![(placedSet 4 (1, 0) required_36), (placedSet 2 (1, 0) required_163), (placedSet 0 (0, 1) required_189)]
def childrenD_281 : Fin 3 → Finset Cell := ![(placedSet 4 (1, 0) envelope_36), (placedSet 2 (1, 0) envelope_163), (placedSet 0 (0, 1) envelope_189)]
theorem common_sub_281 : commonEnvelope childrenD_281 ⊆ insert (0, 0) required_281 := by decide
theorem child_required_sub_281 : ∀ j, childrenC_281 j ⊆ insert (0, 0) required_281 := by decide
theorem child_envelope_sub_281 : ∀ j, childrenD_281 j ⊆ envelope_281 := by decide
theorem pivot_mem_281 : (0, 0) ∈ envelope_281 := by decide
theorem children_work_281 : ∀ j, Template HasSnaky 6 (childrenC_281 j) (childrenD_281 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_36 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_163 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_189 0 (0, 1)).mono (by decide)
theorem row_works_281 : Template HasSnaky 7 required_281 envelope_281 := by
  refine compose HasSnaky 6 childrenC_281 childrenD_281 children_work_281 (0, 0)
    required_281 envelope_281 pivot_mem_281 child_required_sub_281 child_envelope_sub_281 ?_
  intro b hb; exact common_sub_281 (mem_commonEnvelope childrenD_281 b hb)
def required_288 : Finset Cell := ⟨(([(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_288 : Finset Cell := ⟨(([(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_288 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -2) required_130), (placedSet 0 (-3, 0) required_96)]
def childrenD_288 : Fin 2 → Finset Cell := ![(placedSet 1 (0, -2) envelope_130), (placedSet 0 (-3, 0) envelope_96)]
theorem common_sub_288 : commonEnvelope childrenD_288 ⊆ insert (0, 0) required_288 := by decide
theorem child_required_sub_288 : ∀ j, childrenC_288 j ⊆ insert (0, 0) required_288 := by decide
theorem child_envelope_sub_288 : ∀ j, childrenD_288 j ⊆ envelope_288 := by decide
theorem pivot_mem_288 : (0, 0) ∈ envelope_288 := by decide
theorem children_work_288 : ∀ j, Template HasSnaky 6 (childrenC_288 j) (childrenD_288 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_130 1 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_96 0 (-3, 0)).mono (by decide)
theorem row_works_288 : Template HasSnaky 7 required_288 envelope_288 := by
  refine compose HasSnaky 6 childrenC_288 childrenD_288 children_work_288 (0, 0)
    required_288 envelope_288 pivot_mem_288 child_required_sub_288 child_envelope_sub_288 ?_
  intro b hb; exact common_sub_288 (mem_commonEnvelope childrenD_288 b hb)
def required_296 : Finset Cell := ⟨(([(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-1, -2), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_296 : Finset Cell := ⟨(([(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_296 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) required_107), (placedSet 3 (-1, 0) required_209), (placedSet 1 (0, 1) required_65)]
def childrenD_296 : Fin 3 → Finset Cell := ![(placedSet 1 (0, 1) envelope_107), (placedSet 3 (-1, 0) envelope_209), (placedSet 1 (0, 1) envelope_65)]
theorem common_sub_296 : commonEnvelope childrenD_296 ⊆ insert (0, 0) required_296 := by decide
theorem child_required_sub_296 : ∀ j, childrenC_296 j ⊆ insert (0, 0) required_296 := by decide
theorem child_envelope_sub_296 : ∀ j, childrenD_296 j ⊆ envelope_296 := by decide
theorem pivot_mem_296 : (0, 0) ∈ envelope_296 := by decide
theorem children_work_296 : ∀ j, Template HasSnaky 6 (childrenC_296 j) (childrenD_296 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_107 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_209 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_65 1 (0, 1)).mono (by decide)
theorem row_works_296 : Template HasSnaky 7 required_296 envelope_296 := by
  refine compose HasSnaky 6 childrenC_296 childrenD_296 children_work_296 (0, 0)
    required_296 envelope_296 pivot_mem_296 child_required_sub_296 child_envelope_sub_296 ?_
  intro b hb; exact common_sub_296 (mem_commonEnvelope childrenD_296 b hb)
end SnakyConditional

end OAI
