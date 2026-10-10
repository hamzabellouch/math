import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_149 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_149 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_149 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), required_124]
def childrenD_149 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), envelope_124]
theorem common_sub_149 : commonEnvelope childrenD_149 ⊆ insert (1, 3) required_149 := by decide +kernel
theorem child_required_sub_149 : ∀ j, childrenC_149 j ⊆ insert (1, 3) required_149 := by decide +kernel
theorem child_envelope_sub_149 : ∀ j, childrenD_149 j ⊆ envelope_149 := by decide +kernel
theorem pivot_mem_149 : (1, 3) ∈ envelope_149 := by decide +kernel
theorem children_work_149 : ∀ j, Template HasSnaky 3 (childrenC_149 j) (childrenD_149 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact row_works_124.mono (by decide +kernel)
theorem row_works_149 : Template HasSnaky 4 required_149 envelope_149 := by
  refine compose HasSnaky 3 childrenC_149 childrenD_149 children_work_149 (1, 3)
    required_149 envelope_149 pivot_mem_149 child_required_sub_149 child_envelope_sub_149 ?_
  intro b hb
  exact common_sub_149 (mem_commonEnvelope childrenD_149 b hb)
def required_150 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_150 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_150 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 0 (1, 0) required_7)]
def childrenD_150 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 0 (1, 0) envelope_7)]
theorem common_sub_150 : commonEnvelope childrenD_150 ⊆ insert (1, 2) required_150 := by decide +kernel
theorem child_required_sub_150 : ∀ j, childrenC_150 j ⊆ insert (1, 2) required_150 := by decide +kernel
theorem child_envelope_sub_150 : ∀ j, childrenD_150 j ⊆ envelope_150 := by decide +kernel
theorem pivot_mem_150 : (1, 2) ∈ envelope_150 := by decide +kernel
theorem children_work_150 : ∀ j, Template HasSnaky 3 (childrenC_150 j) (childrenD_150 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
theorem row_works_150 : Template HasSnaky 4 required_150 envelope_150 := by
  refine compose HasSnaky 3 childrenC_150 childrenD_150 children_work_150 (1, 2)
    required_150 envelope_150 pivot_mem_150 child_required_sub_150 child_envelope_sub_150 ?_
  intro b hb
  exact common_sub_150 (mem_commonEnvelope childrenD_150 b hb)
def required_151 : Finset Cell := ⟨(([(0, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_151 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_151 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) required_21), (placed21 7 (4, 4) required_35)]
def childrenD_151 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) envelope_21), (placed21 7 (4, 4) envelope_35)]
theorem common_sub_151 : commonEnvelope childrenD_151 ⊆ insert (4, 2) required_151 := by decide +kernel
theorem child_required_sub_151 : ∀ j, childrenC_151 j ⊆ insert (4, 2) required_151 := by decide +kernel
theorem child_envelope_sub_151 : ∀ j, childrenD_151 j ⊆ envelope_151 := by decide +kernel
theorem pivot_mem_151 : (4, 2) ∈ envelope_151 := by decide +kernel
theorem children_work_151 : ∀ j, Template HasSnaky 3 (childrenC_151 j) (childrenD_151 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 7 (4, 4)).mono (by decide +kernel)
theorem row_works_151 : Template HasSnaky 4 required_151 envelope_151 := by
  refine compose HasSnaky 3 childrenC_151 childrenD_151 children_work_151 (4, 2)
    required_151 envelope_151 pivot_mem_151 child_required_sub_151 child_envelope_sub_151 ?_
  intro b hb
  exact common_sub_151 (mem_commonEnvelope childrenD_151 b hb)
def required_165 : Finset Cell := ⟨(([(1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_165 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_165 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) required_44), (placed21 1 (0, 2) required_64)]
def childrenD_165 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) envelope_44), (placed21 1 (0, 2) envelope_64)]
theorem common_sub_165 : commonEnvelope childrenD_165 ⊆ insert (4, 3) required_165 := by decide +kernel
theorem child_required_sub_165 : ∀ j, childrenC_165 j ⊆ insert (4, 3) required_165 := by decide +kernel
theorem child_envelope_sub_165 : ∀ j, childrenD_165 j ⊆ envelope_165 := by decide +kernel
theorem pivot_mem_165 : (4, 3) ∈ envelope_165 := by decide +kernel
theorem children_work_165 : ∀ j, Template HasSnaky 3 (childrenC_165 j) (childrenD_165 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_64 1 (0, 2)).mono (by decide +kernel)
theorem row_works_165 : Template HasSnaky 4 required_165 envelope_165 := by
  refine compose HasSnaky 3 childrenC_165 childrenD_165 children_work_165 (4, 3)
    required_165 envelope_165 pivot_mem_165 child_required_sub_165 child_envelope_sub_165 ?_
  intro b hb
  exact common_sub_165 (mem_commonEnvelope childrenD_165 b hb)
def required_168 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_168 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_168 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), (placed21 0 (1, 0) required_131)]
def childrenD_168 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_131)]
theorem common_sub_168 : commonEnvelope childrenD_168 ⊆ insert (2, 2) required_168 := by decide +kernel
theorem child_required_sub_168 : ∀ j, childrenC_168 j ⊆ insert (2, 2) required_168 := by decide +kernel
theorem child_envelope_sub_168 : ∀ j, childrenD_168 j ⊆ envelope_168 := by decide +kernel
theorem pivot_mem_168 : (2, 2) ∈ envelope_168 := by decide +kernel
theorem children_work_168 : ∀ j, Template HasSnaky 3 (childrenC_168 j) (childrenD_168 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_131 0 (1, 0)).mono (by decide +kernel)
theorem row_works_168 : Template HasSnaky 4 required_168 envelope_168 := by
  refine compose HasSnaky 3 childrenC_168 childrenD_168 children_work_168 (2, 2)
    required_168 envelope_168 pivot_mem_168 child_required_sub_168 child_envelope_sub_168 ?_
  intro b hb
  exact common_sub_168 (mem_commonEnvelope childrenD_168 b hb)
def required_178 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_178 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_178 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), (placed21 0 (1, 0) required_177)]
def childrenD_178 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_177)]
theorem common_sub_178 : commonEnvelope childrenD_178 ⊆ insert (1, 1) required_178 := by decide +kernel
theorem child_required_sub_178 : ∀ j, childrenC_178 j ⊆ insert (1, 1) required_178 := by decide +kernel
theorem child_envelope_sub_178 : ∀ j, childrenD_178 j ⊆ envelope_178 := by decide +kernel
theorem pivot_mem_178 : (1, 1) ∈ envelope_178 := by decide +kernel
theorem children_work_178 : ∀ j, Template HasSnaky 3 (childrenC_178 j) (childrenD_178 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_177 0 (1, 0)).mono (by decide +kernel)
theorem row_works_178 : Template HasSnaky 4 required_178 envelope_178 := by
  refine compose HasSnaky 3 childrenC_178 childrenD_178 children_work_178 (1, 1)
    required_178 envelope_178 pivot_mem_178 child_required_sub_178 child_envelope_sub_178 ?_
  intro b hb
  exact common_sub_178 (mem_commonEnvelope childrenD_178 b hb)
def required_185 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_185 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_185 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_5), required_113]
def childrenD_185 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_5), envelope_113]
theorem common_sub_185 : commonEnvelope childrenD_185 ⊆ insert (1, 4) required_185 := by decide +kernel
theorem child_required_sub_185 : ∀ j, childrenC_185 j ⊆ insert (1, 4) required_185 := by decide +kernel
theorem child_envelope_sub_185 : ∀ j, childrenD_185 j ⊆ envelope_185 := by decide +kernel
theorem pivot_mem_185 : (1, 4) ∈ envelope_185 := by decide +kernel
theorem children_work_185 : ∀ j, Template HasSnaky 3 (childrenC_185 j) (childrenD_185 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_113.mono (by decide +kernel)
theorem row_works_185 : Template HasSnaky 4 required_185 envelope_185 := by
  refine compose HasSnaky 3 childrenC_185 childrenD_185 children_work_185 (1, 4)
    required_185 envelope_185 pivot_mem_185 child_required_sub_185 child_envelope_sub_185 ?_
  intro b hb
  exact common_sub_185 (mem_commonEnvelope childrenD_185 b hb)
def required_194 : Finset Cell := ⟨(([(0, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_194 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_194 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 2 (2, 0) required_9)]
def childrenD_194 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 2 (2, 0) envelope_9)]
theorem common_sub_194 : commonEnvelope childrenD_194 ⊆ insert (1, 4) required_194 := by decide +kernel
theorem child_required_sub_194 : ∀ j, childrenC_194 j ⊆ insert (1, 4) required_194 := by decide +kernel
theorem child_envelope_sub_194 : ∀ j, childrenD_194 j ⊆ envelope_194 := by decide +kernel
theorem pivot_mem_194 : (1, 4) ∈ envelope_194 := by decide +kernel
theorem children_work_194 : ∀ j, Template HasSnaky 3 (childrenC_194 j) (childrenD_194 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (2, 0)).mono (by decide +kernel)
theorem row_works_194 : Template HasSnaky 4 required_194 envelope_194 := by
  refine compose HasSnaky 3 childrenC_194 childrenD_194 children_work_194 (1, 4)
    required_194 envelope_194 pivot_mem_194 child_required_sub_194 child_envelope_sub_194 ?_
  intro b hb
  exact common_sub_194 (mem_commonEnvelope childrenD_194 b hb)
def required_195 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_195 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_195 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 0 (1, 0) required_7)]
def childrenD_195 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 0 (1, 0) envelope_7)]
theorem common_sub_195 : commonEnvelope childrenD_195 ⊆ insert (1, 4) required_195 := by decide +kernel
theorem child_required_sub_195 : ∀ j, childrenC_195 j ⊆ insert (1, 4) required_195 := by decide +kernel
theorem child_envelope_sub_195 : ∀ j, childrenD_195 j ⊆ envelope_195 := by decide +kernel
theorem pivot_mem_195 : (1, 4) ∈ envelope_195 := by decide +kernel
theorem children_work_195 : ∀ j, Template HasSnaky 3 (childrenC_195 j) (childrenD_195 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
theorem row_works_195 : Template HasSnaky 4 required_195 envelope_195 := by
  refine compose HasSnaky 3 childrenC_195 childrenD_195 children_work_195 (1, 4)
    required_195 envelope_195 pivot_mem_195 child_required_sub_195 child_envelope_sub_195 ?_
  intro b hb
  exact common_sub_195 (mem_commonEnvelope childrenD_195 b hb)
def required_196 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_196 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 1), (5, 2), (6, 1), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_196 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 0 (1, 0) required_143)]
def childrenD_196 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 0 (1, 0) envelope_143)]
theorem common_sub_196 : commonEnvelope childrenD_196 ⊆ insert (3, 0) required_196 := by decide +kernel
theorem child_required_sub_196 : ∀ j, childrenC_196 j ⊆ insert (3, 0) required_196 := by decide +kernel
theorem child_envelope_sub_196 : ∀ j, childrenD_196 j ⊆ envelope_196 := by decide +kernel
theorem pivot_mem_196 : (3, 0) ∈ envelope_196 := by decide +kernel
theorem children_work_196 : ∀ j, Template HasSnaky 3 (childrenC_196 j) (childrenD_196 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_143 0 (1, 0)).mono (by decide +kernel)
theorem row_works_196 : Template HasSnaky 4 required_196 envelope_196 := by
  refine compose HasSnaky 3 childrenC_196 childrenD_196 children_work_196 (3, 0)
    required_196 envelope_196 pivot_mem_196 child_required_sub_196 child_envelope_sub_196 ?_
  intro b hb
  exact common_sub_196 (mem_commonEnvelope childrenD_196 b hb)
def required_199 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_199 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_199 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) required_0), required_198]
def childrenD_199 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) envelope_0), envelope_198]
theorem common_sub_199 : commonEnvelope childrenD_199 ⊆ insert (1, 1) required_199 := by decide +kernel
theorem child_required_sub_199 : ∀ j, childrenC_199 j ⊆ insert (1, 1) required_199 := by decide +kernel
theorem child_envelope_sub_199 : ∀ j, childrenD_199 j ⊆ envelope_199 := by decide +kernel
theorem pivot_mem_199 : (1, 1) ∈ envelope_199 := by decide +kernel
theorem children_work_199 : ∀ j, Template HasSnaky 3 (childrenC_199 j) (childrenD_199 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact row_works_198.mono (by decide +kernel)
theorem row_works_199 : Template HasSnaky 4 required_199 envelope_199 := by
  refine compose HasSnaky 3 childrenC_199 childrenD_199 children_work_199 (1, 1)
    required_199 envelope_199 pivot_mem_199 child_required_sub_199 child_envelope_sub_199 ?_
  intro b hb
  exact common_sub_199 (mem_commonEnvelope childrenD_199 b hb)
def required_206 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_206 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_206 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) required_0), required_205]
def childrenD_206 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) envelope_0), envelope_205]
theorem common_sub_206 : commonEnvelope childrenD_206 ⊆ insert (1, 1) required_206 := by decide +kernel
theorem child_required_sub_206 : ∀ j, childrenC_206 j ⊆ insert (1, 1) required_206 := by decide +kernel
theorem child_envelope_sub_206 : ∀ j, childrenD_206 j ⊆ envelope_206 := by decide +kernel
theorem pivot_mem_206 : (1, 1) ∈ envelope_206 := by decide +kernel
theorem children_work_206 : ∀ j, Template HasSnaky 3 (childrenC_206 j) (childrenD_206 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact row_works_205.mono (by decide +kernel)
theorem row_works_206 : Template HasSnaky 4 required_206 envelope_206 := by
  refine compose HasSnaky 3 childrenC_206 childrenD_206 children_work_206 (1, 1)
    required_206 envelope_206 pivot_mem_206 child_required_sub_206 child_envelope_sub_206 ?_
  intro b hb
  exact common_sub_206 (mem_commonEnvelope childrenD_206 b hb)
def required_208 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_208 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_208 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_4), (placed21 0 (1, 0) required_207)]
def childrenD_208 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_4), (placed21 0 (1, 0) envelope_207)]
theorem common_sub_208 : commonEnvelope childrenD_208 ⊆ insert (4, 0) required_208 := by decide +kernel
theorem child_required_sub_208 : ∀ j, childrenC_208 j ⊆ insert (4, 0) required_208 := by decide +kernel
theorem child_envelope_sub_208 : ∀ j, childrenD_208 j ⊆ envelope_208 := by decide +kernel
theorem pivot_mem_208 : (4, 0) ∈ envelope_208 := by decide +kernel
theorem children_work_208 : ∀ j, Template HasSnaky 3 (childrenC_208 j) (childrenD_208 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_207 0 (1, 0)).mono (by decide +kernel)
theorem row_works_208 : Template HasSnaky 4 required_208 envelope_208 := by
  refine compose HasSnaky 3 childrenC_208 childrenD_208 children_work_208 (4, 0)
    required_208 envelope_208 pivot_mem_208 child_required_sub_208 child_envelope_sub_208 ?_
  intro b hb
  exact common_sub_208 (mem_commonEnvelope childrenD_208 b hb)
def required_213 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_213 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_213 : Fin 3 → Finset Cell := ![(placed21 2 (2, 0) required_53), (placed21 4 (1, 6) required_53), (placed21 3 (0, 4) required_212)]
def childrenD_213 : Fin 3 → Finset Cell := ![(placed21 2 (2, 0) envelope_53), (placed21 4 (1, 6) envelope_53), (placed21 3 (0, 4) envelope_212)]
theorem common_sub_213 : commonEnvelope childrenD_213 ⊆ insert (1, 4) required_213 := by decide +kernel
theorem child_required_sub_213 : ∀ j, childrenC_213 j ⊆ insert (1, 4) required_213 := by decide +kernel
theorem child_envelope_sub_213 : ∀ j, childrenD_213 j ⊆ envelope_213 := by decide +kernel
theorem pivot_mem_213 : (1, 4) ∈ envelope_213 := by decide +kernel
theorem children_work_213 : ∀ j, Template HasSnaky 3 (childrenC_213 j) (childrenD_213 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 2 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_212 3 (0, 4)).mono (by decide +kernel)
theorem row_works_213 : Template HasSnaky 4 required_213 envelope_213 := by
  refine compose HasSnaky 3 childrenC_213 childrenD_213 children_work_213 (1, 4)
    required_213 envelope_213 pivot_mem_213 child_required_sub_213 child_envelope_sub_213 ?_
  intro b hb
  exact common_sub_213 (mem_commonEnvelope childrenD_213 b hb)
def required_216 : Finset Cell := ⟨(([(1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_216 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_216 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) required_52), (placed21 1 (0, 2) required_54)]
def childrenD_216 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) envelope_52), (placed21 1 (0, 2) envelope_54)]
theorem common_sub_216 : commonEnvelope childrenD_216 ⊆ insert (4, 3) required_216 := by decide +kernel
theorem child_required_sub_216 : ∀ j, childrenC_216 j ⊆ insert (4, 3) required_216 := by decide +kernel
theorem child_envelope_sub_216 : ∀ j, childrenD_216 j ⊆ envelope_216 := by decide +kernel
theorem pivot_mem_216 : (4, 3) ∈ envelope_216 := by decide +kernel
theorem children_work_216 : ∀ j, Template HasSnaky 3 (childrenC_216 j) (childrenD_216 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_54 1 (0, 2)).mono (by decide +kernel)
theorem row_works_216 : Template HasSnaky 4 required_216 envelope_216 := by
  refine compose HasSnaky 3 childrenC_216 childrenD_216 children_work_216 (4, 3)
    required_216 envelope_216 pivot_mem_216 child_required_sub_216 child_envelope_sub_216 ?_
  intro b hb
  exact common_sub_216 (mem_commonEnvelope childrenD_216 b hb)
def required_227 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 3), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_227 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_227 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 2 (2, 0) required_53)]
def childrenD_227 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 2 (2, 0) envelope_53)]
theorem common_sub_227 : commonEnvelope childrenD_227 ⊆ insert (1, 4) required_227 := by decide +kernel
theorem child_required_sub_227 : ∀ j, childrenC_227 j ⊆ insert (1, 4) required_227 := by decide +kernel
theorem child_envelope_sub_227 : ∀ j, childrenD_227 j ⊆ envelope_227 := by decide +kernel
theorem pivot_mem_227 : (1, 4) ∈ envelope_227 := by decide +kernel
theorem children_work_227 : ∀ j, Template HasSnaky 3 (childrenC_227 j) (childrenD_227 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 2 (2, 0)).mono (by decide +kernel)
theorem row_works_227 : Template HasSnaky 4 required_227 envelope_227 := by
  refine compose HasSnaky 3 childrenC_227 childrenD_227 children_work_227 (1, 4)
    required_227 envelope_227 pivot_mem_227 child_required_sub_227 child_envelope_sub_227 ?_
  intro b hb
  exact common_sub_227 (mem_commonEnvelope childrenD_227 b hb)
def required_229 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_229 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_229 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), required_215]
def childrenD_229 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), envelope_215]
theorem common_sub_229 : commonEnvelope childrenD_229 ⊆ insert (3, 3) required_229 := by decide +kernel
theorem child_required_sub_229 : ∀ j, childrenC_229 j ⊆ insert (3, 3) required_229 := by decide +kernel
theorem child_envelope_sub_229 : ∀ j, childrenD_229 j ⊆ envelope_229 := by decide +kernel
theorem pivot_mem_229 : (3, 3) ∈ envelope_229 := by decide +kernel
theorem children_work_229 : ∀ j, Template HasSnaky 3 (childrenC_229 j) (childrenD_229 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_215.mono (by decide +kernel)
theorem row_works_229 : Template HasSnaky 4 required_229 envelope_229 := by
  refine compose HasSnaky 3 childrenC_229 childrenD_229 children_work_229 (3, 3)
    required_229 envelope_229 pivot_mem_229 child_required_sub_229 child_envelope_sub_229 ?_
  intro b hb
  exact common_sub_229 (mem_commonEnvelope childrenD_229 b hb)
def required_235 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 4), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_235 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_235 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 1 (0, 1) required_226)]
def childrenD_235 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_226)]
theorem common_sub_235 : commonEnvelope childrenD_235 ⊆ insert (2, 1) required_235 := by decide +kernel
theorem child_required_sub_235 : ∀ j, childrenC_235 j ⊆ insert (2, 1) required_235 := by decide +kernel
theorem child_envelope_sub_235 : ∀ j, childrenD_235 j ⊆ envelope_235 := by decide +kernel
theorem pivot_mem_235 : (2, 1) ∈ envelope_235 := by decide +kernel
theorem children_work_235 : ∀ j, Template HasSnaky 3 (childrenC_235 j) (childrenD_235 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_226 1 (0, 1)).mono (by decide +kernel)
theorem row_works_235 : Template HasSnaky 4 required_235 envelope_235 := by
  refine compose HasSnaky 3 childrenC_235 childrenD_235 children_work_235 (2, 1)
    required_235 envelope_235 pivot_mem_235 child_required_sub_235 child_envelope_sub_235 ?_
  intro b hb
  exact common_sub_235 (mem_commonEnvelope childrenD_235 b hb)
def required_240 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_240 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_240 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), (placed21 2 (3, 0) required_52)]
def childrenD_240 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), (placed21 2 (3, 0) envelope_52)]
theorem common_sub_240 : commonEnvelope childrenD_240 ⊆ insert (2, 3) required_240 := by decide +kernel
theorem child_required_sub_240 : ∀ j, childrenC_240 j ⊆ insert (2, 3) required_240 := by decide +kernel
theorem child_envelope_sub_240 : ∀ j, childrenD_240 j ⊆ envelope_240 := by decide +kernel
theorem pivot_mem_240 : (2, 3) ∈ envelope_240 := by decide +kernel
theorem children_work_240 : ∀ j, Template HasSnaky 3 (childrenC_240 j) (childrenD_240 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (3, 0)).mono (by decide +kernel)
theorem row_works_240 : Template HasSnaky 4 required_240 envelope_240 := by
  refine compose HasSnaky 3 childrenC_240 childrenD_240 children_work_240 (2, 3)
    required_240 envelope_240 pivot_mem_240 child_required_sub_240 child_envelope_sub_240 ?_
  intro b hb
  exact common_sub_240 (mem_commonEnvelope childrenD_240 b hb)
def required_242 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_242 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_242 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_5), (placed21 0 (1, 0) required_69)]
def childrenD_242 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_69)]
theorem common_sub_242 : commonEnvelope childrenD_242 ⊆ insert (4, 2) required_242 := by decide +kernel
theorem child_required_sub_242 : ∀ j, childrenC_242 j ⊆ insert (4, 2) required_242 := by decide +kernel
theorem child_envelope_sub_242 : ∀ j, childrenD_242 j ⊆ envelope_242 := by decide +kernel
theorem pivot_mem_242 : (4, 2) ∈ envelope_242 := by decide +kernel
theorem children_work_242 : ∀ j, Template HasSnaky 3 (childrenC_242 j) (childrenD_242 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_69 0 (1, 0)).mono (by decide +kernel)
theorem row_works_242 : Template HasSnaky 4 required_242 envelope_242 := by
  refine compose HasSnaky 3 childrenC_242 childrenD_242 children_work_242 (4, 2)
    required_242 envelope_242 pivot_mem_242 child_required_sub_242 child_envelope_sub_242 ?_
  intro b hb
  exact common_sub_242 (mem_commonEnvelope childrenD_242 b hb)
def required_259 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_259 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_259 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) required_15), (placed21 4 (0, 5) required_159)]
def childrenD_259 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) envelope_15), (placed21 4 (0, 5) envelope_159)]
theorem common_sub_259 : commonEnvelope childrenD_259 ⊆ insert (2, 4) required_259 := by decide +kernel
theorem child_required_sub_259 : ∀ j, childrenC_259 j ⊆ insert (2, 4) required_259 := by decide +kernel
theorem child_envelope_sub_259 : ∀ j, childrenD_259 j ⊆ envelope_259 := by decide +kernel
theorem pivot_mem_259 : (2, 4) ∈ envelope_259 := by decide +kernel
theorem children_work_259 : ∀ j, Template HasSnaky 3 (childrenC_259 j) (childrenD_259 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_159 4 (0, 5)).mono (by decide +kernel)
theorem row_works_259 : Template HasSnaky 4 required_259 envelope_259 := by
  refine compose HasSnaky 3 childrenC_259 childrenD_259 children_work_259 (2, 4)
    required_259 envelope_259 pivot_mem_259 child_required_sub_259 child_envelope_sub_259 ?_
  intro b hb
  exact common_sub_259 (mem_commonEnvelope childrenD_259 b hb)
def required_263 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_263 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_263 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) required_7), (placed21 2 (4, 0) required_9), (placed21 5 (4, 1) required_78)]
def childrenD_263 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) envelope_7), (placed21 2 (4, 0) envelope_9), (placed21 5 (4, 1) envelope_78)]
theorem common_sub_263 : commonEnvelope childrenD_263 ⊆ insert (3, 4) required_263 := by decide +kernel
theorem child_required_sub_263 : ∀ j, childrenC_263 j ⊆ insert (3, 4) required_263 := by decide +kernel
theorem child_envelope_sub_263 : ∀ j, childrenD_263 j ⊆ envelope_263 := by decide +kernel
theorem pivot_mem_263 : (3, 4) ∈ envelope_263 := by decide +kernel
theorem children_work_263 : ∀ j, Template HasSnaky 3 (childrenC_263 j) (childrenD_263 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 5 (4, 1)).mono (by decide +kernel)
theorem row_works_263 : Template HasSnaky 4 required_263 envelope_263 := by
  refine compose HasSnaky 3 childrenC_263 childrenD_263 children_work_263 (3, 4)
    required_263 envelope_263 pivot_mem_263 child_required_sub_263 child_envelope_sub_263 ?_
  intro b hb
  exact common_sub_263 (mem_commonEnvelope childrenD_263 b hb)
def required_264 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_264 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_264 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_8), (placed21 3 (0, 4) required_201)]
def childrenD_264 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_8), (placed21 3 (0, 4) envelope_201)]
theorem common_sub_264 : commonEnvelope childrenD_264 ⊆ insert (1, 4) required_264 := by decide +kernel
theorem child_required_sub_264 : ∀ j, childrenC_264 j ⊆ insert (1, 4) required_264 := by decide +kernel
theorem child_envelope_sub_264 : ∀ j, childrenD_264 j ⊆ envelope_264 := by decide +kernel
theorem pivot_mem_264 : (1, 4) ∈ envelope_264 := by decide +kernel
theorem children_work_264 : ∀ j, Template HasSnaky 3 (childrenC_264 j) (childrenD_264 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_201 3 (0, 4)).mono (by decide +kernel)
theorem row_works_264 : Template HasSnaky 4 required_264 envelope_264 := by
  refine compose HasSnaky 3 childrenC_264 childrenD_264 children_work_264 (1, 4)
    required_264 envelope_264 pivot_mem_264 child_required_sub_264 child_envelope_sub_264 ?_
  intro b hb
  exact common_sub_264 (mem_commonEnvelope childrenD_264 b hb)
def required_266 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_266 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_266 : Fin 3 → Finset Cell := ![(placed21 0 (0, 2) required_6), (placed21 0 (0, 3) required_16), (placed21 4 (0, 7) required_113)]
def childrenD_266 : Fin 3 → Finset Cell := ![(placed21 0 (0, 2) envelope_6), (placed21 0 (0, 3) envelope_16), (placed21 4 (0, 7) envelope_113)]
theorem common_sub_266 : commonEnvelope childrenD_266 ⊆ insert (0, 6) required_266 := by decide +kernel
theorem child_required_sub_266 : ∀ j, childrenC_266 j ⊆ insert (0, 6) required_266 := by decide +kernel
theorem child_envelope_sub_266 : ∀ j, childrenD_266 j ⊆ envelope_266 := by decide +kernel
theorem pivot_mem_266 : (0, 6) ∈ envelope_266 := by decide +kernel
theorem children_work_266 : ∀ j, Template HasSnaky 3 (childrenC_266 j) (childrenD_266 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_113 4 (0, 7)).mono (by decide +kernel)
theorem row_works_266 : Template HasSnaky 4 required_266 envelope_266 := by
  refine compose HasSnaky 3 childrenC_266 childrenD_266 children_work_266 (0, 6)
    required_266 envelope_266 pivot_mem_266 child_required_sub_266 child_envelope_sub_266 ?_
  intro b hb
  exact common_sub_266 (mem_commonEnvelope childrenD_266 b hb)
def height_149 : ℕ := 4
def childrenH_149 : Fin 2 → ℕ := ![height_5, height_124]
theorem height_exact_149 : height_149 = 1 + Finset.univ.sup childrenH_149 := by decide +kernel
theorem required_origin_149 : ∀ x ∈ required_149,
    (∃ j, x ∈ childrenC_149 j) ∨ ∀ j, x ∈ childrenD_149 j := by decide +kernel
theorem required_exact_149 : required_149 =
    ((Finset.univ.biUnion childrenC_149) ∪ commonEnvelope childrenD_149).erase (1, 3) := by
  exact required_eq_combination childrenC_149 childrenD_149 (1, 3) required_149
    (by decide +kernel) child_required_sub_149 common_sub_149 required_origin_149
theorem envelope_origin_149 : ∀ x ∈ envelope_149,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_149 j := by decide +kernel
theorem envelope_exact_149 : envelope_149 =
    insert (1, 3) (Finset.univ.biUnion childrenD_149) := by
  exact envelope_eq_combination childrenD_149 (1, 3) envelope_149
    pivot_mem_149 child_envelope_sub_149 envelope_origin_149
def checked_149 : CheckedCard where
  required := required_149
  envelope := envelope_149
  height := height_149
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_149
def height_150 : ℕ := 4
def childrenH_150 : Fin 2 → ℕ := ![height_5, height_7]
theorem height_exact_150 : height_150 = 1 + Finset.univ.sup childrenH_150 := by decide +kernel
theorem required_origin_150 : ∀ x ∈ required_150,
    (∃ j, x ∈ childrenC_150 j) ∨ ∀ j, x ∈ childrenD_150 j := by decide +kernel
theorem required_exact_150 : required_150 =
    ((Finset.univ.biUnion childrenC_150) ∪ commonEnvelope childrenD_150).erase (1, 2) := by
  exact required_eq_combination childrenC_150 childrenD_150 (1, 2) required_150
    (by decide +kernel) child_required_sub_150 common_sub_150 required_origin_150
theorem envelope_origin_150 : ∀ x ∈ envelope_150,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_150 j := by decide +kernel
theorem envelope_exact_150 : envelope_150 =
    insert (1, 2) (Finset.univ.biUnion childrenD_150) := by
  exact envelope_eq_combination childrenD_150 (1, 2) envelope_150
    pivot_mem_150 child_envelope_sub_150 envelope_origin_150
def checked_150 : CheckedCard where
  required := required_150
  envelope := envelope_150
  height := height_150
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_150
def height_151 : ℕ := 4
def childrenH_151 : Fin 2 → ℕ := ![height_21, height_35]
theorem height_exact_151 : height_151 = 1 + Finset.univ.sup childrenH_151 := by decide +kernel
theorem required_origin_151 : ∀ x ∈ required_151,
    (∃ j, x ∈ childrenC_151 j) ∨ ∀ j, x ∈ childrenD_151 j := by decide +kernel
theorem required_exact_151 : required_151 =
    ((Finset.univ.biUnion childrenC_151) ∪ commonEnvelope childrenD_151).erase (4, 2) := by
  exact required_eq_combination childrenC_151 childrenD_151 (4, 2) required_151
    (by decide +kernel) child_required_sub_151 common_sub_151 required_origin_151
theorem envelope_origin_151 : ∀ x ∈ envelope_151,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_151 j := by decide +kernel
theorem envelope_exact_151 : envelope_151 =
    insert (4, 2) (Finset.univ.biUnion childrenD_151) := by
  exact envelope_eq_combination childrenD_151 (4, 2) envelope_151
    pivot_mem_151 child_envelope_sub_151 envelope_origin_151
def checked_151 : CheckedCard where
  required := required_151
  envelope := envelope_151
  height := height_151
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_151
def height_165 : ℕ := 4
def childrenH_165 : Fin 2 → ℕ := ![height_44, height_64]
theorem height_exact_165 : height_165 = 1 + Finset.univ.sup childrenH_165 := by decide +kernel
theorem required_origin_165 : ∀ x ∈ required_165,
    (∃ j, x ∈ childrenC_165 j) ∨ ∀ j, x ∈ childrenD_165 j := by decide +kernel
theorem required_exact_165 : required_165 =
    ((Finset.univ.biUnion childrenC_165) ∪ commonEnvelope childrenD_165).erase (4, 3) := by
  exact required_eq_combination childrenC_165 childrenD_165 (4, 3) required_165
    (by decide +kernel) child_required_sub_165 common_sub_165 required_origin_165
theorem envelope_origin_165 : ∀ x ∈ envelope_165,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_165 j := by decide +kernel
theorem envelope_exact_165 : envelope_165 =
    insert (4, 3) (Finset.univ.biUnion childrenD_165) := by
  exact envelope_eq_combination childrenD_165 (4, 3) envelope_165
    pivot_mem_165 child_envelope_sub_165 envelope_origin_165
def checked_165 : CheckedCard where
  required := required_165
  envelope := envelope_165
  height := height_165
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_165
def height_168 : ℕ := 4
def childrenH_168 : Fin 2 → ℕ := ![height_5, height_131]
theorem height_exact_168 : height_168 = 1 + Finset.univ.sup childrenH_168 := by decide +kernel
theorem required_origin_168 : ∀ x ∈ required_168,
    (∃ j, x ∈ childrenC_168 j) ∨ ∀ j, x ∈ childrenD_168 j := by decide +kernel
theorem required_exact_168 : required_168 =
    ((Finset.univ.biUnion childrenC_168) ∪ commonEnvelope childrenD_168).erase (2, 2) := by
  exact required_eq_combination childrenC_168 childrenD_168 (2, 2) required_168
    (by decide +kernel) child_required_sub_168 common_sub_168 required_origin_168
theorem envelope_origin_168 : ∀ x ∈ envelope_168,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_168 j := by decide +kernel
theorem envelope_exact_168 : envelope_168 =
    insert (2, 2) (Finset.univ.biUnion childrenD_168) := by
  exact envelope_eq_combination childrenD_168 (2, 2) envelope_168
    pivot_mem_168 child_envelope_sub_168 envelope_origin_168
def checked_168 : CheckedCard where
  required := required_168
  envelope := envelope_168
  height := height_168
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_168
def height_178 : ℕ := 4
def childrenH_178 : Fin 2 → ℕ := ![height_5, height_177]
theorem height_exact_178 : height_178 = 1 + Finset.univ.sup childrenH_178 := by decide +kernel
theorem required_origin_178 : ∀ x ∈ required_178,
    (∃ j, x ∈ childrenC_178 j) ∨ ∀ j, x ∈ childrenD_178 j := by decide +kernel
theorem required_exact_178 : required_178 =
    ((Finset.univ.biUnion childrenC_178) ∪ commonEnvelope childrenD_178).erase (1, 1) := by
  exact required_eq_combination childrenC_178 childrenD_178 (1, 1) required_178
    (by decide +kernel) child_required_sub_178 common_sub_178 required_origin_178
theorem envelope_origin_178 : ∀ x ∈ envelope_178,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_178 j := by decide +kernel
theorem envelope_exact_178 : envelope_178 =
    insert (1, 1) (Finset.univ.biUnion childrenD_178) := by
  exact envelope_eq_combination childrenD_178 (1, 1) envelope_178
    pivot_mem_178 child_envelope_sub_178 envelope_origin_178
def checked_178 : CheckedCard where
  required := required_178
  envelope := envelope_178
  height := height_178
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_178
def height_185 : ℕ := 4
def childrenH_185 : Fin 2 → ℕ := ![height_5, height_113]
theorem height_exact_185 : height_185 = 1 + Finset.univ.sup childrenH_185 := by decide +kernel
theorem required_origin_185 : ∀ x ∈ required_185,
    (∃ j, x ∈ childrenC_185 j) ∨ ∀ j, x ∈ childrenD_185 j := by decide +kernel
theorem required_exact_185 : required_185 =
    ((Finset.univ.biUnion childrenC_185) ∪ commonEnvelope childrenD_185).erase (1, 4) := by
  exact required_eq_combination childrenC_185 childrenD_185 (1, 4) required_185
    (by decide +kernel) child_required_sub_185 common_sub_185 required_origin_185
theorem envelope_origin_185 : ∀ x ∈ envelope_185,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_185 j := by decide +kernel
theorem envelope_exact_185 : envelope_185 =
    insert (1, 4) (Finset.univ.biUnion childrenD_185) := by
  exact envelope_eq_combination childrenD_185 (1, 4) envelope_185
    pivot_mem_185 child_envelope_sub_185 envelope_origin_185
def checked_185 : CheckedCard where
  required := required_185
  envelope := envelope_185
  height := height_185
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_185
def height_194 : ℕ := 4
def childrenH_194 : Fin 2 → ℕ := ![height_4, height_9]
theorem height_exact_194 : height_194 = 1 + Finset.univ.sup childrenH_194 := by decide +kernel
theorem required_origin_194 : ∀ x ∈ required_194,
    (∃ j, x ∈ childrenC_194 j) ∨ ∀ j, x ∈ childrenD_194 j := by decide +kernel
theorem required_exact_194 : required_194 =
    ((Finset.univ.biUnion childrenC_194) ∪ commonEnvelope childrenD_194).erase (1, 4) := by
  exact required_eq_combination childrenC_194 childrenD_194 (1, 4) required_194
    (by decide +kernel) child_required_sub_194 common_sub_194 required_origin_194
theorem envelope_origin_194 : ∀ x ∈ envelope_194,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_194 j := by decide +kernel
theorem envelope_exact_194 : envelope_194 =
    insert (1, 4) (Finset.univ.biUnion childrenD_194) := by
  exact envelope_eq_combination childrenD_194 (1, 4) envelope_194
    pivot_mem_194 child_envelope_sub_194 envelope_origin_194
def checked_194 : CheckedCard where
  required := required_194
  envelope := envelope_194
  height := height_194
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_194
def height_195 : ℕ := 4
def childrenH_195 : Fin 2 → ℕ := ![height_5, height_7]
theorem height_exact_195 : height_195 = 1 + Finset.univ.sup childrenH_195 := by decide +kernel
theorem required_origin_195 : ∀ x ∈ required_195,
    (∃ j, x ∈ childrenC_195 j) ∨ ∀ j, x ∈ childrenD_195 j := by decide +kernel
theorem required_exact_195 : required_195 =
    ((Finset.univ.biUnion childrenC_195) ∪ commonEnvelope childrenD_195).erase (1, 4) := by
  exact required_eq_combination childrenC_195 childrenD_195 (1, 4) required_195
    (by decide +kernel) child_required_sub_195 common_sub_195 required_origin_195
theorem envelope_origin_195 : ∀ x ∈ envelope_195,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_195 j := by decide +kernel
theorem envelope_exact_195 : envelope_195 =
    insert (1, 4) (Finset.univ.biUnion childrenD_195) := by
  exact envelope_eq_combination childrenD_195 (1, 4) envelope_195
    pivot_mem_195 child_envelope_sub_195 envelope_origin_195
def checked_195 : CheckedCard where
  required := required_195
  envelope := envelope_195
  height := height_195
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_195
def height_196 : ℕ := 4
def childrenH_196 : Fin 2 → ℕ := ![height_5, height_143]
theorem height_exact_196 : height_196 = 1 + Finset.univ.sup childrenH_196 := by decide +kernel
theorem required_origin_196 : ∀ x ∈ required_196,
    (∃ j, x ∈ childrenC_196 j) ∨ ∀ j, x ∈ childrenD_196 j := by decide +kernel
theorem required_exact_196 : required_196 =
    ((Finset.univ.biUnion childrenC_196) ∪ commonEnvelope childrenD_196).erase (3, 0) := by
  exact required_eq_combination childrenC_196 childrenD_196 (3, 0) required_196
    (by decide +kernel) child_required_sub_196 common_sub_196 required_origin_196
theorem envelope_origin_196 : ∀ x ∈ envelope_196,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_196 j := by decide +kernel
theorem envelope_exact_196 : envelope_196 =
    insert (3, 0) (Finset.univ.biUnion childrenD_196) := by
  exact envelope_eq_combination childrenD_196 (3, 0) envelope_196
    pivot_mem_196 child_envelope_sub_196 envelope_origin_196
def checked_196 : CheckedCard where
  required := required_196
  envelope := envelope_196
  height := height_196
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_196
def height_199 : ℕ := 4
def childrenH_199 : Fin 2 → ℕ := ![height_0, height_198]
theorem height_exact_199 : height_199 = 1 + Finset.univ.sup childrenH_199 := by decide +kernel
theorem required_origin_199 : ∀ x ∈ required_199,
    (∃ j, x ∈ childrenC_199 j) ∨ ∀ j, x ∈ childrenD_199 j := by decide +kernel
theorem required_exact_199 : required_199 =
    ((Finset.univ.biUnion childrenC_199) ∪ commonEnvelope childrenD_199).erase (1, 1) := by
  exact required_eq_combination childrenC_199 childrenD_199 (1, 1) required_199
    (by decide +kernel) child_required_sub_199 common_sub_199 required_origin_199
theorem envelope_origin_199 : ∀ x ∈ envelope_199,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_199 j := by decide +kernel
theorem envelope_exact_199 : envelope_199 =
    insert (1, 1) (Finset.univ.biUnion childrenD_199) := by
  exact envelope_eq_combination childrenD_199 (1, 1) envelope_199
    pivot_mem_199 child_envelope_sub_199 envelope_origin_199
def checked_199 : CheckedCard where
  required := required_199
  envelope := envelope_199
  height := height_199
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_199
def height_206 : ℕ := 4
def childrenH_206 : Fin 2 → ℕ := ![height_0, height_205]
theorem height_exact_206 : height_206 = 1 + Finset.univ.sup childrenH_206 := by decide +kernel
theorem required_origin_206 : ∀ x ∈ required_206,
    (∃ j, x ∈ childrenC_206 j) ∨ ∀ j, x ∈ childrenD_206 j := by decide +kernel
theorem required_exact_206 : required_206 =
    ((Finset.univ.biUnion childrenC_206) ∪ commonEnvelope childrenD_206).erase (1, 1) := by
  exact required_eq_combination childrenC_206 childrenD_206 (1, 1) required_206
    (by decide +kernel) child_required_sub_206 common_sub_206 required_origin_206
theorem envelope_origin_206 : ∀ x ∈ envelope_206,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_206 j := by decide +kernel
theorem envelope_exact_206 : envelope_206 =
    insert (1, 1) (Finset.univ.biUnion childrenD_206) := by
  exact envelope_eq_combination childrenD_206 (1, 1) envelope_206
    pivot_mem_206 child_envelope_sub_206 envelope_origin_206
def checked_206 : CheckedCard where
  required := required_206
  envelope := envelope_206
  height := height_206
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_206
def height_208 : ℕ := 4
def childrenH_208 : Fin 2 → ℕ := ![height_4, height_207]
theorem height_exact_208 : height_208 = 1 + Finset.univ.sup childrenH_208 := by decide +kernel
theorem required_origin_208 : ∀ x ∈ required_208,
    (∃ j, x ∈ childrenC_208 j) ∨ ∀ j, x ∈ childrenD_208 j := by decide +kernel
theorem required_exact_208 : required_208 =
    ((Finset.univ.biUnion childrenC_208) ∪ commonEnvelope childrenD_208).erase (4, 0) := by
  exact required_eq_combination childrenC_208 childrenD_208 (4, 0) required_208
    (by decide +kernel) child_required_sub_208 common_sub_208 required_origin_208
theorem envelope_origin_208 : ∀ x ∈ envelope_208,
    x = (4, 0) ∨ ∃ j, x ∈ childrenD_208 j := by decide +kernel
theorem envelope_exact_208 : envelope_208 =
    insert (4, 0) (Finset.univ.biUnion childrenD_208) := by
  exact envelope_eq_combination childrenD_208 (4, 0) envelope_208
    pivot_mem_208 child_envelope_sub_208 envelope_origin_208
def checked_208 : CheckedCard where
  required := required_208
  envelope := envelope_208
  height := height_208
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_208
def height_213 : ℕ := 4
def childrenH_213 : Fin 3 → ℕ := ![height_53, height_53, height_212]
theorem height_exact_213 : height_213 = 1 + Finset.univ.sup childrenH_213 := by decide +kernel
theorem required_origin_213 : ∀ x ∈ required_213,
    (∃ j, x ∈ childrenC_213 j) ∨ ∀ j, x ∈ childrenD_213 j := by decide +kernel
theorem required_exact_213 : required_213 =
    ((Finset.univ.biUnion childrenC_213) ∪ commonEnvelope childrenD_213).erase (1, 4) := by
  exact required_eq_combination childrenC_213 childrenD_213 (1, 4) required_213
    (by decide +kernel) child_required_sub_213 common_sub_213 required_origin_213
theorem envelope_origin_213 : ∀ x ∈ envelope_213,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_213 j := by decide +kernel
theorem envelope_exact_213 : envelope_213 =
    insert (1, 4) (Finset.univ.biUnion childrenD_213) := by
  exact envelope_eq_combination childrenD_213 (1, 4) envelope_213
    pivot_mem_213 child_envelope_sub_213 envelope_origin_213
def checked_213 : CheckedCard where
  required := required_213
  envelope := envelope_213
  height := height_213
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_213
def height_216 : ℕ := 4
def childrenH_216 : Fin 2 → ℕ := ![height_52, height_54]
theorem height_exact_216 : height_216 = 1 + Finset.univ.sup childrenH_216 := by decide +kernel
theorem required_origin_216 : ∀ x ∈ required_216,
    (∃ j, x ∈ childrenC_216 j) ∨ ∀ j, x ∈ childrenD_216 j := by decide +kernel
theorem required_exact_216 : required_216 =
    ((Finset.univ.biUnion childrenC_216) ∪ commonEnvelope childrenD_216).erase (4, 3) := by
  exact required_eq_combination childrenC_216 childrenD_216 (4, 3) required_216
    (by decide +kernel) child_required_sub_216 common_sub_216 required_origin_216
theorem envelope_origin_216 : ∀ x ∈ envelope_216,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_216 j := by decide +kernel
theorem envelope_exact_216 : envelope_216 =
    insert (4, 3) (Finset.univ.biUnion childrenD_216) := by
  exact envelope_eq_combination childrenD_216 (4, 3) envelope_216
    pivot_mem_216 child_envelope_sub_216 envelope_origin_216
def checked_216 : CheckedCard where
  required := required_216
  envelope := envelope_216
  height := height_216
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_216
def height_227 : ℕ := 4
def childrenH_227 : Fin 2 → ℕ := ![height_0, height_53]
theorem height_exact_227 : height_227 = 1 + Finset.univ.sup childrenH_227 := by decide +kernel
theorem required_origin_227 : ∀ x ∈ required_227,
    (∃ j, x ∈ childrenC_227 j) ∨ ∀ j, x ∈ childrenD_227 j := by decide +kernel
theorem required_exact_227 : required_227 =
    ((Finset.univ.biUnion childrenC_227) ∪ commonEnvelope childrenD_227).erase (1, 4) := by
  exact required_eq_combination childrenC_227 childrenD_227 (1, 4) required_227
    (by decide +kernel) child_required_sub_227 common_sub_227 required_origin_227
theorem envelope_origin_227 : ∀ x ∈ envelope_227,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_227 j := by decide +kernel
theorem envelope_exact_227 : envelope_227 =
    insert (1, 4) (Finset.univ.biUnion childrenD_227) := by
  exact envelope_eq_combination childrenD_227 (1, 4) envelope_227
    pivot_mem_227 child_envelope_sub_227 envelope_origin_227
def checked_227 : CheckedCard where
  required := required_227
  envelope := envelope_227
  height := height_227
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_227
def height_229 : ℕ := 4
def childrenH_229 : Fin 2 → ℕ := ![height_5, height_215]
theorem height_exact_229 : height_229 = 1 + Finset.univ.sup childrenH_229 := by decide +kernel
theorem required_origin_229 : ∀ x ∈ required_229,
    (∃ j, x ∈ childrenC_229 j) ∨ ∀ j, x ∈ childrenD_229 j := by decide +kernel
theorem required_exact_229 : required_229 =
    ((Finset.univ.biUnion childrenC_229) ∪ commonEnvelope childrenD_229).erase (3, 3) := by
  exact required_eq_combination childrenC_229 childrenD_229 (3, 3) required_229
    (by decide +kernel) child_required_sub_229 common_sub_229 required_origin_229
theorem envelope_origin_229 : ∀ x ∈ envelope_229,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_229 j := by decide +kernel
theorem envelope_exact_229 : envelope_229 =
    insert (3, 3) (Finset.univ.biUnion childrenD_229) := by
  exact envelope_eq_combination childrenD_229 (3, 3) envelope_229
    pivot_mem_229 child_envelope_sub_229 envelope_origin_229
def checked_229 : CheckedCard where
  required := required_229
  envelope := envelope_229
  height := height_229
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_229
def height_235 : ℕ := 4
def childrenH_235 : Fin 2 → ℕ := ![height_5, height_226]
theorem height_exact_235 : height_235 = 1 + Finset.univ.sup childrenH_235 := by decide +kernel
theorem required_origin_235 : ∀ x ∈ required_235,
    (∃ j, x ∈ childrenC_235 j) ∨ ∀ j, x ∈ childrenD_235 j := by decide +kernel
theorem required_exact_235 : required_235 =
    ((Finset.univ.biUnion childrenC_235) ∪ commonEnvelope childrenD_235).erase (2, 1) := by
  exact required_eq_combination childrenC_235 childrenD_235 (2, 1) required_235
    (by decide +kernel) child_required_sub_235 common_sub_235 required_origin_235
theorem envelope_origin_235 : ∀ x ∈ envelope_235,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_235 j := by decide +kernel
theorem envelope_exact_235 : envelope_235 =
    insert (2, 1) (Finset.univ.biUnion childrenD_235) := by
  exact envelope_eq_combination childrenD_235 (2, 1) envelope_235
    pivot_mem_235 child_envelope_sub_235 envelope_origin_235
def checked_235 : CheckedCard where
  required := required_235
  envelope := envelope_235
  height := height_235
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_235
def height_240 : ℕ := 4
def childrenH_240 : Fin 2 → ℕ := ![height_0, height_52]
theorem height_exact_240 : height_240 = 1 + Finset.univ.sup childrenH_240 := by decide +kernel
theorem required_origin_240 : ∀ x ∈ required_240,
    (∃ j, x ∈ childrenC_240 j) ∨ ∀ j, x ∈ childrenD_240 j := by decide +kernel
theorem required_exact_240 : required_240 =
    ((Finset.univ.biUnion childrenC_240) ∪ commonEnvelope childrenD_240).erase (2, 3) := by
  exact required_eq_combination childrenC_240 childrenD_240 (2, 3) required_240
    (by decide +kernel) child_required_sub_240 common_sub_240 required_origin_240
theorem envelope_origin_240 : ∀ x ∈ envelope_240,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_240 j := by decide +kernel
theorem envelope_exact_240 : envelope_240 =
    insert (2, 3) (Finset.univ.biUnion childrenD_240) := by
  exact envelope_eq_combination childrenD_240 (2, 3) envelope_240
    pivot_mem_240 child_envelope_sub_240 envelope_origin_240
def checked_240 : CheckedCard where
  required := required_240
  envelope := envelope_240
  height := height_240
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_240
def height_242 : ℕ := 4
def childrenH_242 : Fin 2 → ℕ := ![height_5, height_69]
theorem height_exact_242 : height_242 = 1 + Finset.univ.sup childrenH_242 := by decide +kernel
theorem required_origin_242 : ∀ x ∈ required_242,
    (∃ j, x ∈ childrenC_242 j) ∨ ∀ j, x ∈ childrenD_242 j := by decide +kernel
theorem required_exact_242 : required_242 =
    ((Finset.univ.biUnion childrenC_242) ∪ commonEnvelope childrenD_242).erase (4, 2) := by
  exact required_eq_combination childrenC_242 childrenD_242 (4, 2) required_242
    (by decide +kernel) child_required_sub_242 common_sub_242 required_origin_242
theorem envelope_origin_242 : ∀ x ∈ envelope_242,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_242 j := by decide +kernel
theorem envelope_exact_242 : envelope_242 =
    insert (4, 2) (Finset.univ.biUnion childrenD_242) := by
  exact envelope_eq_combination childrenD_242 (4, 2) envelope_242
    pivot_mem_242 child_envelope_sub_242 envelope_origin_242
def checked_242 : CheckedCard where
  required := required_242
  envelope := envelope_242
  height := height_242
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_242
def height_259 : ℕ := 4
def childrenH_259 : Fin 2 → ℕ := ![height_15, height_159]
theorem height_exact_259 : height_259 = 1 + Finset.univ.sup childrenH_259 := by decide +kernel
theorem required_origin_259 : ∀ x ∈ required_259,
    (∃ j, x ∈ childrenC_259 j) ∨ ∀ j, x ∈ childrenD_259 j := by decide +kernel
theorem required_exact_259 : required_259 =
    ((Finset.univ.biUnion childrenC_259) ∪ commonEnvelope childrenD_259).erase (2, 4) := by
  exact required_eq_combination childrenC_259 childrenD_259 (2, 4) required_259
    (by decide +kernel) child_required_sub_259 common_sub_259 required_origin_259
theorem envelope_origin_259 : ∀ x ∈ envelope_259,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_259 j := by decide +kernel
theorem envelope_exact_259 : envelope_259 =
    insert (2, 4) (Finset.univ.biUnion childrenD_259) := by
  exact envelope_eq_combination childrenD_259 (2, 4) envelope_259
    pivot_mem_259 child_envelope_sub_259 envelope_origin_259
def checked_259 : CheckedCard where
  required := required_259
  envelope := envelope_259
  height := height_259
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_259
def height_263 : ℕ := 4
def childrenH_263 : Fin 3 → ℕ := ![height_7, height_9, height_78]
theorem height_exact_263 : height_263 = 1 + Finset.univ.sup childrenH_263 := by decide +kernel
theorem required_origin_263 : ∀ x ∈ required_263,
    (∃ j, x ∈ childrenC_263 j) ∨ ∀ j, x ∈ childrenD_263 j := by decide +kernel
theorem required_exact_263 : required_263 =
    ((Finset.univ.biUnion childrenC_263) ∪ commonEnvelope childrenD_263).erase (3, 4) := by
  exact required_eq_combination childrenC_263 childrenD_263 (3, 4) required_263
    (by decide +kernel) child_required_sub_263 common_sub_263 required_origin_263
theorem envelope_origin_263 : ∀ x ∈ envelope_263,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_263 j := by decide +kernel
theorem envelope_exact_263 : envelope_263 =
    insert (3, 4) (Finset.univ.biUnion childrenD_263) := by
  exact envelope_eq_combination childrenD_263 (3, 4) envelope_263
    pivot_mem_263 child_envelope_sub_263 envelope_origin_263
def checked_263 : CheckedCard where
  required := required_263
  envelope := envelope_263
  height := height_263
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_263
def height_264 : ℕ := 4
def childrenH_264 : Fin 2 → ℕ := ![height_8, height_201]
theorem height_exact_264 : height_264 = 1 + Finset.univ.sup childrenH_264 := by decide +kernel
theorem required_origin_264 : ∀ x ∈ required_264,
    (∃ j, x ∈ childrenC_264 j) ∨ ∀ j, x ∈ childrenD_264 j := by decide +kernel
theorem required_exact_264 : required_264 =
    ((Finset.univ.biUnion childrenC_264) ∪ commonEnvelope childrenD_264).erase (1, 4) := by
  exact required_eq_combination childrenC_264 childrenD_264 (1, 4) required_264
    (by decide +kernel) child_required_sub_264 common_sub_264 required_origin_264
theorem envelope_origin_264 : ∀ x ∈ envelope_264,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_264 j := by decide +kernel
theorem envelope_exact_264 : envelope_264 =
    insert (1, 4) (Finset.univ.biUnion childrenD_264) := by
  exact envelope_eq_combination childrenD_264 (1, 4) envelope_264
    pivot_mem_264 child_envelope_sub_264 envelope_origin_264
def checked_264 : CheckedCard where
  required := required_264
  envelope := envelope_264
  height := height_264
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_264
def height_266 : ℕ := 4
def childrenH_266 : Fin 3 → ℕ := ![height_6, height_16, height_113]
theorem height_exact_266 : height_266 = 1 + Finset.univ.sup childrenH_266 := by decide +kernel
theorem required_origin_266 : ∀ x ∈ required_266,
    (∃ j, x ∈ childrenC_266 j) ∨ ∀ j, x ∈ childrenD_266 j := by decide +kernel
theorem required_exact_266 : required_266 =
    ((Finset.univ.biUnion childrenC_266) ∪ commonEnvelope childrenD_266).erase (0, 6) := by
  exact required_eq_combination childrenC_266 childrenD_266 (0, 6) required_266
    (by decide +kernel) child_required_sub_266 common_sub_266 required_origin_266
theorem envelope_origin_266 : ∀ x ∈ envelope_266,
    x = (0, 6) ∨ ∃ j, x ∈ childrenD_266 j := by decide +kernel
theorem envelope_exact_266 : envelope_266 =
    insert (0, 6) (Finset.univ.biUnion childrenD_266) := by
  exact envelope_eq_combination childrenD_266 (0, 6) envelope_266
    pivot_mem_266 child_envelope_sub_266 envelope_origin_266
def checked_266 : CheckedCard where
  required := required_266
  envelope := envelope_266
  height := height_266
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_266
end SnakyPrototype.Certificate21

end OAI
