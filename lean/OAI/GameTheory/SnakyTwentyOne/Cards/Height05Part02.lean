import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_183 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_183 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_183 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) required_5), (placed21 2 (5, 0) required_178)]
def childrenD_183 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) envelope_5), (placed21 2 (5, 0) envelope_178)]
theorem common_sub_183 : commonEnvelope childrenD_183 ⊆ insert (4, 2) required_183 := by decide +kernel
theorem child_required_sub_183 : ∀ j, childrenC_183 j ⊆ insert (4, 2) required_183 := by decide +kernel
theorem child_envelope_sub_183 : ∀ j, childrenD_183 j ⊆ envelope_183 := by decide +kernel
theorem pivot_mem_183 : (4, 2) ∈ envelope_183 := by decide +kernel
theorem children_work_183 : ∀ j, Template HasSnaky 4 (childrenC_183 j) (childrenD_183 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_178 2 (5, 0)).mono (by decide +kernel)
theorem row_works_183 : Template HasSnaky 5 required_183 envelope_183 := by
  refine compose HasSnaky 4 childrenC_183 childrenD_183 children_work_183 (4, 2)
    required_183 envelope_183 pivot_mem_183 child_required_sub_183 child_envelope_sub_183 ?_
  intro b hb
  exact common_sub_183 (mem_commonEnvelope childrenD_183 b hb)
def required_186 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_186 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_186 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) required_6), (placed21 0 (1, 0) required_185)]
def childrenD_186 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) envelope_6), (placed21 0 (1, 0) envelope_185)]
theorem common_sub_186 : commonEnvelope childrenD_186 ⊆ insert (1, 1) required_186 := by decide +kernel
theorem child_required_sub_186 : ∀ j, childrenC_186 j ⊆ insert (1, 1) required_186 := by decide +kernel
theorem child_envelope_sub_186 : ∀ j, childrenD_186 j ⊆ envelope_186 := by decide +kernel
theorem pivot_mem_186 : (1, 1) ∈ envelope_186 := by decide +kernel
theorem children_work_186 : ∀ j, Template HasSnaky 4 (childrenC_186 j) (childrenD_186 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_185 0 (1, 0)).mono (by decide +kernel)
theorem row_works_186 : Template HasSnaky 5 required_186 envelope_186 := by
  refine compose HasSnaky 4 childrenC_186 childrenD_186 children_work_186 (1, 1)
    required_186 envelope_186 pivot_mem_186 child_required_sub_186 child_envelope_sub_186 ?_
  intro b hb
  exact common_sub_186 (mem_commonEnvelope childrenD_186 b hb)
def required_187 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_187 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_187 : Fin 3 → Finset Cell := ![(placed21 0 (0, 2) required_6), (placed21 0 (0, 2) required_7), (placed21 4 (0, 7) required_185)]
def childrenD_187 : Fin 3 → Finset Cell := ![(placed21 0 (0, 2) envelope_6), (placed21 0 (0, 2) envelope_7), (placed21 4 (0, 7) envelope_185)]
theorem common_sub_187 : commonEnvelope childrenD_187 ⊆ insert (0, 6) required_187 := by decide +kernel
theorem child_required_sub_187 : ∀ j, childrenC_187 j ⊆ insert (0, 6) required_187 := by decide +kernel
theorem child_envelope_sub_187 : ∀ j, childrenD_187 j ⊆ envelope_187 := by decide +kernel
theorem pivot_mem_187 : (0, 6) ∈ envelope_187 := by decide +kernel
theorem children_work_187 : ∀ j, Template HasSnaky 4 (childrenC_187 j) (childrenD_187 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_7 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_185 4 (0, 7)).mono (by decide +kernel)
theorem row_works_187 : Template HasSnaky 5 required_187 envelope_187 := by
  refine compose HasSnaky 4 childrenC_187 childrenD_187 children_work_187 (0, 6)
    required_187 envelope_187 pivot_mem_187 child_required_sub_187 child_envelope_sub_187 ?_
  intro b hb
  exact common_sub_187 (mem_commonEnvelope childrenD_187 b hb)
def required_191 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_191 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_191 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 0 (0, 1) required_89)]
def childrenD_191 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 0 (0, 1) envelope_89)]
theorem common_sub_191 : commonEnvelope childrenD_191 ⊆ insert (0, 1) required_191 := by decide +kernel
theorem child_required_sub_191 : ∀ j, childrenC_191 j ⊆ insert (0, 1) required_191 := by decide +kernel
theorem child_envelope_sub_191 : ∀ j, childrenD_191 j ⊆ envelope_191 := by decide +kernel
theorem pivot_mem_191 : (0, 1) ∈ envelope_191 := by decide +kernel
theorem children_work_191 : ∀ j, Template HasSnaky 4 (childrenC_191 j) (childrenD_191 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_89 0 (0, 1)).mono (by decide +kernel)
theorem row_works_191 : Template HasSnaky 5 required_191 envelope_191 := by
  refine compose HasSnaky 4 childrenC_191 childrenD_191 children_work_191 (0, 1)
    required_191 envelope_191 pivot_mem_191 child_required_sub_191 child_envelope_sub_191 ?_
  intro b hb
  exact common_sub_191 (mem_commonEnvelope childrenD_191 b hb)
def required_197 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_197 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_197 : Fin 4 → Finset Cell := ![(placed21 3 (0, 1) required_6), (placed21 0 (1, 0) required_8), (placed21 0 (1, 0) required_26), required_196]
def childrenD_197 : Fin 4 → Finset Cell := ![(placed21 3 (0, 1) envelope_6), (placed21 0 (1, 0) envelope_8), (placed21 0 (1, 0) envelope_26), envelope_196]
theorem common_sub_197 : commonEnvelope childrenD_197 ⊆ insert (4, 1) required_197 := by decide +kernel
theorem child_required_sub_197 : ∀ j, childrenC_197 j ⊆ insert (4, 1) required_197 := by decide +kernel
theorem child_envelope_sub_197 : ∀ j, childrenD_197 j ⊆ envelope_197 := by decide +kernel
theorem pivot_mem_197 : (4, 1) ∈ envelope_197 := by decide +kernel
theorem children_work_197 : ∀ j, Template HasSnaky 4 (childrenC_197 j) (childrenD_197 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_196.mono (by decide +kernel)
theorem row_works_197 : Template HasSnaky 5 required_197 envelope_197 := by
  refine compose HasSnaky 4 childrenC_197 childrenD_197 children_work_197 (4, 1)
    required_197 envelope_197 pivot_mem_197 child_required_sub_197 child_envelope_sub_197 ?_
  intro b hb
  exact common_sub_197 (mem_commonEnvelope childrenD_197 b hb)
def required_202 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_202 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_202 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 2 (3, 0) required_27)]
def childrenD_202 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 2 (3, 0) envelope_27)]
theorem common_sub_202 : commonEnvelope childrenD_202 ⊆ insert (3, 2) required_202 := by decide +kernel
theorem child_required_sub_202 : ∀ j, childrenC_202 j ⊆ insert (3, 2) required_202 := by decide +kernel
theorem child_envelope_sub_202 : ∀ j, childrenD_202 j ⊆ envelope_202 := by decide +kernel
theorem pivot_mem_202 : (3, 2) ∈ envelope_202 := by decide +kernel
theorem children_work_202 : ∀ j, Template HasSnaky 4 (childrenC_202 j) (childrenD_202 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_27 2 (3, 0)).mono (by decide +kernel)
theorem row_works_202 : Template HasSnaky 5 required_202 envelope_202 := by
  refine compose HasSnaky 4 childrenC_202 childrenD_202 children_work_202 (3, 2)
    required_202 envelope_202 pivot_mem_202 child_required_sub_202 child_envelope_sub_202 ?_
  intro b hb
  exact common_sub_202 (mem_commonEnvelope childrenD_202 b hb)
def required_211 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_211 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_211 : Fin 3 → Finset Cell := ![(placed21 6 (3, 6) required_7), (placed21 1 (2, 2) required_8), (placed21 0 (0, 1) required_151)]
def childrenD_211 : Fin 3 → Finset Cell := ![(placed21 6 (3, 6) envelope_7), (placed21 1 (2, 2) envelope_8), (placed21 0 (0, 1) envelope_151)]
theorem common_sub_211 : commonEnvelope childrenD_211 ⊆ insert (3, 5) required_211 := by decide +kernel
theorem child_required_sub_211 : ∀ j, childrenC_211 j ⊆ insert (3, 5) required_211 := by decide +kernel
theorem child_envelope_sub_211 : ∀ j, childrenD_211 j ⊆ envelope_211 := by decide +kernel
theorem pivot_mem_211 : (3, 5) ∈ envelope_211 := by decide +kernel
theorem children_work_211 : ∀ j, Template HasSnaky 4 (childrenC_211 j) (childrenD_211 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_151 0 (0, 1)).mono (by decide +kernel)
theorem row_works_211 : Template HasSnaky 5 required_211 envelope_211 := by
  refine compose HasSnaky 4 childrenC_211 childrenD_211 children_work_211 (3, 5)
    required_211 envelope_211 pivot_mem_211 child_required_sub_211 child_envelope_sub_211 ?_
  intro b hb
  exact common_sub_211 (mem_commonEnvelope childrenD_211 b hb)
def required_214 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_214 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_214 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_5), (placed21 4 (1, 6) required_213)]
def childrenD_214 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_5), (placed21 4 (1, 6) envelope_213)]
theorem common_sub_214 : commonEnvelope childrenD_214 ⊆ insert (3, 4) required_214 := by decide +kernel
theorem child_required_sub_214 : ∀ j, childrenC_214 j ⊆ insert (3, 4) required_214 := by decide +kernel
theorem child_envelope_sub_214 : ∀ j, childrenD_214 j ⊆ envelope_214 := by decide +kernel
theorem pivot_mem_214 : (3, 4) ∈ envelope_214 := by decide +kernel
theorem children_work_214 : ∀ j, Template HasSnaky 4 (childrenC_214 j) (childrenD_214 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_213 4 (1, 6)).mono (by decide +kernel)
theorem row_works_214 : Template HasSnaky 5 required_214 envelope_214 := by
  refine compose HasSnaky 4 childrenC_214 childrenD_214 children_work_214 (3, 4)
    required_214 envelope_214 pivot_mem_214 child_required_sub_214 child_envelope_sub_214 ?_
  intro b hb
  exact common_sub_214 (mem_commonEnvelope childrenD_214 b hb)
def required_225 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_225 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_225 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) required_6), (placed21 5 (2, 2) required_26)]
def childrenD_225 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) envelope_6), (placed21 5 (2, 2) envelope_26)]
theorem common_sub_225 : commonEnvelope childrenD_225 ⊆ insert (1, 5) required_225 := by decide +kernel
theorem child_required_sub_225 : ∀ j, childrenC_225 j ⊆ insert (1, 5) required_225 := by decide +kernel
theorem child_envelope_sub_225 : ∀ j, childrenD_225 j ⊆ envelope_225 := by decide +kernel
theorem pivot_mem_225 : (1, 5) ∈ envelope_225 := by decide +kernel
theorem children_work_225 : ∀ j, Template HasSnaky 4 (childrenC_225 j) (childrenD_225 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 5 (2, 2)).mono (by decide +kernel)
theorem row_works_225 : Template HasSnaky 5 required_225 envelope_225 := by
  refine compose HasSnaky 4 childrenC_225 childrenD_225 children_work_225 (1, 5)
    required_225 envelope_225 pivot_mem_225 child_required_sub_225 child_envelope_sub_225 ?_
  intro b hb
  exact common_sub_225 (mem_commonEnvelope childrenD_225 b hb)
def required_228 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_228 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_228 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) required_52), (placed21 0 (1, 0) required_227)]
def childrenD_228 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) envelope_52), (placed21 0 (1, 0) envelope_227)]
theorem common_sub_228 : commonEnvelope childrenD_228 ⊆ insert (3, 2) required_228 := by decide +kernel
theorem child_required_sub_228 : ∀ j, childrenC_228 j ⊆ insert (3, 2) required_228 := by decide +kernel
theorem child_envelope_sub_228 : ∀ j, childrenD_228 j ⊆ envelope_228 := by decide +kernel
theorem pivot_mem_228 : (3, 2) ∈ envelope_228 := by decide +kernel
theorem children_work_228 : ∀ j, Template HasSnaky 4 (childrenC_228 j) (childrenD_228 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_227 0 (1, 0)).mono (by decide +kernel)
theorem row_works_228 : Template HasSnaky 5 required_228 envelope_228 := by
  refine compose HasSnaky 4 childrenC_228 childrenD_228 children_work_228 (3, 2)
    required_228 envelope_228 pivot_mem_228 child_required_sub_228 child_envelope_sub_228 ?_
  intro b hb
  exact common_sub_228 (mem_commonEnvelope childrenD_228 b hb)
def required_230 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_230 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_230 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) required_7), (placed21 1 (0, 1) required_9), (placed21 0 (1, 0) required_229)]
def childrenD_230 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) envelope_7), (placed21 1 (0, 1) envelope_9), (placed21 0 (1, 0) envelope_229)]
theorem common_sub_230 : commonEnvelope childrenD_230 ⊆ insert (4, 2) required_230 := by decide +kernel
theorem child_required_sub_230 : ∀ j, childrenC_230 j ⊆ insert (4, 2) required_230 := by decide +kernel
theorem child_envelope_sub_230 : ∀ j, childrenD_230 j ⊆ envelope_230 := by decide +kernel
theorem pivot_mem_230 : (4, 2) ∈ envelope_230 := by decide +kernel
theorem children_work_230 : ∀ j, Template HasSnaky 4 (childrenC_230 j) (childrenD_230 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_229 0 (1, 0)).mono (by decide +kernel)
theorem row_works_230 : Template HasSnaky 5 required_230 envelope_230 := by
  refine compose HasSnaky 4 childrenC_230 childrenD_230 children_work_230 (4, 2)
    required_230 envelope_230 pivot_mem_230 child_required_sub_230 child_envelope_sub_230 ?_
  intro b hb
  exact common_sub_230 (mem_commonEnvelope childrenD_230 b hb)
def required_231 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_231 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_231 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) required_8), (placed21 2 (4, 0) required_55)]
def childrenD_231 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) envelope_8), (placed21 2 (4, 0) envelope_55)]
theorem common_sub_231 : commonEnvelope childrenD_231 ⊆ insert (4, 3) required_231 := by decide +kernel
theorem child_required_sub_231 : ∀ j, childrenC_231 j ⊆ insert (4, 3) required_231 := by decide +kernel
theorem child_envelope_sub_231 : ∀ j, childrenD_231 j ⊆ envelope_231 := by decide +kernel
theorem pivot_mem_231 : (4, 3) ∈ envelope_231 := by decide +kernel
theorem children_work_231 : ∀ j, Template HasSnaky 4 (childrenC_231 j) (childrenD_231 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_55 2 (4, 0)).mono (by decide +kernel)
theorem row_works_231 : Template HasSnaky 5 required_231 envelope_231 := by
  refine compose HasSnaky 4 childrenC_231 childrenD_231 children_work_231 (4, 3)
    required_231 envelope_231 pivot_mem_231 child_required_sub_231 child_envelope_sub_231 ?_
  intro b hb
  exact common_sub_231 (mem_commonEnvelope childrenD_231 b hb)
def required_232 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_232 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_232 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 5 (2, 1) required_26)]
def childrenD_232 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 5 (2, 1) envelope_26)]
theorem common_sub_232 : commonEnvelope childrenD_232 ⊆ insert (1, 4) required_232 := by decide +kernel
theorem child_required_sub_232 : ∀ j, childrenC_232 j ⊆ insert (1, 4) required_232 := by decide +kernel
theorem child_envelope_sub_232 : ∀ j, childrenD_232 j ⊆ envelope_232 := by decide +kernel
theorem pivot_mem_232 : (1, 4) ∈ envelope_232 := by decide +kernel
theorem children_work_232 : ∀ j, Template HasSnaky 4 (childrenC_232 j) (childrenD_232 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 5 (2, 1)).mono (by decide +kernel)
theorem row_works_232 : Template HasSnaky 5 required_232 envelope_232 := by
  refine compose HasSnaky 4 childrenC_232 childrenD_232 children_work_232 (1, 4)
    required_232 envelope_232 pivot_mem_232 child_required_sub_232 child_envelope_sub_232 ?_
  intro b hb
  exact common_sub_232 (mem_commonEnvelope childrenD_232 b hb)
def required_233 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_233 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (7, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_233 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_6), (placed21 3 (1, 1) required_27)]
def childrenD_233 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_6), (placed21 3 (1, 1) envelope_27)]
theorem common_sub_233 : commonEnvelope childrenD_233 ⊆ insert (4, 1) required_233 := by decide +kernel
theorem child_required_sub_233 : ∀ j, childrenC_233 j ⊆ insert (4, 1) required_233 := by decide +kernel
theorem child_envelope_sub_233 : ∀ j, childrenD_233 j ⊆ envelope_233 := by decide +kernel
theorem pivot_mem_233 : (4, 1) ∈ envelope_233 := by decide +kernel
theorem children_work_233 : ∀ j, Template HasSnaky 4 (childrenC_233 j) (childrenD_233 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_27 3 (1, 1)).mono (by decide +kernel)
theorem row_works_233 : Template HasSnaky 5 required_233 envelope_233 := by
  refine compose HasSnaky 4 childrenC_233 childrenD_233 children_work_233 (4, 1)
    required_233 envelope_233 pivot_mem_233 child_required_sub_233 child_envelope_sub_233 ?_
  intro b hb
  exact common_sub_233 (mem_commonEnvelope childrenD_233 b hb)
def required_234 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_234 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_234 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 2 (2, 1) required_148)]
def childrenD_234 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 2 (2, 1) envelope_148)]
theorem common_sub_234 : commonEnvelope childrenD_234 ⊆ insert (2, 1) required_234 := by decide +kernel
theorem child_required_sub_234 : ∀ j, childrenC_234 j ⊆ insert (2, 1) required_234 := by decide +kernel
theorem child_envelope_sub_234 : ∀ j, childrenD_234 j ⊆ envelope_234 := by decide +kernel
theorem pivot_mem_234 : (2, 1) ∈ envelope_234 := by decide +kernel
theorem children_work_234 : ∀ j, Template HasSnaky 4 (childrenC_234 j) (childrenD_234 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_148 2 (2, 1)).mono (by decide +kernel)
theorem row_works_234 : Template HasSnaky 5 required_234 envelope_234 := by
  refine compose HasSnaky 4 childrenC_234 childrenD_234 children_work_234 (2, 1)
    required_234 envelope_234 pivot_mem_234 child_required_sub_234 child_envelope_sub_234 ?_
  intro b hb
  exact common_sub_234 (mem_commonEnvelope childrenD_234 b hb)
def required_237 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_237 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_237 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_0), required_10]
def childrenD_237 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_0), envelope_10]
theorem common_sub_237 : commonEnvelope childrenD_237 ⊆ insert (0, 1) required_237 := by decide +kernel
theorem child_required_sub_237 : ∀ j, childrenC_237 j ⊆ insert (0, 1) required_237 := by decide +kernel
theorem child_envelope_sub_237 : ∀ j, childrenD_237 j ⊆ envelope_237 := by decide +kernel
theorem pivot_mem_237 : (0, 1) ∈ envelope_237 := by decide +kernel
theorem children_work_237 : ∀ j, Template HasSnaky 4 (childrenC_237 j) (childrenD_237 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 2)).mono (by decide +kernel)
  · exact row_works_10.mono (by decide +kernel)
theorem row_works_237 : Template HasSnaky 5 required_237 envelope_237 := by
  refine compose HasSnaky 4 childrenC_237 childrenD_237 children_work_237 (0, 1)
    required_237 envelope_237 pivot_mem_237 child_required_sub_237 child_envelope_sub_237 ?_
  intro b hb
  exact common_sub_237 (mem_commonEnvelope childrenD_237 b hb)
def required_241 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_241 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_241 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 2 (2, 1) required_91)]
def childrenD_241 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 2 (2, 1) envelope_91)]
theorem common_sub_241 : commonEnvelope childrenD_241 ⊆ insert (2, 1) required_241 := by decide +kernel
theorem child_required_sub_241 : ∀ j, childrenC_241 j ⊆ insert (2, 1) required_241 := by decide +kernel
theorem child_envelope_sub_241 : ∀ j, childrenD_241 j ⊆ envelope_241 := by decide +kernel
theorem pivot_mem_241 : (2, 1) ∈ envelope_241 := by decide +kernel
theorem children_work_241 : ∀ j, Template HasSnaky 4 (childrenC_241 j) (childrenD_241 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_91 2 (2, 1)).mono (by decide +kernel)
theorem row_works_241 : Template HasSnaky 5 required_241 envelope_241 := by
  refine compose HasSnaky 4 childrenC_241 childrenD_241 children_work_241 (2, 1)
    required_241 envelope_241 pivot_mem_241 child_required_sub_241 child_envelope_sub_241 ?_
  intro b hb
  exact common_sub_241 (mem_commonEnvelope childrenD_241 b hb)
def required_243 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_243 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_243 : Fin 2 → Finset Cell := ![(placed21 2 (2, 1) required_10), required_242]
def childrenD_243 : Fin 2 → Finset Cell := ![(placed21 2 (2, 1) envelope_10), envelope_242]
theorem common_sub_243 : commonEnvelope childrenD_243 ⊆ insert (2, 2) required_243 := by decide +kernel
theorem child_required_sub_243 : ∀ j, childrenC_243 j ⊆ insert (2, 2) required_243 := by decide +kernel
theorem child_envelope_sub_243 : ∀ j, childrenD_243 j ⊆ envelope_243 := by decide +kernel
theorem pivot_mem_243 : (2, 2) ∈ envelope_243 := by decide +kernel
theorem children_work_243 : ∀ j, Template HasSnaky 4 (childrenC_243 j) (childrenD_243 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (2, 1)).mono (by decide +kernel)
  · exact row_works_242.mono (by decide +kernel)
theorem row_works_243 : Template HasSnaky 5 required_243 envelope_243 := by
  refine compose HasSnaky 4 childrenC_243 childrenD_243 children_work_243 (2, 2)
    required_243 envelope_243 pivot_mem_243 child_required_sub_243 child_envelope_sub_243 ?_
  intro b hb
  exact common_sub_243 (mem_commonEnvelope childrenD_243 b hb)
def required_249 : Finset Cell := ⟨(([(0, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_249 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_249 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_17), (placed21 7 (4, 4) required_35)]
def childrenD_249 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_17), (placed21 7 (4, 4) envelope_35)]
theorem common_sub_249 : commonEnvelope childrenD_249 ⊆ insert (4, 2) required_249 := by decide +kernel
theorem child_required_sub_249 : ∀ j, childrenC_249 j ⊆ insert (4, 2) required_249 := by decide +kernel
theorem child_envelope_sub_249 : ∀ j, childrenD_249 j ⊆ envelope_249 := by decide +kernel
theorem pivot_mem_249 : (4, 2) ∈ envelope_249 := by decide +kernel
theorem children_work_249 : ∀ j, Template HasSnaky 4 (childrenC_249 j) (childrenD_249 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 7 (4, 4)).mono (by decide +kernel)
theorem row_works_249 : Template HasSnaky 5 required_249 envelope_249 := by
  refine compose HasSnaky 4 childrenC_249 childrenD_249 children_work_249 (4, 2)
    required_249 envelope_249 pivot_mem_249 child_required_sub_249 child_envelope_sub_249 ?_
  intro b hb
  exact common_sub_249 (mem_commonEnvelope childrenD_249 b hb)
def required_250 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (1, 1), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_250 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_250 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) required_0), required_195]
def childrenD_250 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) envelope_0), envelope_195]
theorem common_sub_250 : commonEnvelope childrenD_250 ⊆ insert (1, 2) required_250 := by decide +kernel
theorem child_required_sub_250 : ∀ j, childrenC_250 j ⊆ insert (1, 2) required_250 := by decide +kernel
theorem child_envelope_sub_250 : ∀ j, childrenD_250 j ⊆ envelope_250 := by decide +kernel
theorem pivot_mem_250 : (1, 2) ∈ envelope_250 := by decide +kernel
theorem children_work_250 : ∀ j, Template HasSnaky 4 (childrenC_250 j) (childrenD_250 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact row_works_195.mono (by decide +kernel)
theorem row_works_250 : Template HasSnaky 5 required_250 envelope_250 := by
  refine compose HasSnaky 4 childrenC_250 childrenD_250 children_work_250 (1, 2)
    required_250 envelope_250 pivot_mem_250 child_required_sub_250 child_envelope_sub_250 ?_
  intro b hb
  exact common_sub_250 (mem_commonEnvelope childrenD_250 b hb)
def required_252 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_252 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 3), (5, 4), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_252 : Fin 3 → Finset Cell := ![(placed21 4 (0, 6) required_55), (placed21 4 (0, 6) required_56), (placed21 1 (1, 2) required_91)]
def childrenD_252 : Fin 3 → Finset Cell := ![(placed21 4 (0, 6) envelope_55), (placed21 4 (0, 6) envelope_56), (placed21 1 (1, 2) envelope_91)]
theorem common_sub_252 : commonEnvelope childrenD_252 ⊆ insert (2, 4) required_252 := by decide +kernel
theorem child_required_sub_252 : ∀ j, childrenC_252 j ⊆ insert (2, 4) required_252 := by decide +kernel
theorem child_envelope_sub_252 : ∀ j, childrenD_252 j ⊆ envelope_252 := by decide +kernel
theorem pivot_mem_252 : (2, 4) ∈ envelope_252 := by decide +kernel
theorem children_work_252 : ∀ j, Template HasSnaky 4 (childrenC_252 j) (childrenD_252 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_55 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_91 1 (1, 2)).mono (by decide +kernel)
theorem row_works_252 : Template HasSnaky 5 required_252 envelope_252 := by
  refine compose HasSnaky 4 childrenC_252 childrenD_252 children_work_252 (2, 4)
    required_252 envelope_252 pivot_mem_252 child_required_sub_252 child_envelope_sub_252 ?_
  intro b hb
  exact common_sub_252 (mem_commonEnvelope childrenD_252 b hb)
def required_254 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_254 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_254 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) required_11), required_75, (placed21 6 (1, 5) required_103)]
def childrenD_254 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) envelope_11), envelope_75, (placed21 6 (1, 5) envelope_103)]
theorem common_sub_254 : commonEnvelope childrenD_254 ⊆ insert (1, 5) required_254 := by decide +kernel
theorem child_required_sub_254 : ∀ j, childrenC_254 j ⊆ insert (1, 5) required_254 := by decide +kernel
theorem child_envelope_sub_254 : ∀ j, childrenD_254 j ⊆ envelope_254 := by decide +kernel
theorem pivot_mem_254 : (1, 5) ∈ envelope_254 := by decide +kernel
theorem children_work_254 : ∀ j, Template HasSnaky 4 (childrenC_254 j) (childrenD_254 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 2 (1, 1)).mono (by decide +kernel)
  · exact row_works_75.mono (by decide +kernel)
  · exact (placed21_template row_works_103 6 (1, 5)).mono (by decide +kernel)
theorem row_works_254 : Template HasSnaky 5 required_254 envelope_254 := by
  refine compose HasSnaky 4 childrenC_254 childrenD_254 children_work_254 (1, 5)
    required_254 envelope_254 pivot_mem_254 child_required_sub_254 child_envelope_sub_254 ?_
  intro b hb
  exact common_sub_254 (mem_commonEnvelope childrenD_254 b hb)
def required_260 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3), (2, 1), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_260 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3), (1, 4), (2, 1), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_260 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 5 (4, 0) required_208)]
def childrenD_260 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 5 (4, 0) envelope_208)]
theorem common_sub_260 : commonEnvelope childrenD_260 ⊆ insert (3, 0) required_260 := by decide +kernel
theorem child_required_sub_260 : ∀ j, childrenC_260 j ⊆ insert (3, 0) required_260 := by decide +kernel
theorem child_envelope_sub_260 : ∀ j, childrenD_260 j ⊆ envelope_260 := by decide +kernel
theorem pivot_mem_260 : (3, 0) ∈ envelope_260 := by decide +kernel
theorem children_work_260 : ∀ j, Template HasSnaky 4 (childrenC_260 j) (childrenD_260 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_208 5 (4, 0)).mono (by decide +kernel)
theorem row_works_260 : Template HasSnaky 5 required_260 envelope_260 := by
  refine compose HasSnaky 4 childrenC_260 childrenD_260 children_work_260 (3, 0)
    required_260 envelope_260 pivot_mem_260 child_required_sub_260 child_envelope_sub_260 ?_
  intro b hb
  exact common_sub_260 (mem_commonEnvelope childrenD_260 b hb)
def required_265 : Finset Cell := ⟨(([(0, 0), (0, 3), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_265 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_265 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 1 (0, 1) required_93)]
def childrenD_265 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 1 (0, 1) envelope_93)]
theorem common_sub_265 : commonEnvelope childrenD_265 ⊆ insert (1, 4) required_265 := by decide +kernel
theorem child_required_sub_265 : ∀ j, childrenC_265 j ⊆ insert (1, 4) required_265 := by decide +kernel
theorem child_envelope_sub_265 : ∀ j, childrenD_265 j ⊆ envelope_265 := by decide +kernel
theorem pivot_mem_265 : (1, 4) ∈ envelope_265 := by decide +kernel
theorem children_work_265 : ∀ j, Template HasSnaky 4 (childrenC_265 j) (childrenD_265 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_93 1 (0, 1)).mono (by decide +kernel)
theorem row_works_265 : Template HasSnaky 5 required_265 envelope_265 := by
  refine compose HasSnaky 4 childrenC_265 childrenD_265 children_work_265 (1, 4)
    required_265 envelope_265 pivot_mem_265 child_required_sub_265 child_envelope_sub_265 ?_
  intro b hb
  exact common_sub_265 (mem_commonEnvelope childrenD_265 b hb)
def height_183 : ℕ := 5
def childrenH_183 : Fin 2 → ℕ := ![height_5, height_178]
theorem height_exact_183 : height_183 = 1 + Finset.univ.sup childrenH_183 := by decide +kernel
theorem required_origin_183 : ∀ x ∈ required_183,
    (∃ j, x ∈ childrenC_183 j) ∨ ∀ j, x ∈ childrenD_183 j := by decide +kernel
theorem required_exact_183 : required_183 =
    ((Finset.univ.biUnion childrenC_183) ∪ commonEnvelope childrenD_183).erase (4, 2) := by
  exact required_eq_combination childrenC_183 childrenD_183 (4, 2) required_183
    (by decide +kernel) child_required_sub_183 common_sub_183 required_origin_183
theorem envelope_origin_183 : ∀ x ∈ envelope_183,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_183 j := by decide +kernel
theorem envelope_exact_183 : envelope_183 =
    insert (4, 2) (Finset.univ.biUnion childrenD_183) := by
  exact envelope_eq_combination childrenD_183 (4, 2) envelope_183
    pivot_mem_183 child_envelope_sub_183 envelope_origin_183
def checked_183 : CheckedCard where
  required := required_183
  envelope := envelope_183
  height := height_183
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_183
def height_186 : ℕ := 5
def childrenH_186 : Fin 2 → ℕ := ![height_6, height_185]
theorem height_exact_186 : height_186 = 1 + Finset.univ.sup childrenH_186 := by decide +kernel
theorem required_origin_186 : ∀ x ∈ required_186,
    (∃ j, x ∈ childrenC_186 j) ∨ ∀ j, x ∈ childrenD_186 j := by decide +kernel
theorem required_exact_186 : required_186 =
    ((Finset.univ.biUnion childrenC_186) ∪ commonEnvelope childrenD_186).erase (1, 1) := by
  exact required_eq_combination childrenC_186 childrenD_186 (1, 1) required_186
    (by decide +kernel) child_required_sub_186 common_sub_186 required_origin_186
theorem envelope_origin_186 : ∀ x ∈ envelope_186,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_186 j := by decide +kernel
theorem envelope_exact_186 : envelope_186 =
    insert (1, 1) (Finset.univ.biUnion childrenD_186) := by
  exact envelope_eq_combination childrenD_186 (1, 1) envelope_186
    pivot_mem_186 child_envelope_sub_186 envelope_origin_186
def checked_186 : CheckedCard where
  required := required_186
  envelope := envelope_186
  height := height_186
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_186
def height_187 : ℕ := 5
def childrenH_187 : Fin 3 → ℕ := ![height_6, height_7, height_185]
theorem height_exact_187 : height_187 = 1 + Finset.univ.sup childrenH_187 := by decide +kernel
theorem required_origin_187 : ∀ x ∈ required_187,
    (∃ j, x ∈ childrenC_187 j) ∨ ∀ j, x ∈ childrenD_187 j := by decide +kernel
theorem required_exact_187 : required_187 =
    ((Finset.univ.biUnion childrenC_187) ∪ commonEnvelope childrenD_187).erase (0, 6) := by
  exact required_eq_combination childrenC_187 childrenD_187 (0, 6) required_187
    (by decide +kernel) child_required_sub_187 common_sub_187 required_origin_187
theorem envelope_origin_187 : ∀ x ∈ envelope_187,
    x = (0, 6) ∨ ∃ j, x ∈ childrenD_187 j := by decide +kernel
theorem envelope_exact_187 : envelope_187 =
    insert (0, 6) (Finset.univ.biUnion childrenD_187) := by
  exact envelope_eq_combination childrenD_187 (0, 6) envelope_187
    pivot_mem_187 child_envelope_sub_187 envelope_origin_187
def checked_187 : CheckedCard where
  required := required_187
  envelope := envelope_187
  height := height_187
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_187
def height_191 : ℕ := 5
def childrenH_191 : Fin 2 → ℕ := ![height_5, height_89]
theorem height_exact_191 : height_191 = 1 + Finset.univ.sup childrenH_191 := by decide +kernel
theorem required_origin_191 : ∀ x ∈ required_191,
    (∃ j, x ∈ childrenC_191 j) ∨ ∀ j, x ∈ childrenD_191 j := by decide +kernel
theorem required_exact_191 : required_191 =
    ((Finset.univ.biUnion childrenC_191) ∪ commonEnvelope childrenD_191).erase (0, 1) := by
  exact required_eq_combination childrenC_191 childrenD_191 (0, 1) required_191
    (by decide +kernel) child_required_sub_191 common_sub_191 required_origin_191
theorem envelope_origin_191 : ∀ x ∈ envelope_191,
    x = (0, 1) ∨ ∃ j, x ∈ childrenD_191 j := by decide +kernel
theorem envelope_exact_191 : envelope_191 =
    insert (0, 1) (Finset.univ.biUnion childrenD_191) := by
  exact envelope_eq_combination childrenD_191 (0, 1) envelope_191
    pivot_mem_191 child_envelope_sub_191 envelope_origin_191
def checked_191 : CheckedCard where
  required := required_191
  envelope := envelope_191
  height := height_191
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_191
def height_197 : ℕ := 5
def childrenH_197 : Fin 4 → ℕ := ![height_6, height_8, height_26, height_196]
theorem height_exact_197 : height_197 = 1 + Finset.univ.sup childrenH_197 := by decide +kernel
theorem required_origin_197 : ∀ x ∈ required_197,
    (∃ j, x ∈ childrenC_197 j) ∨ ∀ j, x ∈ childrenD_197 j := by decide +kernel
theorem required_exact_197 : required_197 =
    ((Finset.univ.biUnion childrenC_197) ∪ commonEnvelope childrenD_197).erase (4, 1) := by
  exact required_eq_combination childrenC_197 childrenD_197 (4, 1) required_197
    (by decide +kernel) child_required_sub_197 common_sub_197 required_origin_197
theorem envelope_origin_197 : ∀ x ∈ envelope_197,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_197 j := by decide +kernel
theorem envelope_exact_197 : envelope_197 =
    insert (4, 1) (Finset.univ.biUnion childrenD_197) := by
  exact envelope_eq_combination childrenD_197 (4, 1) envelope_197
    pivot_mem_197 child_envelope_sub_197 envelope_origin_197
def checked_197 : CheckedCard where
  required := required_197
  envelope := envelope_197
  height := height_197
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_197
def height_202 : ℕ := 5
def childrenH_202 : Fin 2 → ℕ := ![height_5, height_27]
theorem height_exact_202 : height_202 = 1 + Finset.univ.sup childrenH_202 := by decide +kernel
theorem required_origin_202 : ∀ x ∈ required_202,
    (∃ j, x ∈ childrenC_202 j) ∨ ∀ j, x ∈ childrenD_202 j := by decide +kernel
theorem required_exact_202 : required_202 =
    ((Finset.univ.biUnion childrenC_202) ∪ commonEnvelope childrenD_202).erase (3, 2) := by
  exact required_eq_combination childrenC_202 childrenD_202 (3, 2) required_202
    (by decide +kernel) child_required_sub_202 common_sub_202 required_origin_202
theorem envelope_origin_202 : ∀ x ∈ envelope_202,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_202 j := by decide +kernel
theorem envelope_exact_202 : envelope_202 =
    insert (3, 2) (Finset.univ.biUnion childrenD_202) := by
  exact envelope_eq_combination childrenD_202 (3, 2) envelope_202
    pivot_mem_202 child_envelope_sub_202 envelope_origin_202
def checked_202 : CheckedCard where
  required := required_202
  envelope := envelope_202
  height := height_202
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_202
def height_211 : ℕ := 5
def childrenH_211 : Fin 3 → ℕ := ![height_7, height_8, height_151]
theorem height_exact_211 : height_211 = 1 + Finset.univ.sup childrenH_211 := by decide +kernel
theorem required_origin_211 : ∀ x ∈ required_211,
    (∃ j, x ∈ childrenC_211 j) ∨ ∀ j, x ∈ childrenD_211 j := by decide +kernel
theorem required_exact_211 : required_211 =
    ((Finset.univ.biUnion childrenC_211) ∪ commonEnvelope childrenD_211).erase (3, 5) := by
  exact required_eq_combination childrenC_211 childrenD_211 (3, 5) required_211
    (by decide +kernel) child_required_sub_211 common_sub_211 required_origin_211
theorem envelope_origin_211 : ∀ x ∈ envelope_211,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_211 j := by decide +kernel
theorem envelope_exact_211 : envelope_211 =
    insert (3, 5) (Finset.univ.biUnion childrenD_211) := by
  exact envelope_eq_combination childrenD_211 (3, 5) envelope_211
    pivot_mem_211 child_envelope_sub_211 envelope_origin_211
def checked_211 : CheckedCard where
  required := required_211
  envelope := envelope_211
  height := height_211
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_211
def height_214 : ℕ := 5
def childrenH_214 : Fin 2 → ℕ := ![height_5, height_213]
theorem height_exact_214 : height_214 = 1 + Finset.univ.sup childrenH_214 := by decide +kernel
theorem required_origin_214 : ∀ x ∈ required_214,
    (∃ j, x ∈ childrenC_214 j) ∨ ∀ j, x ∈ childrenD_214 j := by decide +kernel
theorem required_exact_214 : required_214 =
    ((Finset.univ.biUnion childrenC_214) ∪ commonEnvelope childrenD_214).erase (3, 4) := by
  exact required_eq_combination childrenC_214 childrenD_214 (3, 4) required_214
    (by decide +kernel) child_required_sub_214 common_sub_214 required_origin_214
theorem envelope_origin_214 : ∀ x ∈ envelope_214,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_214 j := by decide +kernel
theorem envelope_exact_214 : envelope_214 =
    insert (3, 4) (Finset.univ.biUnion childrenD_214) := by
  exact envelope_eq_combination childrenD_214 (3, 4) envelope_214
    pivot_mem_214 child_envelope_sub_214 envelope_origin_214
def checked_214 : CheckedCard where
  required := required_214
  envelope := envelope_214
  height := height_214
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_214
def height_225 : ℕ := 5
def childrenH_225 : Fin 2 → ℕ := ![height_6, height_26]
theorem height_exact_225 : height_225 = 1 + Finset.univ.sup childrenH_225 := by decide +kernel
theorem required_origin_225 : ∀ x ∈ required_225,
    (∃ j, x ∈ childrenC_225 j) ∨ ∀ j, x ∈ childrenD_225 j := by decide +kernel
theorem required_exact_225 : required_225 =
    ((Finset.univ.biUnion childrenC_225) ∪ commonEnvelope childrenD_225).erase (1, 5) := by
  exact required_eq_combination childrenC_225 childrenD_225 (1, 5) required_225
    (by decide +kernel) child_required_sub_225 common_sub_225 required_origin_225
theorem envelope_origin_225 : ∀ x ∈ envelope_225,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_225 j := by decide +kernel
theorem envelope_exact_225 : envelope_225 =
    insert (1, 5) (Finset.univ.biUnion childrenD_225) := by
  exact envelope_eq_combination childrenD_225 (1, 5) envelope_225
    pivot_mem_225 child_envelope_sub_225 envelope_origin_225
def checked_225 : CheckedCard where
  required := required_225
  envelope := envelope_225
  height := height_225
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_225
def height_228 : ℕ := 5
def childrenH_228 : Fin 2 → ℕ := ![height_52, height_227]
theorem height_exact_228 : height_228 = 1 + Finset.univ.sup childrenH_228 := by decide +kernel
theorem required_origin_228 : ∀ x ∈ required_228,
    (∃ j, x ∈ childrenC_228 j) ∨ ∀ j, x ∈ childrenD_228 j := by decide +kernel
theorem required_exact_228 : required_228 =
    ((Finset.univ.biUnion childrenC_228) ∪ commonEnvelope childrenD_228).erase (3, 2) := by
  exact required_eq_combination childrenC_228 childrenD_228 (3, 2) required_228
    (by decide +kernel) child_required_sub_228 common_sub_228 required_origin_228
theorem envelope_origin_228 : ∀ x ∈ envelope_228,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_228 j := by decide +kernel
theorem envelope_exact_228 : envelope_228 =
    insert (3, 2) (Finset.univ.biUnion childrenD_228) := by
  exact envelope_eq_combination childrenD_228 (3, 2) envelope_228
    pivot_mem_228 child_envelope_sub_228 envelope_origin_228
def checked_228 : CheckedCard where
  required := required_228
  envelope := envelope_228
  height := height_228
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_228
def height_230 : ℕ := 5
def childrenH_230 : Fin 3 → ℕ := ![height_7, height_9, height_229]
theorem height_exact_230 : height_230 = 1 + Finset.univ.sup childrenH_230 := by decide +kernel
theorem required_origin_230 : ∀ x ∈ required_230,
    (∃ j, x ∈ childrenC_230 j) ∨ ∀ j, x ∈ childrenD_230 j := by decide +kernel
theorem required_exact_230 : required_230 =
    ((Finset.univ.biUnion childrenC_230) ∪ commonEnvelope childrenD_230).erase (4, 2) := by
  exact required_eq_combination childrenC_230 childrenD_230 (4, 2) required_230
    (by decide +kernel) child_required_sub_230 common_sub_230 required_origin_230
theorem envelope_origin_230 : ∀ x ∈ envelope_230,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_230 j := by decide +kernel
theorem envelope_exact_230 : envelope_230 =
    insert (4, 2) (Finset.univ.biUnion childrenD_230) := by
  exact envelope_eq_combination childrenD_230 (4, 2) envelope_230
    pivot_mem_230 child_envelope_sub_230 envelope_origin_230
def checked_230 : CheckedCard where
  required := required_230
  envelope := envelope_230
  height := height_230
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_230
def height_231 : ℕ := 5
def childrenH_231 : Fin 2 → ℕ := ![height_8, height_55]
theorem height_exact_231 : height_231 = 1 + Finset.univ.sup childrenH_231 := by decide +kernel
theorem required_origin_231 : ∀ x ∈ required_231,
    (∃ j, x ∈ childrenC_231 j) ∨ ∀ j, x ∈ childrenD_231 j := by decide +kernel
theorem required_exact_231 : required_231 =
    ((Finset.univ.biUnion childrenC_231) ∪ commonEnvelope childrenD_231).erase (4, 3) := by
  exact required_eq_combination childrenC_231 childrenD_231 (4, 3) required_231
    (by decide +kernel) child_required_sub_231 common_sub_231 required_origin_231
theorem envelope_origin_231 : ∀ x ∈ envelope_231,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_231 j := by decide +kernel
theorem envelope_exact_231 : envelope_231 =
    insert (4, 3) (Finset.univ.biUnion childrenD_231) := by
  exact envelope_eq_combination childrenD_231 (4, 3) envelope_231
    pivot_mem_231 child_envelope_sub_231 envelope_origin_231
def checked_231 : CheckedCard where
  required := required_231
  envelope := envelope_231
  height := height_231
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_231
def height_232 : ℕ := 5
def childrenH_232 : Fin 2 → ℕ := ![height_5, height_26]
theorem height_exact_232 : height_232 = 1 + Finset.univ.sup childrenH_232 := by decide +kernel
theorem required_origin_232 : ∀ x ∈ required_232,
    (∃ j, x ∈ childrenC_232 j) ∨ ∀ j, x ∈ childrenD_232 j := by decide +kernel
theorem required_exact_232 : required_232 =
    ((Finset.univ.biUnion childrenC_232) ∪ commonEnvelope childrenD_232).erase (1, 4) := by
  exact required_eq_combination childrenC_232 childrenD_232 (1, 4) required_232
    (by decide +kernel) child_required_sub_232 common_sub_232 required_origin_232
theorem envelope_origin_232 : ∀ x ∈ envelope_232,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_232 j := by decide +kernel
theorem envelope_exact_232 : envelope_232 =
    insert (1, 4) (Finset.univ.biUnion childrenD_232) := by
  exact envelope_eq_combination childrenD_232 (1, 4) envelope_232
    pivot_mem_232 child_envelope_sub_232 envelope_origin_232
def checked_232 : CheckedCard where
  required := required_232
  envelope := envelope_232
  height := height_232
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_232
def height_233 : ℕ := 5
def childrenH_233 : Fin 2 → ℕ := ![height_6, height_27]
theorem height_exact_233 : height_233 = 1 + Finset.univ.sup childrenH_233 := by decide +kernel
theorem required_origin_233 : ∀ x ∈ required_233,
    (∃ j, x ∈ childrenC_233 j) ∨ ∀ j, x ∈ childrenD_233 j := by decide +kernel
theorem required_exact_233 : required_233 =
    ((Finset.univ.biUnion childrenC_233) ∪ commonEnvelope childrenD_233).erase (4, 1) := by
  exact required_eq_combination childrenC_233 childrenD_233 (4, 1) required_233
    (by decide +kernel) child_required_sub_233 common_sub_233 required_origin_233
theorem envelope_origin_233 : ∀ x ∈ envelope_233,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_233 j := by decide +kernel
theorem envelope_exact_233 : envelope_233 =
    insert (4, 1) (Finset.univ.biUnion childrenD_233) := by
  exact envelope_eq_combination childrenD_233 (4, 1) envelope_233
    pivot_mem_233 child_envelope_sub_233 envelope_origin_233
def checked_233 : CheckedCard where
  required := required_233
  envelope := envelope_233
  height := height_233
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_233
def height_234 : ℕ := 5
def childrenH_234 : Fin 2 → ℕ := ![height_5, height_148]
theorem height_exact_234 : height_234 = 1 + Finset.univ.sup childrenH_234 := by decide +kernel
theorem required_origin_234 : ∀ x ∈ required_234,
    (∃ j, x ∈ childrenC_234 j) ∨ ∀ j, x ∈ childrenD_234 j := by decide +kernel
theorem required_exact_234 : required_234 =
    ((Finset.univ.biUnion childrenC_234) ∪ commonEnvelope childrenD_234).erase (2, 1) := by
  exact required_eq_combination childrenC_234 childrenD_234 (2, 1) required_234
    (by decide +kernel) child_required_sub_234 common_sub_234 required_origin_234
theorem envelope_origin_234 : ∀ x ∈ envelope_234,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_234 j := by decide +kernel
theorem envelope_exact_234 : envelope_234 =
    insert (2, 1) (Finset.univ.biUnion childrenD_234) := by
  exact envelope_eq_combination childrenD_234 (2, 1) envelope_234
    pivot_mem_234 child_envelope_sub_234 envelope_origin_234
def checked_234 : CheckedCard where
  required := required_234
  envelope := envelope_234
  height := height_234
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_234
def height_237 : ℕ := 5
def childrenH_237 : Fin 2 → ℕ := ![height_0, height_10]
theorem height_exact_237 : height_237 = 1 + Finset.univ.sup childrenH_237 := by decide +kernel
theorem required_origin_237 : ∀ x ∈ required_237,
    (∃ j, x ∈ childrenC_237 j) ∨ ∀ j, x ∈ childrenD_237 j := by decide +kernel
theorem required_exact_237 : required_237 =
    ((Finset.univ.biUnion childrenC_237) ∪ commonEnvelope childrenD_237).erase (0, 1) := by
  exact required_eq_combination childrenC_237 childrenD_237 (0, 1) required_237
    (by decide +kernel) child_required_sub_237 common_sub_237 required_origin_237
theorem envelope_origin_237 : ∀ x ∈ envelope_237,
    x = (0, 1) ∨ ∃ j, x ∈ childrenD_237 j := by decide +kernel
theorem envelope_exact_237 : envelope_237 =
    insert (0, 1) (Finset.univ.biUnion childrenD_237) := by
  exact envelope_eq_combination childrenD_237 (0, 1) envelope_237
    pivot_mem_237 child_envelope_sub_237 envelope_origin_237
def checked_237 : CheckedCard where
  required := required_237
  envelope := envelope_237
  height := height_237
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_237
def height_241 : ℕ := 5
def childrenH_241 : Fin 2 → ℕ := ![height_5, height_91]
theorem height_exact_241 : height_241 = 1 + Finset.univ.sup childrenH_241 := by decide +kernel
theorem required_origin_241 : ∀ x ∈ required_241,
    (∃ j, x ∈ childrenC_241 j) ∨ ∀ j, x ∈ childrenD_241 j := by decide +kernel
theorem required_exact_241 : required_241 =
    ((Finset.univ.biUnion childrenC_241) ∪ commonEnvelope childrenD_241).erase (2, 1) := by
  exact required_eq_combination childrenC_241 childrenD_241 (2, 1) required_241
    (by decide +kernel) child_required_sub_241 common_sub_241 required_origin_241
theorem envelope_origin_241 : ∀ x ∈ envelope_241,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_241 j := by decide +kernel
theorem envelope_exact_241 : envelope_241 =
    insert (2, 1) (Finset.univ.biUnion childrenD_241) := by
  exact envelope_eq_combination childrenD_241 (2, 1) envelope_241
    pivot_mem_241 child_envelope_sub_241 envelope_origin_241
def checked_241 : CheckedCard where
  required := required_241
  envelope := envelope_241
  height := height_241
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_241
def height_243 : ℕ := 5
def childrenH_243 : Fin 2 → ℕ := ![height_10, height_242]
theorem height_exact_243 : height_243 = 1 + Finset.univ.sup childrenH_243 := by decide +kernel
theorem required_origin_243 : ∀ x ∈ required_243,
    (∃ j, x ∈ childrenC_243 j) ∨ ∀ j, x ∈ childrenD_243 j := by decide +kernel
theorem required_exact_243 : required_243 =
    ((Finset.univ.biUnion childrenC_243) ∪ commonEnvelope childrenD_243).erase (2, 2) := by
  exact required_eq_combination childrenC_243 childrenD_243 (2, 2) required_243
    (by decide +kernel) child_required_sub_243 common_sub_243 required_origin_243
theorem envelope_origin_243 : ∀ x ∈ envelope_243,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_243 j := by decide +kernel
theorem envelope_exact_243 : envelope_243 =
    insert (2, 2) (Finset.univ.biUnion childrenD_243) := by
  exact envelope_eq_combination childrenD_243 (2, 2) envelope_243
    pivot_mem_243 child_envelope_sub_243 envelope_origin_243
def checked_243 : CheckedCard where
  required := required_243
  envelope := envelope_243
  height := height_243
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_243
def height_249 : ℕ := 5
def childrenH_249 : Fin 2 → ℕ := ![height_17, height_35]
theorem height_exact_249 : height_249 = 1 + Finset.univ.sup childrenH_249 := by decide +kernel
theorem required_origin_249 : ∀ x ∈ required_249,
    (∃ j, x ∈ childrenC_249 j) ∨ ∀ j, x ∈ childrenD_249 j := by decide +kernel
theorem required_exact_249 : required_249 =
    ((Finset.univ.biUnion childrenC_249) ∪ commonEnvelope childrenD_249).erase (4, 2) := by
  exact required_eq_combination childrenC_249 childrenD_249 (4, 2) required_249
    (by decide +kernel) child_required_sub_249 common_sub_249 required_origin_249
theorem envelope_origin_249 : ∀ x ∈ envelope_249,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_249 j := by decide +kernel
theorem envelope_exact_249 : envelope_249 =
    insert (4, 2) (Finset.univ.biUnion childrenD_249) := by
  exact envelope_eq_combination childrenD_249 (4, 2) envelope_249
    pivot_mem_249 child_envelope_sub_249 envelope_origin_249
def checked_249 : CheckedCard where
  required := required_249
  envelope := envelope_249
  height := height_249
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_249
def height_250 : ℕ := 5
def childrenH_250 : Fin 2 → ℕ := ![height_0, height_195]
theorem height_exact_250 : height_250 = 1 + Finset.univ.sup childrenH_250 := by decide +kernel
theorem required_origin_250 : ∀ x ∈ required_250,
    (∃ j, x ∈ childrenC_250 j) ∨ ∀ j, x ∈ childrenD_250 j := by decide +kernel
theorem required_exact_250 : required_250 =
    ((Finset.univ.biUnion childrenC_250) ∪ commonEnvelope childrenD_250).erase (1, 2) := by
  exact required_eq_combination childrenC_250 childrenD_250 (1, 2) required_250
    (by decide +kernel) child_required_sub_250 common_sub_250 required_origin_250
theorem envelope_origin_250 : ∀ x ∈ envelope_250,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_250 j := by decide +kernel
theorem envelope_exact_250 : envelope_250 =
    insert (1, 2) (Finset.univ.biUnion childrenD_250) := by
  exact envelope_eq_combination childrenD_250 (1, 2) envelope_250
    pivot_mem_250 child_envelope_sub_250 envelope_origin_250
def checked_250 : CheckedCard where
  required := required_250
  envelope := envelope_250
  height := height_250
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_250
def height_252 : ℕ := 5
def childrenH_252 : Fin 3 → ℕ := ![height_55, height_56, height_91]
theorem height_exact_252 : height_252 = 1 + Finset.univ.sup childrenH_252 := by decide +kernel
theorem required_origin_252 : ∀ x ∈ required_252,
    (∃ j, x ∈ childrenC_252 j) ∨ ∀ j, x ∈ childrenD_252 j := by decide +kernel
theorem required_exact_252 : required_252 =
    ((Finset.univ.biUnion childrenC_252) ∪ commonEnvelope childrenD_252).erase (2, 4) := by
  exact required_eq_combination childrenC_252 childrenD_252 (2, 4) required_252
    (by decide +kernel) child_required_sub_252 common_sub_252 required_origin_252
theorem envelope_origin_252 : ∀ x ∈ envelope_252,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_252 j := by decide +kernel
theorem envelope_exact_252 : envelope_252 =
    insert (2, 4) (Finset.univ.biUnion childrenD_252) := by
  exact envelope_eq_combination childrenD_252 (2, 4) envelope_252
    pivot_mem_252 child_envelope_sub_252 envelope_origin_252
def checked_252 : CheckedCard where
  required := required_252
  envelope := envelope_252
  height := height_252
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_252
def height_254 : ℕ := 5
def childrenH_254 : Fin 3 → ℕ := ![height_11, height_75, height_103]
theorem height_exact_254 : height_254 = 1 + Finset.univ.sup childrenH_254 := by decide +kernel
theorem required_origin_254 : ∀ x ∈ required_254,
    (∃ j, x ∈ childrenC_254 j) ∨ ∀ j, x ∈ childrenD_254 j := by decide +kernel
theorem required_exact_254 : required_254 =
    ((Finset.univ.biUnion childrenC_254) ∪ commonEnvelope childrenD_254).erase (1, 5) := by
  exact required_eq_combination childrenC_254 childrenD_254 (1, 5) required_254
    (by decide +kernel) child_required_sub_254 common_sub_254 required_origin_254
theorem envelope_origin_254 : ∀ x ∈ envelope_254,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_254 j := by decide +kernel
theorem envelope_exact_254 : envelope_254 =
    insert (1, 5) (Finset.univ.biUnion childrenD_254) := by
  exact envelope_eq_combination childrenD_254 (1, 5) envelope_254
    pivot_mem_254 child_envelope_sub_254 envelope_origin_254
def checked_254 : CheckedCard where
  required := required_254
  envelope := envelope_254
  height := height_254
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_254
def height_260 : ℕ := 5
def childrenH_260 : Fin 2 → ℕ := ![height_5, height_208]
theorem height_exact_260 : height_260 = 1 + Finset.univ.sup childrenH_260 := by decide +kernel
theorem required_origin_260 : ∀ x ∈ required_260,
    (∃ j, x ∈ childrenC_260 j) ∨ ∀ j, x ∈ childrenD_260 j := by decide +kernel
theorem required_exact_260 : required_260 =
    ((Finset.univ.biUnion childrenC_260) ∪ commonEnvelope childrenD_260).erase (3, 0) := by
  exact required_eq_combination childrenC_260 childrenD_260 (3, 0) required_260
    (by decide +kernel) child_required_sub_260 common_sub_260 required_origin_260
theorem envelope_origin_260 : ∀ x ∈ envelope_260,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_260 j := by decide +kernel
theorem envelope_exact_260 : envelope_260 =
    insert (3, 0) (Finset.univ.biUnion childrenD_260) := by
  exact envelope_eq_combination childrenD_260 (3, 0) envelope_260
    pivot_mem_260 child_envelope_sub_260 envelope_origin_260
def checked_260 : CheckedCard where
  required := required_260
  envelope := envelope_260
  height := height_260
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_260
def height_265 : ℕ := 5
def childrenH_265 : Fin 2 → ℕ := ![height_4, height_93]
theorem height_exact_265 : height_265 = 1 + Finset.univ.sup childrenH_265 := by decide +kernel
theorem required_origin_265 : ∀ x ∈ required_265,
    (∃ j, x ∈ childrenC_265 j) ∨ ∀ j, x ∈ childrenD_265 j := by decide +kernel
theorem required_exact_265 : required_265 =
    ((Finset.univ.biUnion childrenC_265) ∪ commonEnvelope childrenD_265).erase (1, 4) := by
  exact required_eq_combination childrenC_265 childrenD_265 (1, 4) required_265
    (by decide +kernel) child_required_sub_265 common_sub_265 required_origin_265
theorem envelope_origin_265 : ∀ x ∈ envelope_265,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_265 j := by decide +kernel
theorem envelope_exact_265 : envelope_265 =
    insert (1, 4) (Finset.univ.biUnion childrenD_265) := by
  exact envelope_eq_combination childrenD_265 (1, 4) envelope_265
    pivot_mem_265 child_envelope_sub_265 envelope_origin_265
def checked_265 : CheckedCard where
  required := required_265
  envelope := envelope_265
  height := height_265
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_265
end SnakyPrototype.Certificate21

end OAI
