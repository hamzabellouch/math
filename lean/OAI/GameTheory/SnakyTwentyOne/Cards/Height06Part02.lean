import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_193 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_193 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_193 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) required_7), (placed21 5 (2, 2) required_26), (placed21 0 (0, 1) required_191)]
def childrenD_193 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) envelope_7), (placed21 5 (2, 2) envelope_26), (placed21 0 (0, 1) envelope_191)]
theorem common_sub_193 : commonEnvelope childrenD_193 ⊆ insert (1, 5) required_193 := by decide +kernel
theorem child_required_sub_193 : ∀ j, childrenC_193 j ⊆ insert (1, 5) required_193 := by decide +kernel
theorem child_envelope_sub_193 : ∀ j, childrenD_193 j ⊆ envelope_193 := by decide +kernel
theorem pivot_mem_193 : (1, 5) ∈ envelope_193 := by decide +kernel
theorem children_work_193 : ∀ j, Template HasSnaky 5 (childrenC_193 j) (childrenD_193 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 5 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_191 0 (0, 1)).mono (by decide +kernel)
theorem row_works_193 : Template HasSnaky 6 required_193 envelope_193 := by
  refine compose HasSnaky 5 childrenC_193 childrenD_193 children_work_193 (1, 5)
    required_193 envelope_193 pivot_mem_193 child_required_sub_193 child_envelope_sub_193 ?_
  intro b hb
  exact common_sub_193 (mem_commonEnvelope childrenD_193 b hb)
def required_203 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (2, 1), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_203 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 4), (4, 3), (4, 4), (5, 3), (5, 4), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_203 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 1 (0, 1) required_202)]
def childrenD_203 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_202)]
theorem common_sub_203 : commonEnvelope childrenD_203 ⊆ insert (1, 3) required_203 := by decide +kernel
theorem child_required_sub_203 : ∀ j, childrenC_203 j ⊆ insert (1, 3) required_203 := by decide +kernel
theorem child_envelope_sub_203 : ∀ j, childrenD_203 j ⊆ envelope_203 := by decide +kernel
theorem pivot_mem_203 : (1, 3) ∈ envelope_203 := by decide +kernel
theorem children_work_203 : ∀ j, Template HasSnaky 5 (childrenC_203 j) (childrenD_203 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_202 1 (0, 1)).mono (by decide +kernel)
theorem row_works_203 : Template HasSnaky 6 required_203 envelope_203 := by
  refine compose HasSnaky 5 childrenC_203 childrenD_203 children_work_203 (1, 3)
    required_203 envelope_203 pivot_mem_203 child_required_sub_203 child_envelope_sub_203 ?_
  intro b hb
  exact common_sub_203 (mem_commonEnvelope childrenD_203 b hb)
def required_217 : Finset Cell := ⟨(([(1, 2), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_217 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_217 : Fin 3 → Finset Cell := ![(placed21 2 (2, 1) required_21), (placed21 0 (1, 1) required_37), (placed21 3 (0, 5) required_179)]
def childrenD_217 : Fin 3 → Finset Cell := ![(placed21 2 (2, 1) envelope_21), (placed21 0 (1, 1) envelope_37), (placed21 3 (0, 5) envelope_179)]
theorem common_sub_217 : commonEnvelope childrenD_217 ⊆ insert (2, 4) required_217 := by decide +kernel
theorem child_required_sub_217 : ∀ j, childrenC_217 j ⊆ insert (2, 4) required_217 := by decide +kernel
theorem child_envelope_sub_217 : ∀ j, childrenD_217 j ⊆ envelope_217 := by decide +kernel
theorem pivot_mem_217 : (2, 4) ∈ envelope_217 := by decide +kernel
theorem children_work_217 : ∀ j, Template HasSnaky 5 (childrenC_217 j) (childrenD_217 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 3 (0, 5)).mono (by decide +kernel)
theorem row_works_217 : Template HasSnaky 6 required_217 envelope_217 := by
  refine compose HasSnaky 5 childrenC_217 childrenD_217 children_work_217 (2, 4)
    required_217 envelope_217 pivot_mem_217 child_required_sub_217 child_envelope_sub_217 ?_
  intro b hb
  exact common_sub_217 (mem_commonEnvelope childrenD_217 b hb)
def required_238 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_238 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_238 : Fin 2 → Finset Cell := ![(placed21 7 (2, 5) required_0), (placed21 3 (0, 5) required_133)]
def childrenD_238 : Fin 2 → Finset Cell := ![(placed21 7 (2, 5) envelope_0), (placed21 3 (0, 5) envelope_133)]
theorem common_sub_238 : commonEnvelope childrenD_238 ⊆ insert (2, 4) required_238 := by decide +kernel
theorem child_required_sub_238 : ∀ j, childrenC_238 j ⊆ insert (2, 4) required_238 := by decide +kernel
theorem child_envelope_sub_238 : ∀ j, childrenD_238 j ⊆ envelope_238 := by decide +kernel
theorem pivot_mem_238 : (2, 4) ∈ envelope_238 := by decide +kernel
theorem children_work_238 : ∀ j, Template HasSnaky 5 (childrenC_238 j) (childrenD_238 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 3 (0, 5)).mono (by decide +kernel)
theorem row_works_238 : Template HasSnaky 6 required_238 envelope_238 := by
  refine compose HasSnaky 5 childrenC_238 childrenD_238 children_work_238 (2, 4)
    required_238 envelope_238 pivot_mem_238 child_required_sub_238 child_envelope_sub_238 ?_
  intro b hb
  exact common_sub_238 (mem_commonEnvelope childrenD_238 b hb)
def required_248 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_248 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_248 : Fin 3 → Finset Cell := ![(placed21 6 (2, 6) required_44), (placed21 3 (0, 6) required_47), (placed21 0 (1, 1) required_127)]
def childrenD_248 : Fin 3 → Finset Cell := ![(placed21 6 (2, 6) envelope_44), (placed21 3 (0, 6) envelope_47), (placed21 0 (1, 1) envelope_127)]
theorem common_sub_248 : commonEnvelope childrenD_248 ⊆ insert (2, 5) required_248 := by decide +kernel
theorem child_required_sub_248 : ∀ j, childrenC_248 j ⊆ insert (2, 5) required_248 := by decide +kernel
theorem child_envelope_sub_248 : ∀ j, childrenD_248 j ⊆ envelope_248 := by decide +kernel
theorem pivot_mem_248 : (2, 5) ∈ envelope_248 := by decide +kernel
theorem children_work_248 : ∀ j, Template HasSnaky 5 (childrenC_248 j) (childrenD_248 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_127 0 (1, 1)).mono (by decide +kernel)
theorem row_works_248 : Template HasSnaky 6 required_248 envelope_248 := by
  refine compose HasSnaky 5 childrenC_248 childrenD_248 children_work_248 (2, 5)
    required_248 envelope_248 pivot_mem_248 child_required_sub_248 child_envelope_sub_248 ?_
  intro b hb
  exact common_sub_248 (mem_commonEnvelope childrenD_248 b hb)
def required_253 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_253 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_253 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_6), (placed21 1 (1, 2) required_18), required_252]
def childrenD_253 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_6), (placed21 1 (1, 2) envelope_18), envelope_252]
theorem common_sub_253 : commonEnvelope childrenD_253 ⊆ insert (4, 3) required_253 := by decide +kernel
theorem child_required_sub_253 : ∀ j, childrenC_253 j ⊆ insert (4, 3) required_253 := by decide +kernel
theorem child_envelope_sub_253 : ∀ j, childrenD_253 j ⊆ envelope_253 := by decide +kernel
theorem pivot_mem_253 : (4, 3) ∈ envelope_253 := by decide +kernel
theorem children_work_253 : ∀ j, Template HasSnaky 5 (childrenC_253 j) (childrenD_253 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_18 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_252.mono (by decide +kernel)
theorem row_works_253 : Template HasSnaky 6 required_253 envelope_253 := by
  refine compose HasSnaky 5 childrenC_253 childrenD_253 children_work_253 (4, 3)
    required_253 envelope_253 pivot_mem_253 child_required_sub_253 child_envelope_sub_253 ?_
  intro b hb
  exact common_sub_253 (mem_commonEnvelope childrenD_253 b hb)
def required_255 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_255 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_255 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), (placed21 0 (2, 0) required_254)]
def childrenD_255 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), (placed21 0 (2, 0) envelope_254)]
theorem common_sub_255 : commonEnvelope childrenD_255 ⊆ insert (3, 2) required_255 := by decide +kernel
theorem child_required_sub_255 : ∀ j, childrenC_255 j ⊆ insert (3, 2) required_255 := by decide +kernel
theorem child_envelope_sub_255 : ∀ j, childrenD_255 j ⊆ envelope_255 := by decide +kernel
theorem pivot_mem_255 : (3, 2) ∈ envelope_255 := by decide +kernel
theorem children_work_255 : ∀ j, Template HasSnaky 5 (childrenC_255 j) (childrenD_255 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_254 0 (2, 0)).mono (by decide +kernel)
theorem row_works_255 : Template HasSnaky 6 required_255 envelope_255 := by
  refine compose HasSnaky 5 childrenC_255 childrenD_255 children_work_255 (3, 2)
    required_255 envelope_255 pivot_mem_255 child_required_sub_255 child_envelope_sub_255 ?_
  intro b hb
  exact common_sub_255 (mem_commonEnvelope childrenD_255 b hb)
def required_267 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_267 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_267 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) required_8), (placed21 0 (1, 2) required_17), (placed21 0 (1, 0) required_75), (placed21 3 (0, 6) required_179), (placed21 2 (2, 0) required_266)]
def childrenD_267 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) envelope_8), (placed21 0 (1, 2) envelope_17), (placed21 0 (1, 0) envelope_75), (placed21 3 (0, 6) envelope_179), (placed21 2 (2, 0) envelope_266)]
theorem common_sub_267 : commonEnvelope childrenD_267 ⊆ insert (2, 5) required_267 := by decide +kernel
theorem child_required_sub_267 : ∀ j, childrenC_267 j ⊆ insert (2, 5) required_267 := by decide +kernel
theorem child_envelope_sub_267 : ∀ j, childrenD_267 j ⊆ envelope_267 := by decide +kernel
theorem pivot_mem_267 : (2, 5) ∈ envelope_267 := by decide +kernel
theorem children_work_267 : ∀ j, Template HasSnaky 5 (childrenC_267 j) (childrenD_267 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_75 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_266 2 (2, 0)).mono (by decide +kernel)
theorem row_works_267 : Template HasSnaky 6 required_267 envelope_267 := by
  refine compose HasSnaky 5 childrenC_267 childrenD_267 children_work_267 (2, 5)
    required_267 envelope_267 pivot_mem_267 child_required_sub_267 child_envelope_sub_267 ?_
  intro b hb
  exact common_sub_267 (mem_commonEnvelope childrenD_267 b hb)
def required_270 : Finset Cell := ⟨(([(0, 1), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_270 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3), (7, 1), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_270 : Fin 4 → Finset Cell := ![(placed21 7 (4, 2) required_70), (placed21 1 (0, 1) required_106), (placed21 1 (1, 0) required_122), (placed21 1 (0, 1) required_269)]
def childrenD_270 : Fin 4 → Finset Cell := ![(placed21 7 (4, 2) envelope_70), (placed21 1 (0, 1) envelope_106), (placed21 1 (1, 0) envelope_122), (placed21 1 (0, 1) envelope_269)]
theorem common_sub_270 : commonEnvelope childrenD_270 ⊆ insert (4, 2) required_270 := by decide +kernel
theorem child_required_sub_270 : ∀ j, childrenC_270 j ⊆ insert (4, 2) required_270 := by decide +kernel
theorem child_envelope_sub_270 : ∀ j, childrenD_270 j ⊆ envelope_270 := by decide +kernel
theorem pivot_mem_270 : (4, 2) ∈ envelope_270 := by decide +kernel
theorem children_work_270 : ∀ j, Template HasSnaky 5 (childrenC_270 j) (childrenD_270 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_70 7 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_106 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_122 1 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_269 1 (0, 1)).mono (by decide +kernel)
theorem row_works_270 : Template HasSnaky 6 required_270 envelope_270 := by
  refine compose HasSnaky 5 childrenC_270 childrenD_270 children_work_270 (4, 2)
    required_270 envelope_270 pivot_mem_270 child_required_sub_270 child_envelope_sub_270 ?_
  intro b hb
  exact common_sub_270 (mem_commonEnvelope childrenD_270 b hb)
def required_275 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_275 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_275 : Fin 3 → Finset Cell := ![(placed21 3 (1, 2) required_16), (placed21 0 (1, 1) required_24), (placed21 2 (5, 0) required_179)]
def childrenD_275 : Fin 3 → Finset Cell := ![(placed21 3 (1, 2) envelope_16), (placed21 0 (1, 1) envelope_24), (placed21 2 (5, 0) envelope_179)]
theorem common_sub_275 : commonEnvelope childrenD_275 ⊆ insert (4, 2) required_275 := by decide +kernel
theorem child_required_sub_275 : ∀ j, childrenC_275 j ⊆ insert (4, 2) required_275 := by decide +kernel
theorem child_envelope_sub_275 : ∀ j, childrenD_275 j ⊆ envelope_275 := by decide +kernel
theorem pivot_mem_275 : (4, 2) ∈ envelope_275 := by decide +kernel
theorem children_work_275 : ∀ j, Template HasSnaky 5 (childrenC_275 j) (childrenD_275 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 3 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 2 (5, 0)).mono (by decide +kernel)
theorem row_works_275 : Template HasSnaky 6 required_275 envelope_275 := by
  refine compose HasSnaky 5 childrenC_275 childrenD_275 children_work_275 (4, 2)
    required_275 envelope_275 pivot_mem_275 child_required_sub_275 child_envelope_sub_275 ?_
  intro b hb
  exact common_sub_275 (mem_commonEnvelope childrenD_275 b hb)
def required_283 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_283 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3), (7, 1), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_283 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_1), (placed21 0 (2, 0) required_282)]
def childrenD_283 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_1), (placed21 0 (2, 0) envelope_282)]
theorem common_sub_283 : commonEnvelope childrenD_283 ⊆ insert (2, 2) required_283 := by decide +kernel
theorem child_required_sub_283 : ∀ j, childrenC_283 j ⊆ insert (2, 2) required_283 := by decide +kernel
theorem child_envelope_sub_283 : ∀ j, childrenD_283 j ⊆ envelope_283 := by decide +kernel
theorem pivot_mem_283 : (2, 2) ∈ envelope_283 := by decide +kernel
theorem children_work_283 : ∀ j, Template HasSnaky 5 (childrenC_283 j) (childrenD_283 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_282 0 (2, 0)).mono (by decide +kernel)
theorem row_works_283 : Template HasSnaky 6 required_283 envelope_283 := by
  refine compose HasSnaky 5 childrenC_283 childrenD_283 children_work_283 (2, 2)
    required_283 envelope_283 pivot_mem_283 child_required_sub_283 child_envelope_sub_283 ?_
  intro b hb
  exact common_sub_283 (mem_commonEnvelope childrenD_283 b hb)
def required_284 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_284 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_284 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) required_8), (placed21 0 (0, 3) required_17), (placed21 4 (0, 7) required_19), (placed21 0 (0, 1) required_75)]
def childrenD_284 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) envelope_8), (placed21 0 (0, 3) envelope_17), (placed21 4 (0, 7) envelope_19), (placed21 0 (0, 1) envelope_75)]
theorem common_sub_284 : commonEnvelope childrenD_284 ⊆ insert (1, 3) required_284 := by decide +kernel
theorem child_required_sub_284 : ∀ j, childrenC_284 j ⊆ insert (1, 3) required_284 := by decide +kernel
theorem child_envelope_sub_284 : ∀ j, childrenD_284 j ⊆ envelope_284 := by decide +kernel
theorem pivot_mem_284 : (1, 3) ∈ envelope_284 := by decide +kernel
theorem children_work_284 : ∀ j, Template HasSnaky 5 (childrenC_284 j) (childrenD_284 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_75 0 (0, 1)).mono (by decide +kernel)
theorem row_works_284 : Template HasSnaky 6 required_284 envelope_284 := by
  refine compose HasSnaky 5 childrenC_284 childrenD_284 children_work_284 (1, 3)
    required_284 envelope_284 pivot_mem_284 child_required_sub_284 child_envelope_sub_284 ?_
  intro b hb
  exact common_sub_284 (mem_commonEnvelope childrenD_284 b hb)
def required_287 : Finset Cell := ⟨(([(0, 0), (0, 3), (1, 3), (1, 4), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_287 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_287 : Fin 2 → Finset Cell := ![(placed21 6 (1, 6) required_169), (placed21 5 (5, 2) required_230)]
def childrenD_287 : Fin 2 → Finset Cell := ![(placed21 6 (1, 6) envelope_169), (placed21 5 (5, 2) envelope_230)]
theorem common_sub_287 : commonEnvelope childrenD_287 ⊆ insert (1, 6) required_287 := by decide +kernel
theorem child_required_sub_287 : ∀ j, childrenC_287 j ⊆ insert (1, 6) required_287 := by decide +kernel
theorem child_envelope_sub_287 : ∀ j, childrenD_287 j ⊆ envelope_287 := by decide +kernel
theorem pivot_mem_287 : (1, 6) ∈ envelope_287 := by decide +kernel
theorem children_work_287 : ∀ j, Template HasSnaky 5 (childrenC_287 j) (childrenD_287 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_169 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_230 5 (5, 2)).mono (by decide +kernel)
theorem row_works_287 : Template HasSnaky 6 required_287 envelope_287 := by
  refine compose HasSnaky 5 childrenC_287 childrenD_287 children_work_287 (1, 6)
    required_287 envelope_287 pivot_mem_287 child_required_sub_287 child_envelope_sub_287 ?_
  intro b hb
  exact common_sub_287 (mem_commonEnvelope childrenD_287 b hb)
def required_292 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_292 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_292 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) required_6), (placed21 1 (0, 2) required_19), required_214]
def childrenD_292 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) envelope_6), (placed21 1 (0, 2) envelope_19), envelope_214]
theorem common_sub_292 : commonEnvelope childrenD_292 ⊆ insert (4, 3) required_292 := by decide +kernel
theorem child_required_sub_292 : ∀ j, childrenC_292 j ⊆ insert (4, 3) required_292 := by decide +kernel
theorem child_envelope_sub_292 : ∀ j, childrenD_292 j ⊆ envelope_292 := by decide +kernel
theorem pivot_mem_292 : (4, 3) ∈ envelope_292 := by decide +kernel
theorem children_work_292 : ∀ j, Template HasSnaky 5 (childrenC_292 j) (childrenD_292 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_214.mono (by decide +kernel)
theorem row_works_292 : Template HasSnaky 6 required_292 envelope_292 := by
  refine compose HasSnaky 5 childrenC_292 childrenD_292 children_work_292 (4, 3)
    required_292 envelope_292 pivot_mem_292 child_required_sub_292 child_envelope_sub_292 ?_
  intro b hb
  exact common_sub_292 (mem_commonEnvelope childrenD_292 b hb)
def required_300 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_300 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_300 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) required_44), (placed21 6 (2, 6) required_52), (placed21 0 (1, 1) required_128), (placed21 3 (0, 6) required_155)]
def childrenD_300 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) envelope_44), (placed21 6 (2, 6) envelope_52), (placed21 0 (1, 1) envelope_128), (placed21 3 (0, 6) envelope_155)]
theorem common_sub_300 : commonEnvelope childrenD_300 ⊆ insert (2, 5) required_300 := by decide +kernel
theorem child_required_sub_300 : ∀ j, childrenC_300 j ⊆ insert (2, 5) required_300 := by decide +kernel
theorem child_envelope_sub_300 : ∀ j, childrenD_300 j ⊆ envelope_300 := by decide +kernel
theorem pivot_mem_300 : (2, 5) ∈ envelope_300 := by decide +kernel
theorem children_work_300 : ∀ j, Template HasSnaky 5 (childrenC_300 j) (childrenD_300 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_128 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_155 3 (0, 6)).mono (by decide +kernel)
theorem row_works_300 : Template HasSnaky 6 required_300 envelope_300 := by
  refine compose HasSnaky 5 childrenC_300 childrenD_300 children_work_300 (2, 5)
    required_300 envelope_300 pivot_mem_300 child_required_sub_300 child_envelope_sub_300 ?_
  intro b hb
  exact common_sub_300 (mem_commonEnvelope childrenD_300 b hb)
def required_302 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_302 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (6, 3), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_302 : Fin 2 → Finset Cell := ![(placed21 7 (5, 3) required_6), (placed21 4 (1, 6) required_214)]
def childrenD_302 : Fin 2 → Finset Cell := ![(placed21 7 (5, 3) envelope_6), (placed21 4 (1, 6) envelope_214)]
theorem common_sub_302 : commonEnvelope childrenD_302 ⊆ insert (5, 3) required_302 := by decide +kernel
theorem child_required_sub_302 : ∀ j, childrenC_302 j ⊆ insert (5, 3) required_302 := by decide +kernel
theorem child_envelope_sub_302 : ∀ j, childrenD_302 j ⊆ envelope_302 := by decide +kernel
theorem pivot_mem_302 : (5, 3) ∈ envelope_302 := by decide +kernel
theorem children_work_302 : ∀ j, Template HasSnaky 5 (childrenC_302 j) (childrenD_302 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 7 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_214 4 (1, 6)).mono (by decide +kernel)
theorem row_works_302 : Template HasSnaky 6 required_302 envelope_302 := by
  refine compose HasSnaky 5 childrenC_302 childrenD_302 children_work_302 (5, 3)
    required_302 envelope_302 pivot_mem_302 child_required_sub_302 child_envelope_sub_302 ?_
  intro b hb
  exact common_sub_302 (mem_commonEnvelope childrenD_302 b hb)
def required_303 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_303 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_303 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_55), (placed21 3 (0, 4) required_234)]
def childrenD_303 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_55), (placed21 3 (0, 4) envelope_234)]
theorem common_sub_303 : commonEnvelope childrenD_303 ⊆ insert (3, 4) required_303 := by decide +kernel
theorem child_required_sub_303 : ∀ j, childrenC_303 j ⊆ insert (3, 4) required_303 := by decide +kernel
theorem child_envelope_sub_303 : ∀ j, childrenD_303 j ⊆ envelope_303 := by decide +kernel
theorem pivot_mem_303 : (3, 4) ∈ envelope_303 := by decide +kernel
theorem children_work_303 : ∀ j, Template HasSnaky 5 (childrenC_303 j) (childrenD_303 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_55 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_234 3 (0, 4)).mono (by decide +kernel)
theorem row_works_303 : Template HasSnaky 6 required_303 envelope_303 := by
  refine compose HasSnaky 5 childrenC_303 childrenD_303 children_work_303 (3, 4)
    required_303 envelope_303 pivot_mem_303 child_required_sub_303 child_envelope_sub_303 ?_
  intro b hb
  exact common_sub_303 (mem_commonEnvelope childrenD_303 b hb)
def required_313 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_313 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_313 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 5 (4, 0) required_312)]
def childrenD_313 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 5 (4, 0) envelope_312)]
theorem common_sub_313 : commonEnvelope childrenD_313 ⊆ insert (3, 0) required_313 := by decide +kernel
theorem child_required_sub_313 : ∀ j, childrenC_313 j ⊆ insert (3, 0) required_313 := by decide +kernel
theorem child_envelope_sub_313 : ∀ j, childrenD_313 j ⊆ envelope_313 := by decide +kernel
theorem pivot_mem_313 : (3, 0) ∈ envelope_313 := by decide +kernel
theorem children_work_313 : ∀ j, Template HasSnaky 5 (childrenC_313 j) (childrenD_313 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_312 5 (4, 0)).mono (by decide +kernel)
theorem row_works_313 : Template HasSnaky 6 required_313 envelope_313 := by
  refine compose HasSnaky 5 childrenC_313 childrenD_313 children_work_313 (3, 0)
    required_313 envelope_313 pivot_mem_313 child_required_sub_313 child_envelope_sub_313 ?_
  intro b hb
  exact common_sub_313 (mem_commonEnvelope childrenD_313 b hb)
def required_315 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_315 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_315 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_314)]
def childrenD_315 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_314)]
theorem common_sub_315 : commonEnvelope childrenD_315 ⊆ insert (1, 4) required_315 := by decide +kernel
theorem child_required_sub_315 : ∀ j, childrenC_315 j ⊆ insert (1, 4) required_315 := by decide +kernel
theorem child_envelope_sub_315 : ∀ j, childrenD_315 j ⊆ envelope_315 := by decide +kernel
theorem pivot_mem_315 : (1, 4) ∈ envelope_315 := by decide +kernel
theorem children_work_315 : ∀ j, Template HasSnaky 5 (childrenC_315 j) (childrenD_315 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 1 (0, 1)).mono (by decide +kernel)
theorem row_works_315 : Template HasSnaky 6 required_315 envelope_315 := by
  refine compose HasSnaky 5 childrenC_315 childrenD_315 children_work_315 (1, 4)
    required_315 envelope_315 pivot_mem_315 child_required_sub_315 child_envelope_sub_315 ?_
  intro b hb
  exact common_sub_315 (mem_commonEnvelope childrenD_315 b hb)
def required_316 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_316 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_316 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_8), (placed21 1 (0, 2) required_314)]
def childrenD_316 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_8), (placed21 1 (0, 2) envelope_314)]
theorem common_sub_316 : commonEnvelope childrenD_316 ⊆ insert (1, 2) required_316 := by decide +kernel
theorem child_required_sub_316 : ∀ j, childrenC_316 j ⊆ insert (1, 2) required_316 := by decide +kernel
theorem child_envelope_sub_316 : ∀ j, childrenD_316 j ⊆ envelope_316 := by decide +kernel
theorem pivot_mem_316 : (1, 2) ∈ envelope_316 := by decide +kernel
theorem children_work_316 : ∀ j, Template HasSnaky 5 (childrenC_316 j) (childrenD_316 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 1 (0, 2)).mono (by decide +kernel)
theorem row_works_316 : Template HasSnaky 6 required_316 envelope_316 := by
  refine compose HasSnaky 5 childrenC_316 childrenD_316 children_work_316 (1, 2)
    required_316 envelope_316 pivot_mem_316 child_required_sub_316 child_envelope_sub_316 ?_
  intro b hb
  exact common_sub_316 (mem_commonEnvelope childrenD_316 b hb)
def required_331_i1 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_331_i1 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_331_i1 : Fin 2 → Finset Cell := ![(placed21 0 (2, 2) required_20), (placed21 6 (3, 5) required_29)]
def childrenD_331_i1 : Fin 2 → Finset Cell := ![(placed21 0 (2, 2) envelope_20), (placed21 6 (3, 5) envelope_29)]
theorem common_sub_331_i1 : commonEnvelope childrenD_331_i1 ⊆ insert (3, 5) required_331_i1 := by decide +kernel
theorem child_required_sub_331_i1 : ∀ j, childrenC_331_i1 j ⊆ insert (3, 5) required_331_i1 := by decide +kernel
theorem child_envelope_sub_331_i1 : ∀ j, childrenD_331_i1 j ⊆ envelope_331_i1 := by decide +kernel
theorem pivot_mem_331_i1 : (3, 5) ∈ envelope_331_i1 := by decide +kernel
theorem children_work_331_i1 : ∀ j, Template HasSnaky 3 (childrenC_331_i1 j) (childrenD_331_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 6 (3, 5)).mono (by decide +kernel)
theorem row_works_331_i1 : Template HasSnaky 4 required_331_i1 envelope_331_i1 := by
  refine compose HasSnaky 3 childrenC_331_i1 childrenD_331_i1 children_work_331_i1 (3, 5)
    required_331_i1 envelope_331_i1 pivot_mem_331_i1 child_required_sub_331_i1 child_envelope_sub_331_i1 ?_
  intro b hb
  exact common_sub_331_i1 (mem_commonEnvelope childrenD_331_i1 b hb)
def required_331_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_331_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_331_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), required_331_i1]
def childrenD_331_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), envelope_331_i1]
theorem common_sub_331_i0 : commonEnvelope childrenD_331_i0 ⊆ insert (3, 2) required_331_i0 := by decide +kernel
theorem child_required_sub_331_i0 : ∀ j, childrenC_331_i0 j ⊆ insert (3, 2) required_331_i0 := by decide +kernel
theorem child_envelope_sub_331_i0 : ∀ j, childrenD_331_i0 j ⊆ envelope_331_i0 := by decide +kernel
theorem pivot_mem_331_i0 : (3, 2) ∈ envelope_331_i0 := by decide +kernel
theorem children_work_331_i0 : ∀ j, Template HasSnaky 4 (childrenC_331_i0 j) (childrenD_331_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact row_works_331_i1.mono (by decide +kernel)
theorem row_works_331_i0 : Template HasSnaky 5 required_331_i0 envelope_331_i0 := by
  refine compose HasSnaky 4 childrenC_331_i0 childrenD_331_i0 children_work_331_i0 (3, 2)
    required_331_i0 envelope_331_i0 pivot_mem_331_i0 child_required_sub_331_i0 child_envelope_sub_331_i0 ?_
  intro b hb
  exact common_sub_331_i0 (mem_commonEnvelope childrenD_331_i0 b hb)
def required_331 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_331 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_331 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_5), required_331_i0]
def childrenD_331 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_5), envelope_331_i0]
theorem common_sub_331 : commonEnvelope childrenD_331 ⊆ insert (3, 4) required_331 := by decide +kernel
theorem child_required_sub_331 : ∀ j, childrenC_331 j ⊆ insert (3, 4) required_331 := by decide +kernel
theorem child_envelope_sub_331 : ∀ j, childrenD_331 j ⊆ envelope_331 := by decide +kernel
theorem pivot_mem_331 : (3, 4) ∈ envelope_331 := by decide +kernel
theorem children_work_331 : ∀ j, Template HasSnaky 5 (childrenC_331 j) (childrenD_331 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_331_i0.mono (by decide +kernel)
theorem row_works_331 : Template HasSnaky 6 required_331 envelope_331 := by
  refine compose HasSnaky 5 childrenC_331 childrenD_331 children_work_331 (3, 4)
    required_331 envelope_331 pivot_mem_331 child_required_sub_331 child_envelope_sub_331 ?_
  intro b hb
  exact common_sub_331 (mem_commonEnvelope childrenD_331 b hb)
def height_193 : ℕ := 6
def childrenH_193 : Fin 3 → ℕ := ![height_7, height_26, height_191]
theorem height_exact_193 : height_193 = 1 + Finset.univ.sup childrenH_193 := by decide +kernel
theorem required_origin_193 : ∀ x ∈ required_193,
    (∃ j, x ∈ childrenC_193 j) ∨ ∀ j, x ∈ childrenD_193 j := by decide +kernel
theorem required_exact_193 : required_193 =
    ((Finset.univ.biUnion childrenC_193) ∪ commonEnvelope childrenD_193).erase (1, 5) := by
  exact required_eq_combination childrenC_193 childrenD_193 (1, 5) required_193
    (by decide +kernel) child_required_sub_193 common_sub_193 required_origin_193
theorem envelope_origin_193 : ∀ x ∈ envelope_193,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_193 j := by decide +kernel
theorem envelope_exact_193 : envelope_193 =
    insert (1, 5) (Finset.univ.biUnion childrenD_193) := by
  exact envelope_eq_combination childrenD_193 (1, 5) envelope_193
    pivot_mem_193 child_envelope_sub_193 envelope_origin_193
def checked_193 : CheckedCard where
  required := required_193
  envelope := envelope_193
  height := height_193
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_193
def height_203 : ℕ := 6
def childrenH_203 : Fin 2 → ℕ := ![height_5, height_202]
theorem height_exact_203 : height_203 = 1 + Finset.univ.sup childrenH_203 := by decide +kernel
theorem required_origin_203 : ∀ x ∈ required_203,
    (∃ j, x ∈ childrenC_203 j) ∨ ∀ j, x ∈ childrenD_203 j := by decide +kernel
theorem required_exact_203 : required_203 =
    ((Finset.univ.biUnion childrenC_203) ∪ commonEnvelope childrenD_203).erase (1, 3) := by
  exact required_eq_combination childrenC_203 childrenD_203 (1, 3) required_203
    (by decide +kernel) child_required_sub_203 common_sub_203 required_origin_203
theorem envelope_origin_203 : ∀ x ∈ envelope_203,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_203 j := by decide +kernel
theorem envelope_exact_203 : envelope_203 =
    insert (1, 3) (Finset.univ.biUnion childrenD_203) := by
  exact envelope_eq_combination childrenD_203 (1, 3) envelope_203
    pivot_mem_203 child_envelope_sub_203 envelope_origin_203
def checked_203 : CheckedCard where
  required := required_203
  envelope := envelope_203
  height := height_203
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_203
def height_217 : ℕ := 6
def childrenH_217 : Fin 3 → ℕ := ![height_21, height_37, height_179]
theorem height_exact_217 : height_217 = 1 + Finset.univ.sup childrenH_217 := by decide +kernel
theorem required_origin_217 : ∀ x ∈ required_217,
    (∃ j, x ∈ childrenC_217 j) ∨ ∀ j, x ∈ childrenD_217 j := by decide +kernel
theorem required_exact_217 : required_217 =
    ((Finset.univ.biUnion childrenC_217) ∪ commonEnvelope childrenD_217).erase (2, 4) := by
  exact required_eq_combination childrenC_217 childrenD_217 (2, 4) required_217
    (by decide +kernel) child_required_sub_217 common_sub_217 required_origin_217
theorem envelope_origin_217 : ∀ x ∈ envelope_217,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_217 j := by decide +kernel
theorem envelope_exact_217 : envelope_217 =
    insert (2, 4) (Finset.univ.biUnion childrenD_217) := by
  exact envelope_eq_combination childrenD_217 (2, 4) envelope_217
    pivot_mem_217 child_envelope_sub_217 envelope_origin_217
def checked_217 : CheckedCard where
  required := required_217
  envelope := envelope_217
  height := height_217
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_217
def height_238 : ℕ := 6
def childrenH_238 : Fin 2 → ℕ := ![height_0, height_133]
theorem height_exact_238 : height_238 = 1 + Finset.univ.sup childrenH_238 := by decide +kernel
theorem required_origin_238 : ∀ x ∈ required_238,
    (∃ j, x ∈ childrenC_238 j) ∨ ∀ j, x ∈ childrenD_238 j := by decide +kernel
theorem required_exact_238 : required_238 =
    ((Finset.univ.biUnion childrenC_238) ∪ commonEnvelope childrenD_238).erase (2, 4) := by
  exact required_eq_combination childrenC_238 childrenD_238 (2, 4) required_238
    (by decide +kernel) child_required_sub_238 common_sub_238 required_origin_238
theorem envelope_origin_238 : ∀ x ∈ envelope_238,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_238 j := by decide +kernel
theorem envelope_exact_238 : envelope_238 =
    insert (2, 4) (Finset.univ.biUnion childrenD_238) := by
  exact envelope_eq_combination childrenD_238 (2, 4) envelope_238
    pivot_mem_238 child_envelope_sub_238 envelope_origin_238
def checked_238 : CheckedCard where
  required := required_238
  envelope := envelope_238
  height := height_238
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_238
def height_248 : ℕ := 6
def childrenH_248 : Fin 3 → ℕ := ![height_44, height_47, height_127]
theorem height_exact_248 : height_248 = 1 + Finset.univ.sup childrenH_248 := by decide +kernel
theorem required_origin_248 : ∀ x ∈ required_248,
    (∃ j, x ∈ childrenC_248 j) ∨ ∀ j, x ∈ childrenD_248 j := by decide +kernel
theorem required_exact_248 : required_248 =
    ((Finset.univ.biUnion childrenC_248) ∪ commonEnvelope childrenD_248).erase (2, 5) := by
  exact required_eq_combination childrenC_248 childrenD_248 (2, 5) required_248
    (by decide +kernel) child_required_sub_248 common_sub_248 required_origin_248
theorem envelope_origin_248 : ∀ x ∈ envelope_248,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_248 j := by decide +kernel
theorem envelope_exact_248 : envelope_248 =
    insert (2, 5) (Finset.univ.biUnion childrenD_248) := by
  exact envelope_eq_combination childrenD_248 (2, 5) envelope_248
    pivot_mem_248 child_envelope_sub_248 envelope_origin_248
def checked_248 : CheckedCard where
  required := required_248
  envelope := envelope_248
  height := height_248
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_248
def height_253 : ℕ := 6
def childrenH_253 : Fin 3 → ℕ := ![height_6, height_18, height_252]
theorem height_exact_253 : height_253 = 1 + Finset.univ.sup childrenH_253 := by decide +kernel
theorem required_origin_253 : ∀ x ∈ required_253,
    (∃ j, x ∈ childrenC_253 j) ∨ ∀ j, x ∈ childrenD_253 j := by decide +kernel
theorem required_exact_253 : required_253 =
    ((Finset.univ.biUnion childrenC_253) ∪ commonEnvelope childrenD_253).erase (4, 3) := by
  exact required_eq_combination childrenC_253 childrenD_253 (4, 3) required_253
    (by decide +kernel) child_required_sub_253 common_sub_253 required_origin_253
theorem envelope_origin_253 : ∀ x ∈ envelope_253,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_253 j := by decide +kernel
theorem envelope_exact_253 : envelope_253 =
    insert (4, 3) (Finset.univ.biUnion childrenD_253) := by
  exact envelope_eq_combination childrenD_253 (4, 3) envelope_253
    pivot_mem_253 child_envelope_sub_253 envelope_origin_253
def checked_253 : CheckedCard where
  required := required_253
  envelope := envelope_253
  height := height_253
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_253
def height_255 : ℕ := 6
def childrenH_255 : Fin 2 → ℕ := ![height_5, height_254]
theorem height_exact_255 : height_255 = 1 + Finset.univ.sup childrenH_255 := by decide +kernel
theorem required_origin_255 : ∀ x ∈ required_255,
    (∃ j, x ∈ childrenC_255 j) ∨ ∀ j, x ∈ childrenD_255 j := by decide +kernel
theorem required_exact_255 : required_255 =
    ((Finset.univ.biUnion childrenC_255) ∪ commonEnvelope childrenD_255).erase (3, 2) := by
  exact required_eq_combination childrenC_255 childrenD_255 (3, 2) required_255
    (by decide +kernel) child_required_sub_255 common_sub_255 required_origin_255
theorem envelope_origin_255 : ∀ x ∈ envelope_255,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_255 j := by decide +kernel
theorem envelope_exact_255 : envelope_255 =
    insert (3, 2) (Finset.univ.biUnion childrenD_255) := by
  exact envelope_eq_combination childrenD_255 (3, 2) envelope_255
    pivot_mem_255 child_envelope_sub_255 envelope_origin_255
def checked_255 : CheckedCard where
  required := required_255
  envelope := envelope_255
  height := height_255
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_255
def height_267 : ℕ := 6
def childrenH_267 : Fin 5 → ℕ := ![height_8, height_17, height_75, height_179, height_266]
theorem height_exact_267 : height_267 = 1 + Finset.univ.sup childrenH_267 := by decide +kernel
theorem required_origin_267 : ∀ x ∈ required_267,
    (∃ j, x ∈ childrenC_267 j) ∨ ∀ j, x ∈ childrenD_267 j := by decide +kernel
theorem required_exact_267 : required_267 =
    ((Finset.univ.biUnion childrenC_267) ∪ commonEnvelope childrenD_267).erase (2, 5) := by
  exact required_eq_combination childrenC_267 childrenD_267 (2, 5) required_267
    (by decide +kernel) child_required_sub_267 common_sub_267 required_origin_267
theorem envelope_origin_267 : ∀ x ∈ envelope_267,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_267 j := by decide +kernel
theorem envelope_exact_267 : envelope_267 =
    insert (2, 5) (Finset.univ.biUnion childrenD_267) := by
  exact envelope_eq_combination childrenD_267 (2, 5) envelope_267
    pivot_mem_267 child_envelope_sub_267 envelope_origin_267
def checked_267 : CheckedCard where
  required := required_267
  envelope := envelope_267
  height := height_267
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_267
def height_270 : ℕ := 6
def childrenH_270 : Fin 4 → ℕ := ![height_70, height_106, height_122, height_269]
theorem height_exact_270 : height_270 = 1 + Finset.univ.sup childrenH_270 := by decide +kernel
theorem required_origin_270 : ∀ x ∈ required_270,
    (∃ j, x ∈ childrenC_270 j) ∨ ∀ j, x ∈ childrenD_270 j := by decide +kernel
theorem required_exact_270 : required_270 =
    ((Finset.univ.biUnion childrenC_270) ∪ commonEnvelope childrenD_270).erase (4, 2) := by
  exact required_eq_combination childrenC_270 childrenD_270 (4, 2) required_270
    (by decide +kernel) child_required_sub_270 common_sub_270 required_origin_270
theorem envelope_origin_270 : ∀ x ∈ envelope_270,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_270 j := by decide +kernel
theorem envelope_exact_270 : envelope_270 =
    insert (4, 2) (Finset.univ.biUnion childrenD_270) := by
  exact envelope_eq_combination childrenD_270 (4, 2) envelope_270
    pivot_mem_270 child_envelope_sub_270 envelope_origin_270
def checked_270 : CheckedCard where
  required := required_270
  envelope := envelope_270
  height := height_270
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_270
def height_275 : ℕ := 6
def childrenH_275 : Fin 3 → ℕ := ![height_16, height_24, height_179]
theorem height_exact_275 : height_275 = 1 + Finset.univ.sup childrenH_275 := by decide +kernel
theorem required_origin_275 : ∀ x ∈ required_275,
    (∃ j, x ∈ childrenC_275 j) ∨ ∀ j, x ∈ childrenD_275 j := by decide +kernel
theorem required_exact_275 : required_275 =
    ((Finset.univ.biUnion childrenC_275) ∪ commonEnvelope childrenD_275).erase (4, 2) := by
  exact required_eq_combination childrenC_275 childrenD_275 (4, 2) required_275
    (by decide +kernel) child_required_sub_275 common_sub_275 required_origin_275
theorem envelope_origin_275 : ∀ x ∈ envelope_275,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_275 j := by decide +kernel
theorem envelope_exact_275 : envelope_275 =
    insert (4, 2) (Finset.univ.biUnion childrenD_275) := by
  exact envelope_eq_combination childrenD_275 (4, 2) envelope_275
    pivot_mem_275 child_envelope_sub_275 envelope_origin_275
def checked_275 : CheckedCard where
  required := required_275
  envelope := envelope_275
  height := height_275
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_275
def height_283 : ℕ := 6
def childrenH_283 : Fin 2 → ℕ := ![height_1, height_282]
theorem height_exact_283 : height_283 = 1 + Finset.univ.sup childrenH_283 := by decide +kernel
theorem required_origin_283 : ∀ x ∈ required_283,
    (∃ j, x ∈ childrenC_283 j) ∨ ∀ j, x ∈ childrenD_283 j := by decide +kernel
theorem required_exact_283 : required_283 =
    ((Finset.univ.biUnion childrenC_283) ∪ commonEnvelope childrenD_283).erase (2, 2) := by
  exact required_eq_combination childrenC_283 childrenD_283 (2, 2) required_283
    (by decide +kernel) child_required_sub_283 common_sub_283 required_origin_283
theorem envelope_origin_283 : ∀ x ∈ envelope_283,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_283 j := by decide +kernel
theorem envelope_exact_283 : envelope_283 =
    insert (2, 2) (Finset.univ.biUnion childrenD_283) := by
  exact envelope_eq_combination childrenD_283 (2, 2) envelope_283
    pivot_mem_283 child_envelope_sub_283 envelope_origin_283
def checked_283 : CheckedCard where
  required := required_283
  envelope := envelope_283
  height := height_283
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_283
def height_284 : ℕ := 6
def childrenH_284 : Fin 4 → ℕ := ![height_8, height_17, height_19, height_75]
theorem height_exact_284 : height_284 = 1 + Finset.univ.sup childrenH_284 := by decide +kernel
theorem required_origin_284 : ∀ x ∈ required_284,
    (∃ j, x ∈ childrenC_284 j) ∨ ∀ j, x ∈ childrenD_284 j := by decide +kernel
theorem required_exact_284 : required_284 =
    ((Finset.univ.biUnion childrenC_284) ∪ commonEnvelope childrenD_284).erase (1, 3) := by
  exact required_eq_combination childrenC_284 childrenD_284 (1, 3) required_284
    (by decide +kernel) child_required_sub_284 common_sub_284 required_origin_284
theorem envelope_origin_284 : ∀ x ∈ envelope_284,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_284 j := by decide +kernel
theorem envelope_exact_284 : envelope_284 =
    insert (1, 3) (Finset.univ.biUnion childrenD_284) := by
  exact envelope_eq_combination childrenD_284 (1, 3) envelope_284
    pivot_mem_284 child_envelope_sub_284 envelope_origin_284
def checked_284 : CheckedCard where
  required := required_284
  envelope := envelope_284
  height := height_284
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_284
def height_287 : ℕ := 6
def childrenH_287 : Fin 2 → ℕ := ![height_169, height_230]
theorem height_exact_287 : height_287 = 1 + Finset.univ.sup childrenH_287 := by decide +kernel
theorem required_origin_287 : ∀ x ∈ required_287,
    (∃ j, x ∈ childrenC_287 j) ∨ ∀ j, x ∈ childrenD_287 j := by decide +kernel
theorem required_exact_287 : required_287 =
    ((Finset.univ.biUnion childrenC_287) ∪ commonEnvelope childrenD_287).erase (1, 6) := by
  exact required_eq_combination childrenC_287 childrenD_287 (1, 6) required_287
    (by decide +kernel) child_required_sub_287 common_sub_287 required_origin_287
theorem envelope_origin_287 : ∀ x ∈ envelope_287,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_287 j := by decide +kernel
theorem envelope_exact_287 : envelope_287 =
    insert (1, 6) (Finset.univ.biUnion childrenD_287) := by
  exact envelope_eq_combination childrenD_287 (1, 6) envelope_287
    pivot_mem_287 child_envelope_sub_287 envelope_origin_287
def checked_287 : CheckedCard where
  required := required_287
  envelope := envelope_287
  height := height_287
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_287
def height_292 : ℕ := 6
def childrenH_292 : Fin 3 → ℕ := ![height_6, height_19, height_214]
theorem height_exact_292 : height_292 = 1 + Finset.univ.sup childrenH_292 := by decide +kernel
theorem required_origin_292 : ∀ x ∈ required_292,
    (∃ j, x ∈ childrenC_292 j) ∨ ∀ j, x ∈ childrenD_292 j := by decide +kernel
theorem required_exact_292 : required_292 =
    ((Finset.univ.biUnion childrenC_292) ∪ commonEnvelope childrenD_292).erase (4, 3) := by
  exact required_eq_combination childrenC_292 childrenD_292 (4, 3) required_292
    (by decide +kernel) child_required_sub_292 common_sub_292 required_origin_292
theorem envelope_origin_292 : ∀ x ∈ envelope_292,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_292 j := by decide +kernel
theorem envelope_exact_292 : envelope_292 =
    insert (4, 3) (Finset.univ.biUnion childrenD_292) := by
  exact envelope_eq_combination childrenD_292 (4, 3) envelope_292
    pivot_mem_292 child_envelope_sub_292 envelope_origin_292
def checked_292 : CheckedCard where
  required := required_292
  envelope := envelope_292
  height := height_292
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_292
def height_300 : ℕ := 6
def childrenH_300 : Fin 4 → ℕ := ![height_44, height_52, height_128, height_155]
theorem height_exact_300 : height_300 = 1 + Finset.univ.sup childrenH_300 := by decide +kernel
theorem required_origin_300 : ∀ x ∈ required_300,
    (∃ j, x ∈ childrenC_300 j) ∨ ∀ j, x ∈ childrenD_300 j := by decide +kernel
theorem required_exact_300 : required_300 =
    ((Finset.univ.biUnion childrenC_300) ∪ commonEnvelope childrenD_300).erase (2, 5) := by
  exact required_eq_combination childrenC_300 childrenD_300 (2, 5) required_300
    (by decide +kernel) child_required_sub_300 common_sub_300 required_origin_300
theorem envelope_origin_300 : ∀ x ∈ envelope_300,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_300 j := by decide +kernel
theorem envelope_exact_300 : envelope_300 =
    insert (2, 5) (Finset.univ.biUnion childrenD_300) := by
  exact envelope_eq_combination childrenD_300 (2, 5) envelope_300
    pivot_mem_300 child_envelope_sub_300 envelope_origin_300
def checked_300 : CheckedCard where
  required := required_300
  envelope := envelope_300
  height := height_300
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_300
def height_302 : ℕ := 6
def childrenH_302 : Fin 2 → ℕ := ![height_6, height_214]
theorem height_exact_302 : height_302 = 1 + Finset.univ.sup childrenH_302 := by decide +kernel
theorem required_origin_302 : ∀ x ∈ required_302,
    (∃ j, x ∈ childrenC_302 j) ∨ ∀ j, x ∈ childrenD_302 j := by decide +kernel
theorem required_exact_302 : required_302 =
    ((Finset.univ.biUnion childrenC_302) ∪ commonEnvelope childrenD_302).erase (5, 3) := by
  exact required_eq_combination childrenC_302 childrenD_302 (5, 3) required_302
    (by decide +kernel) child_required_sub_302 common_sub_302 required_origin_302
theorem envelope_origin_302 : ∀ x ∈ envelope_302,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_302 j := by decide +kernel
theorem envelope_exact_302 : envelope_302 =
    insert (5, 3) (Finset.univ.biUnion childrenD_302) := by
  exact envelope_eq_combination childrenD_302 (5, 3) envelope_302
    pivot_mem_302 child_envelope_sub_302 envelope_origin_302
def checked_302 : CheckedCard where
  required := required_302
  envelope := envelope_302
  height := height_302
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_302
def height_303 : ℕ := 6
def childrenH_303 : Fin 2 → ℕ := ![height_55, height_234]
theorem height_exact_303 : height_303 = 1 + Finset.univ.sup childrenH_303 := by decide +kernel
theorem required_origin_303 : ∀ x ∈ required_303,
    (∃ j, x ∈ childrenC_303 j) ∨ ∀ j, x ∈ childrenD_303 j := by decide +kernel
theorem required_exact_303 : required_303 =
    ((Finset.univ.biUnion childrenC_303) ∪ commonEnvelope childrenD_303).erase (3, 4) := by
  exact required_eq_combination childrenC_303 childrenD_303 (3, 4) required_303
    (by decide +kernel) child_required_sub_303 common_sub_303 required_origin_303
theorem envelope_origin_303 : ∀ x ∈ envelope_303,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_303 j := by decide +kernel
theorem envelope_exact_303 : envelope_303 =
    insert (3, 4) (Finset.univ.biUnion childrenD_303) := by
  exact envelope_eq_combination childrenD_303 (3, 4) envelope_303
    pivot_mem_303 child_envelope_sub_303 envelope_origin_303
def checked_303 : CheckedCard where
  required := required_303
  envelope := envelope_303
  height := height_303
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_303
def height_313 : ℕ := 6
def childrenH_313 : Fin 2 → ℕ := ![height_5, height_312]
theorem height_exact_313 : height_313 = 1 + Finset.univ.sup childrenH_313 := by decide +kernel
theorem required_origin_313 : ∀ x ∈ required_313,
    (∃ j, x ∈ childrenC_313 j) ∨ ∀ j, x ∈ childrenD_313 j := by decide +kernel
theorem required_exact_313 : required_313 =
    ((Finset.univ.biUnion childrenC_313) ∪ commonEnvelope childrenD_313).erase (3, 0) := by
  exact required_eq_combination childrenC_313 childrenD_313 (3, 0) required_313
    (by decide +kernel) child_required_sub_313 common_sub_313 required_origin_313
theorem envelope_origin_313 : ∀ x ∈ envelope_313,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_313 j := by decide +kernel
theorem envelope_exact_313 : envelope_313 =
    insert (3, 0) (Finset.univ.biUnion childrenD_313) := by
  exact envelope_eq_combination childrenD_313 (3, 0) envelope_313
    pivot_mem_313 child_envelope_sub_313 envelope_origin_313
def checked_313 : CheckedCard where
  required := required_313
  envelope := envelope_313
  height := height_313
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_313
def height_315 : ℕ := 6
def childrenH_315 : Fin 2 → ℕ := ![height_5, height_314]
theorem height_exact_315 : height_315 = 1 + Finset.univ.sup childrenH_315 := by decide +kernel
theorem required_origin_315 : ∀ x ∈ required_315,
    (∃ j, x ∈ childrenC_315 j) ∨ ∀ j, x ∈ childrenD_315 j := by decide +kernel
theorem required_exact_315 : required_315 =
    ((Finset.univ.biUnion childrenC_315) ∪ commonEnvelope childrenD_315).erase (1, 4) := by
  exact required_eq_combination childrenC_315 childrenD_315 (1, 4) required_315
    (by decide +kernel) child_required_sub_315 common_sub_315 required_origin_315
theorem envelope_origin_315 : ∀ x ∈ envelope_315,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_315 j := by decide +kernel
theorem envelope_exact_315 : envelope_315 =
    insert (1, 4) (Finset.univ.biUnion childrenD_315) := by
  exact envelope_eq_combination childrenD_315 (1, 4) envelope_315
    pivot_mem_315 child_envelope_sub_315 envelope_origin_315
def checked_315 : CheckedCard where
  required := required_315
  envelope := envelope_315
  height := height_315
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_315
def height_316 : ℕ := 6
def childrenH_316 : Fin 2 → ℕ := ![height_8, height_314]
theorem height_exact_316 : height_316 = 1 + Finset.univ.sup childrenH_316 := by decide +kernel
theorem required_origin_316 : ∀ x ∈ required_316,
    (∃ j, x ∈ childrenC_316 j) ∨ ∀ j, x ∈ childrenD_316 j := by decide +kernel
theorem required_exact_316 : required_316 =
    ((Finset.univ.biUnion childrenC_316) ∪ commonEnvelope childrenD_316).erase (1, 2) := by
  exact required_eq_combination childrenC_316 childrenD_316 (1, 2) required_316
    (by decide +kernel) child_required_sub_316 common_sub_316 required_origin_316
theorem envelope_origin_316 : ∀ x ∈ envelope_316,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_316 j := by decide +kernel
theorem envelope_exact_316 : envelope_316 =
    insert (1, 2) (Finset.univ.biUnion childrenD_316) := by
  exact envelope_eq_combination childrenD_316 (1, 2) envelope_316
    pivot_mem_316 child_envelope_sub_316 envelope_origin_316
def checked_316 : CheckedCard where
  required := required_316
  envelope := envelope_316
  height := height_316
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_316
def height_331_i1 : ℕ := 4
def childrenH_331_i1 : Fin 2 → ℕ := ![height_20, height_29]
theorem height_exact_331_i1 : height_331_i1 = 1 + Finset.univ.sup childrenH_331_i1 := by decide +kernel
theorem required_origin_331_i1 : ∀ x ∈ required_331_i1,
    (∃ j, x ∈ childrenC_331_i1 j) ∨ ∀ j, x ∈ childrenD_331_i1 j := by decide +kernel
theorem required_exact_331_i1 : required_331_i1 =
    ((Finset.univ.biUnion childrenC_331_i1) ∪ commonEnvelope childrenD_331_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_331_i1 childrenD_331_i1 (3, 5) required_331_i1
    (by decide +kernel) child_required_sub_331_i1 common_sub_331_i1 required_origin_331_i1
theorem envelope_origin_331_i1 : ∀ x ∈ envelope_331_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_331_i1 j := by decide +kernel
theorem envelope_exact_331_i1 : envelope_331_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_331_i1) := by
  exact envelope_eq_combination childrenD_331_i1 (3, 5) envelope_331_i1
    pivot_mem_331_i1 child_envelope_sub_331_i1 envelope_origin_331_i1
def checked_331_i1 : CheckedCard where
  required := required_331_i1
  envelope := envelope_331_i1
  height := height_331_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_331_i1
def height_331_i0 : ℕ := 5
def childrenH_331_i0 : Fin 2 → ℕ := ![height_5, height_331_i1]
theorem height_exact_331_i0 : height_331_i0 = 1 + Finset.univ.sup childrenH_331_i0 := by decide +kernel
theorem required_origin_331_i0 : ∀ x ∈ required_331_i0,
    (∃ j, x ∈ childrenC_331_i0 j) ∨ ∀ j, x ∈ childrenD_331_i0 j := by decide +kernel
theorem required_exact_331_i0 : required_331_i0 =
    ((Finset.univ.biUnion childrenC_331_i0) ∪ commonEnvelope childrenD_331_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_331_i0 childrenD_331_i0 (3, 2) required_331_i0
    (by decide +kernel) child_required_sub_331_i0 common_sub_331_i0 required_origin_331_i0
theorem envelope_origin_331_i0 : ∀ x ∈ envelope_331_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_331_i0 j := by decide +kernel
theorem envelope_exact_331_i0 : envelope_331_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_331_i0) := by
  exact envelope_eq_combination childrenD_331_i0 (3, 2) envelope_331_i0
    pivot_mem_331_i0 child_envelope_sub_331_i0 envelope_origin_331_i0
def checked_331_i0 : CheckedCard where
  required := required_331_i0
  envelope := envelope_331_i0
  height := height_331_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_331_i0
def height_331 : ℕ := 6
def childrenH_331 : Fin 2 → ℕ := ![height_5, height_331_i0]
theorem height_exact_331 : height_331 = 1 + Finset.univ.sup childrenH_331 := by decide +kernel
theorem required_origin_331 : ∀ x ∈ required_331,
    (∃ j, x ∈ childrenC_331 j) ∨ ∀ j, x ∈ childrenD_331 j := by decide +kernel
theorem required_exact_331 : required_331 =
    ((Finset.univ.biUnion childrenC_331) ∪ commonEnvelope childrenD_331).erase (3, 4) := by
  exact required_eq_combination childrenC_331 childrenD_331 (3, 4) required_331
    (by decide +kernel) child_required_sub_331 common_sub_331 required_origin_331
theorem envelope_origin_331 : ∀ x ∈ envelope_331,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_331 j := by decide +kernel
theorem envelope_exact_331 : envelope_331 =
    insert (3, 4) (Finset.univ.biUnion childrenD_331) := by
  exact envelope_eq_combination childrenD_331 (3, 4) envelope_331
    pivot_mem_331 child_envelope_sub_331 envelope_origin_331
def checked_331 : CheckedCard where
  required := required_331
  envelope := envelope_331
  height := height_331
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_331
end SnakyPrototype.Certificate21

end OAI
