import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_120 : Finset Cell := ⟨(([(1, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_120 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_120 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_44), (placed21 3 (0, 3) required_52), required_116]
def childrenD_120 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_44), (placed21 3 (0, 3) envelope_52), envelope_116]
theorem common_sub_120 : commonEnvelope childrenD_120 ⊆ insert (2, 3) required_120 := by decide +kernel
theorem child_required_sub_120 : ∀ j, childrenC_120 j ⊆ insert (2, 3) required_120 := by decide +kernel
theorem child_envelope_sub_120 : ∀ j, childrenD_120 j ⊆ envelope_120 := by decide +kernel
theorem pivot_mem_120 : (2, 3) ∈ envelope_120 := by decide +kernel
theorem children_work_120 : ∀ j, Template HasSnaky 7 (childrenC_120 j) (childrenD_120 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 3 (0, 3)).mono (by decide +kernel)
  · exact row_works_116.mono (by decide +kernel)
theorem row_works_120 : Template HasSnaky 8 required_120 envelope_120 := by
  refine compose HasSnaky 7 childrenC_120 childrenD_120 children_work_120 (2, 3)
    required_120 envelope_120 pivot_mem_120 child_required_sub_120 child_envelope_sub_120 ?_
  intro b hb
  exact common_sub_120 (mem_commonEnvelope childrenD_120 b hb)
def required_171 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_171 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_171 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_6), (placed21 4 (1, 4) required_26), (placed21 0 (1, 0) required_116)]
def childrenD_171 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_6), (placed21 4 (1, 4) envelope_26), (placed21 0 (1, 0) envelope_116)]
theorem common_sub_171 : commonEnvelope childrenD_171 ⊆ insert (4, 3) required_171 := by decide +kernel
theorem child_required_sub_171 : ∀ j, childrenC_171 j ⊆ insert (4, 3) required_171 := by decide +kernel
theorem child_envelope_sub_171 : ∀ j, childrenD_171 j ⊆ envelope_171 := by decide +kernel
theorem pivot_mem_171 : (4, 3) ∈ envelope_171 := by decide +kernel
theorem children_work_171 : ∀ j, Template HasSnaky 7 (childrenC_171 j) (childrenD_171 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 4 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_116 0 (1, 0)).mono (by decide +kernel)
theorem row_works_171 : Template HasSnaky 8 required_171 envelope_171 := by
  refine compose HasSnaky 7 childrenC_171 childrenD_171 children_work_171 (4, 3)
    required_171 envelope_171 pivot_mem_171 child_required_sub_171 child_envelope_sub_171 ?_
  intro b hb
  exact common_sub_171 (mem_commonEnvelope childrenD_171 b hb)
def required_174 : Finset Cell := ⟨(([(3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_174 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_174 : Fin 6 → Finset Cell := ![(placed21 1 (0, 2) required_116), (placed21 3 (0, 6) required_117), (placed21 0 (1, 1) required_135), (placed21 6 (5, 7) required_135), (placed21 3 (0, 6) required_173), (placed21 5 (6, 2) required_173)]
def childrenD_174 : Fin 6 → Finset Cell := ![(placed21 1 (0, 2) envelope_116), (placed21 3 (0, 6) envelope_117), (placed21 0 (1, 1) envelope_135), (placed21 6 (5, 7) envelope_135), (placed21 3 (0, 6) envelope_173), (placed21 5 (6, 2) envelope_173)]
theorem common_sub_174 : commonEnvelope childrenD_174 ⊆ insert (3, 5) required_174 := by decide +kernel
theorem child_required_sub_174 : ∀ j, childrenC_174 j ⊆ insert (3, 5) required_174 := by decide +kernel
theorem child_envelope_sub_174 : ∀ j, childrenD_174 j ⊆ envelope_174 := by decide +kernel
theorem pivot_mem_174 : (3, 5) ∈ envelope_174 := by decide +kernel
theorem children_work_174 : ∀ j, Template HasSnaky 7 (childrenC_174 j) (childrenD_174 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_116 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_117 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_135 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_135 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_173 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_173 5 (6, 2)).mono (by decide +kernel)
theorem row_works_174 : Template HasSnaky 8 required_174 envelope_174 := by
  refine compose HasSnaky 7 childrenC_174 childrenD_174 children_work_174 (3, 5)
    required_174 envelope_174 pivot_mem_174 child_required_sub_174 child_envelope_sub_174 ?_
  intro b hb
  exact common_sub_174 (mem_commonEnvelope childrenD_174 b hb)
def required_257 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_257 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_257 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) required_7), (placed21 3 (0, 4) required_9), (placed21 0 (1, 0) required_256)]
def childrenD_257 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) envelope_7), (placed21 3 (0, 4) envelope_9), (placed21 0 (1, 0) envelope_256)]
theorem common_sub_257 : commonEnvelope childrenD_257 ⊆ insert (4, 3) required_257 := by decide +kernel
theorem child_required_sub_257 : ∀ j, childrenC_257 j ⊆ insert (4, 3) required_257 := by decide +kernel
theorem child_envelope_sub_257 : ∀ j, childrenD_257 j ⊆ envelope_257 := by decide +kernel
theorem pivot_mem_257 : (4, 3) ∈ envelope_257 := by decide +kernel
theorem children_work_257 : ∀ j, Template HasSnaky 7 (childrenC_257 j) (childrenD_257 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_256 0 (1, 0)).mono (by decide +kernel)
theorem row_works_257 : Template HasSnaky 8 required_257 envelope_257 := by
  refine compose HasSnaky 7 childrenC_257 childrenD_257 children_work_257 (4, 3)
    required_257 envelope_257 pivot_mem_257 child_required_sub_257 child_envelope_sub_257 ?_
  intro b hb
  exact common_sub_257 (mem_commonEnvelope childrenD_257 b hb)
def required_258 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_258 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_258 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) required_8), (placed21 4 (0, 6) required_161), (placed21 4 (0, 6) required_162), required_256]
def childrenD_258 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) envelope_8), (placed21 4 (0, 6) envelope_161), (placed21 4 (0, 6) envelope_162), envelope_256]
theorem common_sub_258 : commonEnvelope childrenD_258 ⊆ insert (3, 3) required_258 := by decide +kernel
theorem child_required_sub_258 : ∀ j, childrenC_258 j ⊆ insert (3, 3) required_258 := by decide +kernel
theorem child_envelope_sub_258 : ∀ j, childrenD_258 j ⊆ envelope_258 := by decide +kernel
theorem pivot_mem_258 : (3, 3) ∈ envelope_258 := by decide +kernel
theorem children_work_258 : ∀ j, Template HasSnaky 7 (childrenC_258 j) (childrenD_258 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_161 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_162 4 (0, 6)).mono (by decide +kernel)
  · exact row_works_256.mono (by decide +kernel)
theorem row_works_258 : Template HasSnaky 8 required_258 envelope_258 := by
  refine compose HasSnaky 7 childrenC_258 childrenD_258 children_work_258 (3, 3)
    required_258 envelope_258 pivot_mem_258 child_required_sub_258 child_envelope_sub_258 ?_
  intro b hb
  exact common_sub_258 (mem_commonEnvelope childrenD_258 b hb)
def required_285 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_285 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_285 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) required_6), (placed21 0 (1, 2) required_26), (placed21 0 (1, 0) required_117)]
def childrenD_285 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) envelope_6), (placed21 0 (1, 2) envelope_26), (placed21 0 (1, 0) envelope_117)]
theorem common_sub_285 : commonEnvelope childrenD_285 ⊆ insert (4, 3) required_285 := by decide +kernel
theorem child_required_sub_285 : ∀ j, childrenC_285 j ⊆ insert (4, 3) required_285 := by decide +kernel
theorem child_envelope_sub_285 : ∀ j, childrenD_285 j ⊆ envelope_285 := by decide +kernel
theorem pivot_mem_285 : (4, 3) ∈ envelope_285 := by decide +kernel
theorem children_work_285 : ∀ j, Template HasSnaky 7 (childrenC_285 j) (childrenD_285 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_117 0 (1, 0)).mono (by decide +kernel)
theorem row_works_285 : Template HasSnaky 8 required_285 envelope_285 := by
  refine compose HasSnaky 7 childrenC_285 childrenD_285 children_work_285 (4, 3)
    required_285 envelope_285 pivot_mem_285 child_required_sub_285 child_envelope_sub_285 ?_
  intro b hb
  exact common_sub_285 (mem_commonEnvelope childrenD_285 b hb)
def required_319 : Finset Cell := ⟨(([(1, 5), (2, 3), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_319 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_319 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_52), (placed21 0 (2, 0) required_318)]
def childrenD_319 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_52), (placed21 0 (2, 0) envelope_318)]
theorem common_sub_319 : commonEnvelope childrenD_319 ⊆ insert (3, 4) required_319 := by decide +kernel
theorem child_required_sub_319 : ∀ j, childrenC_319 j ⊆ insert (3, 4) required_319 := by decide +kernel
theorem child_envelope_sub_319 : ∀ j, childrenD_319 j ⊆ envelope_319 := by decide +kernel
theorem pivot_mem_319 : (3, 4) ∈ envelope_319 := by decide +kernel
theorem children_work_319 : ∀ j, Template HasSnaky 7 (childrenC_319 j) (childrenD_319 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_318 0 (2, 0)).mono (by decide +kernel)
theorem row_works_319 : Template HasSnaky 8 required_319 envelope_319 := by
  refine compose HasSnaky 7 childrenC_319 childrenD_319 children_work_319 (3, 4)
    required_319 envelope_319 pivot_mem_319 child_required_sub_319 child_envelope_sub_319 ?_
  intro b hb
  exact common_sub_319 (mem_commonEnvelope childrenD_319 b hb)
def required_321 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_321 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_321 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) required_5), required_320]
def childrenD_321 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) envelope_5), envelope_320]
theorem common_sub_321 : commonEnvelope childrenD_321 ⊆ insert (3, 3) required_321 := by decide +kernel
theorem child_required_sub_321 : ∀ j, childrenC_321 j ⊆ insert (3, 3) required_321 := by decide +kernel
theorem child_envelope_sub_321 : ∀ j, childrenD_321 j ⊆ envelope_321 := by decide +kernel
theorem pivot_mem_321 : (3, 3) ∈ envelope_321 := by decide +kernel
theorem children_work_321 : ∀ j, Template HasSnaky 7 (childrenC_321 j) (childrenD_321 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 4)).mono (by decide +kernel)
  · exact row_works_320.mono (by decide +kernel)
theorem row_works_321 : Template HasSnaky 8 required_321 envelope_321 := by
  refine compose HasSnaky 7 childrenC_321 childrenD_321 children_work_321 (3, 3)
    required_321 envelope_321 pivot_mem_321 child_required_sub_321 child_envelope_sub_321 ?_
  intro b hb
  exact common_sub_321 (mem_commonEnvelope childrenD_321 b hb)
def required_323 : Finset Cell := ⟨(([(1, 3), (1, 4), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_323 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (4, 3), (4, 4), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_323 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) required_11), (placed21 2 (4, 0) required_320)]
def childrenD_323 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) envelope_11), (placed21 2 (4, 0) envelope_320)]
theorem common_sub_323 : commonEnvelope childrenD_323 ⊆ insert (2, 4) required_323 := by decide +kernel
theorem child_required_sub_323 : ∀ j, childrenC_323 j ⊆ insert (2, 4) required_323 := by decide +kernel
theorem child_envelope_sub_323 : ∀ j, childrenD_323 j ⊆ envelope_323 := by decide +kernel
theorem pivot_mem_323 : (2, 4) ∈ envelope_323 := by decide +kernel
theorem children_work_323 : ∀ j, Template HasSnaky 7 (childrenC_323 j) (childrenD_323 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 7 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_320 2 (4, 0)).mono (by decide +kernel)
theorem row_works_323 : Template HasSnaky 8 required_323 envelope_323 := by
  refine compose HasSnaky 7 childrenC_323 childrenD_323 children_work_323 (2, 4)
    required_323 envelope_323 pivot_mem_323 child_required_sub_323 child_envelope_sub_323 ?_
  intro b hb
  exact common_sub_323 (mem_commonEnvelope childrenD_323 b hb)
def required_338 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_338 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_338 : Fin 3 → Finset Cell := ![(placed21 6 (2, 6) required_44), (placed21 3 (0, 6) required_47), (placed21 0 (1, 0) required_337)]
def childrenD_338 : Fin 3 → Finset Cell := ![(placed21 6 (2, 6) envelope_44), (placed21 3 (0, 6) envelope_47), (placed21 0 (1, 0) envelope_337)]
theorem common_sub_338 : commonEnvelope childrenD_338 ⊆ insert (2, 4) required_338 := by decide +kernel
theorem child_required_sub_338 : ∀ j, childrenC_338 j ⊆ insert (2, 4) required_338 := by decide +kernel
theorem child_envelope_sub_338 : ∀ j, childrenD_338 j ⊆ envelope_338 := by decide +kernel
theorem pivot_mem_338 : (2, 4) ∈ envelope_338 := by decide +kernel
theorem children_work_338 : ∀ j, Template HasSnaky 7 (childrenC_338 j) (childrenD_338 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_337 0 (1, 0)).mono (by decide +kernel)
theorem row_works_338 : Template HasSnaky 8 required_338 envelope_338 := by
  refine compose HasSnaky 7 childrenC_338 childrenD_338 children_work_338 (2, 4)
    required_338 envelope_338 pivot_mem_338 child_required_sub_338 child_envelope_sub_338 ?_
  intro b hb
  exact common_sub_338 (mem_commonEnvelope childrenD_338 b hb)
def required_345 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_345 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_345 : Fin 3 → Finset Cell := ![(placed21 0 (1, 1) required_8), (placed21 1 (0, 2) required_11), required_344]
def childrenD_345 : Fin 3 → Finset Cell := ![(placed21 0 (1, 1) envelope_8), (placed21 1 (0, 2) envelope_11), envelope_344]
theorem common_sub_345 : commonEnvelope childrenD_345 ⊆ insert (4, 2) required_345 := by decide +kernel
theorem child_required_sub_345 : ∀ j, childrenC_345 j ⊆ insert (4, 2) required_345 := by decide +kernel
theorem child_envelope_sub_345 : ∀ j, childrenD_345 j ⊆ envelope_345 := by decide +kernel
theorem pivot_mem_345 : (4, 2) ∈ envelope_345 := by decide +kernel
theorem children_work_345 : ∀ j, Template HasSnaky 7 (childrenC_345 j) (childrenD_345 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_344.mono (by decide +kernel)
theorem row_works_345 : Template HasSnaky 8 required_345 envelope_345 := by
  refine compose HasSnaky 7 childrenC_345 childrenD_345 children_work_345 (4, 2)
    required_345 envelope_345 pivot_mem_345 child_required_sub_345 child_envelope_sub_345 ?_
  intro b hb
  exact common_sub_345 (mem_commonEnvelope childrenD_345 b hb)
def required_373 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_373 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (6, 0), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_373 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), required_372]
def childrenD_373 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), envelope_372]
theorem common_sub_373 : commonEnvelope childrenD_373 ⊆ insert (1, 4) required_373 := by decide +kernel
theorem child_required_sub_373 : ∀ j, childrenC_373 j ⊆ insert (1, 4) required_373 := by decide +kernel
theorem child_envelope_sub_373 : ∀ j, childrenD_373 j ⊆ envelope_373 := by decide +kernel
theorem pivot_mem_373 : (1, 4) ∈ envelope_373 := by decide +kernel
theorem children_work_373 : ∀ j, Template HasSnaky 7 (childrenC_373 j) (childrenD_373 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_372.mono (by decide +kernel)
theorem row_works_373 : Template HasSnaky 8 required_373 envelope_373 := by
  refine compose HasSnaky 7 childrenC_373 childrenD_373 children_work_373 (1, 4)
    required_373 envelope_373 pivot_mem_373 child_required_sub_373 child_envelope_sub_373 ?_
  intro b hb
  exact common_sub_373 (mem_commonEnvelope childrenD_373 b hb)
def required_395_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_395_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 4), (4, 5), (4, 6), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_395_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), (placed21 0 (1, 0) required_217)]
def childrenD_395_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), (placed21 0 (1, 0) envelope_217)]
theorem common_sub_395_i0 : commonEnvelope childrenD_395_i0 ⊆ insert (3, 1) required_395_i0 := by decide +kernel
theorem child_required_sub_395_i0 : ∀ j, childrenC_395_i0 j ⊆ insert (3, 1) required_395_i0 := by decide +kernel
theorem child_envelope_sub_395_i0 : ∀ j, childrenD_395_i0 j ⊆ envelope_395_i0 := by decide +kernel
theorem pivot_mem_395_i0 : (3, 1) ∈ envelope_395_i0 := by decide +kernel
theorem children_work_395_i0 : ∀ j, Template HasSnaky 6 (childrenC_395_i0 j) (childrenD_395_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_217 0 (1, 0)).mono (by decide +kernel)
theorem row_works_395_i0 : Template HasSnaky 7 required_395_i0 envelope_395_i0 := by
  refine compose HasSnaky 6 childrenC_395_i0 childrenD_395_i0 children_work_395_i0 (3, 1)
    required_395_i0 envelope_395_i0 pivot_mem_395_i0 child_required_sub_395_i0 child_envelope_sub_395_i0 ?_
  intro b hb
  exact common_sub_395_i0 (mem_commonEnvelope childrenD_395_i0 b hb)
def required_395 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_395 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_395 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), required_395_i0]
def childrenD_395 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), envelope_395_i0]
theorem common_sub_395 : commonEnvelope childrenD_395 ⊆ insert (3, 3) required_395 := by decide +kernel
theorem child_required_sub_395 : ∀ j, childrenC_395 j ⊆ insert (3, 3) required_395 := by decide +kernel
theorem child_envelope_sub_395 : ∀ j, childrenD_395 j ⊆ envelope_395 := by decide +kernel
theorem pivot_mem_395 : (3, 3) ∈ envelope_395 := by decide +kernel
theorem children_work_395 : ∀ j, Template HasSnaky 7 (childrenC_395 j) (childrenD_395 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_395_i0.mono (by decide +kernel)
theorem row_works_395 : Template HasSnaky 8 required_395 envelope_395 := by
  refine compose HasSnaky 7 childrenC_395 childrenD_395 children_work_395 (3, 3)
    required_395 envelope_395 pivot_mem_395 child_required_sub_395 child_envelope_sub_395 ?_
  intro b hb
  exact common_sub_395 (mem_commonEnvelope childrenD_395 b hb)
def required_405 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_405 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_405 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), required_404]
def childrenD_405 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), envelope_404]
theorem common_sub_405 : commonEnvelope childrenD_405 ⊆ insert (1, 4) required_405 := by decide +kernel
theorem child_required_sub_405 : ∀ j, childrenC_405 j ⊆ insert (1, 4) required_405 := by decide +kernel
theorem child_envelope_sub_405 : ∀ j, childrenD_405 j ⊆ envelope_405 := by decide +kernel
theorem pivot_mem_405 : (1, 4) ∈ envelope_405 := by decide +kernel
theorem children_work_405 : ∀ j, Template HasSnaky 7 (childrenC_405 j) (childrenD_405 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact row_works_404.mono (by decide +kernel)
theorem row_works_405 : Template HasSnaky 8 required_405 envelope_405 := by
  refine compose HasSnaky 7 childrenC_405 childrenD_405 children_work_405 (1, 4)
    required_405 envelope_405 pivot_mem_405 child_required_sub_405 child_envelope_sub_405 ?_
  intro b hb
  exact common_sub_405 (mem_commonEnvelope childrenD_405 b hb)
def required_412_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_412_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_412_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), required_358]
def childrenD_412_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), envelope_358]
theorem common_sub_412_i0 : commonEnvelope childrenD_412_i0 ⊆ insert (3, 1) required_412_i0 := by decide +kernel
theorem child_required_sub_412_i0 : ∀ j, childrenC_412_i0 j ⊆ insert (3, 1) required_412_i0 := by decide +kernel
theorem child_envelope_sub_412_i0 : ∀ j, childrenD_412_i0 j ⊆ envelope_412_i0 := by decide +kernel
theorem pivot_mem_412_i0 : (3, 1) ∈ envelope_412_i0 := by decide +kernel
theorem children_work_412_i0 : ∀ j, Template HasSnaky 6 (childrenC_412_i0 j) (childrenD_412_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact row_works_358.mono (by decide +kernel)
theorem row_works_412_i0 : Template HasSnaky 7 required_412_i0 envelope_412_i0 := by
  refine compose HasSnaky 6 childrenC_412_i0 childrenD_412_i0 children_work_412_i0 (3, 1)
    required_412_i0 envelope_412_i0 pivot_mem_412_i0 child_required_sub_412_i0 child_envelope_sub_412_i0 ?_
  intro b hb
  exact common_sub_412_i0 (mem_commonEnvelope childrenD_412_i0 b hb)
def required_412 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_412 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_412 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), required_412_i0]
def childrenD_412 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), envelope_412_i0]
theorem common_sub_412 : commonEnvelope childrenD_412 ⊆ insert (2, 1) required_412 := by decide +kernel
theorem child_required_sub_412 : ∀ j, childrenC_412 j ⊆ insert (2, 1) required_412 := by decide +kernel
theorem child_envelope_sub_412 : ∀ j, childrenD_412 j ⊆ envelope_412 := by decide +kernel
theorem pivot_mem_412 : (2, 1) ∈ envelope_412 := by decide +kernel
theorem children_work_412 : ∀ j, Template HasSnaky 7 (childrenC_412 j) (childrenD_412 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_412_i0.mono (by decide +kernel)
theorem row_works_412 : Template HasSnaky 8 required_412 envelope_412 := by
  refine compose HasSnaky 7 childrenC_412 childrenD_412 children_work_412 (2, 1)
    required_412 envelope_412 pivot_mem_412 child_required_sub_412 child_envelope_sub_412 ?_
  intro b hb
  exact common_sub_412 (mem_commonEnvelope childrenD_412 b hb)
def required_419 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_419 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_419 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 1 (0, 1) required_418)]
def childrenD_419 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_418)]
theorem common_sub_419 : commonEnvelope childrenD_419 ⊆ insert (2, 1) required_419 := by decide +kernel
theorem child_required_sub_419 : ∀ j, childrenC_419 j ⊆ insert (2, 1) required_419 := by decide +kernel
theorem child_envelope_sub_419 : ∀ j, childrenD_419 j ⊆ envelope_419 := by decide +kernel
theorem pivot_mem_419 : (2, 1) ∈ envelope_419 := by decide +kernel
theorem children_work_419 : ∀ j, Template HasSnaky 7 (childrenC_419 j) (childrenD_419 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_418 1 (0, 1)).mono (by decide +kernel)
theorem row_works_419 : Template HasSnaky 8 required_419 envelope_419 := by
  refine compose HasSnaky 7 childrenC_419 childrenD_419 children_work_419 (2, 1)
    required_419 envelope_419 pivot_mem_419 child_required_sub_419 child_envelope_sub_419 ?_
  intro b hb
  exact common_sub_419 (mem_commonEnvelope childrenD_419 b hb)
def required_420 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_420 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_420 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), required_418]
def childrenD_420 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), envelope_418]
theorem common_sub_420 : commonEnvelope childrenD_420 ⊆ insert (3, 1) required_420 := by decide +kernel
theorem child_required_sub_420 : ∀ j, childrenC_420 j ⊆ insert (3, 1) required_420 := by decide +kernel
theorem child_envelope_sub_420 : ∀ j, childrenD_420 j ⊆ envelope_420 := by decide +kernel
theorem pivot_mem_420 : (3, 1) ∈ envelope_420 := by decide +kernel
theorem children_work_420 : ∀ j, Template HasSnaky 7 (childrenC_420 j) (childrenD_420 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact row_works_418.mono (by decide +kernel)
theorem row_works_420 : Template HasSnaky 8 required_420 envelope_420 := by
  refine compose HasSnaky 7 childrenC_420 childrenD_420 children_work_420 (3, 1)
    required_420 envelope_420 pivot_mem_420 child_required_sub_420 child_envelope_sub_420 ?_
  intro b hb
  exact common_sub_420 (mem_commonEnvelope childrenD_420 b hb)
def required_438 : Finset Cell := ⟨(([(3, 3), (3, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_438 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 2), (7, 4), (7, 6), (8, 2), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_438 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) required_10), (placed21 6 (6, 5) required_47), (placed21 0 (2, 0) required_436)]
def childrenD_438 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) envelope_10), (placed21 6 (6, 5) envelope_47), (placed21 0 (2, 0) envelope_436)]
theorem common_sub_438 : commonEnvelope childrenD_438 ⊆ insert (4, 3) required_438 := by decide +kernel
theorem child_required_sub_438 : ∀ j, childrenC_438 j ⊆ insert (4, 3) required_438 := by decide +kernel
theorem child_envelope_sub_438 : ∀ j, childrenD_438 j ⊆ envelope_438 := by decide +kernel
theorem pivot_mem_438 : (4, 3) ∈ envelope_438 := by decide +kernel
theorem children_work_438 : ∀ j, Template HasSnaky 7 (childrenC_438 j) (childrenD_438 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 7 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 6 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_436 0 (2, 0)).mono (by decide +kernel)
theorem row_works_438 : Template HasSnaky 8 required_438 envelope_438 := by
  refine compose HasSnaky 7 childrenC_438 childrenD_438 children_work_438 (4, 3)
    required_438 envelope_438 pivot_mem_438 child_required_sub_438 child_envelope_sub_438 ?_
  intro b hb
  exact common_sub_438 (mem_commonEnvelope childrenD_438 b hb)
def required_440_i0 : Finset Cell := ⟨(([(0, 1), (1, 2), (1, 3), (1, 4), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_440_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_440_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 7 (5, 4) required_439)]
def childrenD_440_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 7 (5, 4) envelope_439)]
theorem common_sub_440_i0 : commonEnvelope childrenD_440_i0 ⊆ insert (1, 1) required_440_i0 := by decide +kernel
theorem child_required_sub_440_i0 : ∀ j, childrenC_440_i0 j ⊆ insert (1, 1) required_440_i0 := by decide +kernel
theorem child_envelope_sub_440_i0 : ∀ j, childrenD_440_i0 j ⊆ envelope_440_i0 := by decide +kernel
theorem pivot_mem_440_i0 : (1, 1) ∈ envelope_440_i0 := by decide +kernel
theorem children_work_440_i0 : ∀ j, Template HasSnaky 6 (childrenC_440_i0 j) (childrenD_440_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_439 7 (5, 4)).mono (by decide +kernel)
theorem row_works_440_i0 : Template HasSnaky 7 required_440_i0 envelope_440_i0 := by
  refine compose HasSnaky 6 childrenC_440_i0 childrenD_440_i0 children_work_440_i0 (1, 1)
    required_440_i0 envelope_440_i0 pivot_mem_440_i0 child_required_sub_440_i0 child_envelope_sub_440_i0 ?_
  intro b hb
  exact common_sub_440_i0 (mem_commonEnvelope childrenD_440_i0 b hb)
def required_440 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_440 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_440 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_18), required_440_i0]
def childrenD_440 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_18), envelope_440_i0]
theorem common_sub_440 : commonEnvelope childrenD_440 ⊆ insert (0, 1) required_440 := by decide +kernel
theorem child_required_sub_440 : ∀ j, childrenC_440 j ⊆ insert (0, 1) required_440 := by decide +kernel
theorem child_envelope_sub_440 : ∀ j, childrenD_440 j ⊆ envelope_440 := by decide +kernel
theorem pivot_mem_440 : (0, 1) ∈ envelope_440 := by decide +kernel
theorem children_work_440 : ∀ j, Template HasSnaky 7 (childrenC_440 j) (childrenD_440 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_440_i0.mono (by decide +kernel)
theorem row_works_440 : Template HasSnaky 8 required_440 envelope_440 := by
  refine compose HasSnaky 7 childrenC_440 childrenD_440 children_work_440 (0, 1)
    required_440 envelope_440 pivot_mem_440 child_required_sub_440 child_envelope_sub_440 ?_
  intro b hb
  exact common_sub_440 (mem_commonEnvelope childrenD_440 b hb)
def required_448 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_448 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_448 : Fin 2 → Finset Cell := ![(placed21 6 (4, 6) required_56), (placed21 1 (0, 2) required_447)]
def childrenD_448 : Fin 2 → Finset Cell := ![(placed21 6 (4, 6) envelope_56), (placed21 1 (0, 2) envelope_447)]
theorem common_sub_448 : commonEnvelope childrenD_448 ⊆ insert (1, 3) required_448 := by decide +kernel
theorem child_required_sub_448 : ∀ j, childrenC_448 j ⊆ insert (1, 3) required_448 := by decide +kernel
theorem child_envelope_sub_448 : ∀ j, childrenD_448 j ⊆ envelope_448 := by decide +kernel
theorem pivot_mem_448 : (1, 3) ∈ envelope_448 := by decide +kernel
theorem children_work_448 : ∀ j, Template HasSnaky 7 (childrenC_448 j) (childrenD_448 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_56 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_447 1 (0, 2)).mono (by decide +kernel)
theorem row_works_448 : Template HasSnaky 8 required_448 envelope_448 := by
  refine compose HasSnaky 7 childrenC_448 childrenD_448 children_work_448 (1, 3)
    required_448 envelope_448 pivot_mem_448 child_required_sub_448 child_envelope_sub_448 ?_
  intro b hb
  exact common_sub_448 (mem_commonEnvelope childrenD_448 b hb)
def height_120 : ℕ := 8
def childrenH_120 : Fin 3 → ℕ := ![height_44, height_52, height_116]
theorem height_exact_120 : height_120 = 1 + Finset.univ.sup childrenH_120 := by decide +kernel
theorem required_origin_120 : ∀ x ∈ required_120,
    (∃ j, x ∈ childrenC_120 j) ∨ ∀ j, x ∈ childrenD_120 j := by decide +kernel
theorem required_exact_120 : required_120 =
    ((Finset.univ.biUnion childrenC_120) ∪ commonEnvelope childrenD_120).erase (2, 3) := by
  exact required_eq_combination childrenC_120 childrenD_120 (2, 3) required_120
    (by decide +kernel) child_required_sub_120 common_sub_120 required_origin_120
theorem envelope_origin_120 : ∀ x ∈ envelope_120,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_120 j := by decide +kernel
theorem envelope_exact_120 : envelope_120 =
    insert (2, 3) (Finset.univ.biUnion childrenD_120) := by
  exact envelope_eq_combination childrenD_120 (2, 3) envelope_120
    pivot_mem_120 child_envelope_sub_120 envelope_origin_120
def checked_120 : CheckedCard where
  required := required_120
  envelope := envelope_120
  height := height_120
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_120
def height_171 : ℕ := 8
def childrenH_171 : Fin 3 → ℕ := ![height_6, height_26, height_116]
theorem height_exact_171 : height_171 = 1 + Finset.univ.sup childrenH_171 := by decide +kernel
theorem required_origin_171 : ∀ x ∈ required_171,
    (∃ j, x ∈ childrenC_171 j) ∨ ∀ j, x ∈ childrenD_171 j := by decide +kernel
theorem required_exact_171 : required_171 =
    ((Finset.univ.biUnion childrenC_171) ∪ commonEnvelope childrenD_171).erase (4, 3) := by
  exact required_eq_combination childrenC_171 childrenD_171 (4, 3) required_171
    (by decide +kernel) child_required_sub_171 common_sub_171 required_origin_171
theorem envelope_origin_171 : ∀ x ∈ envelope_171,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_171 j := by decide +kernel
theorem envelope_exact_171 : envelope_171 =
    insert (4, 3) (Finset.univ.biUnion childrenD_171) := by
  exact envelope_eq_combination childrenD_171 (4, 3) envelope_171
    pivot_mem_171 child_envelope_sub_171 envelope_origin_171
def checked_171 : CheckedCard where
  required := required_171
  envelope := envelope_171
  height := height_171
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_171
def height_174 : ℕ := 8
def childrenH_174 : Fin 6 → ℕ := ![height_116, height_117, height_135, height_135, height_173, height_173]
theorem height_exact_174 : height_174 = 1 + Finset.univ.sup childrenH_174 := by decide +kernel
theorem required_origin_174 : ∀ x ∈ required_174,
    (∃ j, x ∈ childrenC_174 j) ∨ ∀ j, x ∈ childrenD_174 j := by decide +kernel
theorem required_exact_174 : required_174 =
    ((Finset.univ.biUnion childrenC_174) ∪ commonEnvelope childrenD_174).erase (3, 5) := by
  exact required_eq_combination childrenC_174 childrenD_174 (3, 5) required_174
    (by decide +kernel) child_required_sub_174 common_sub_174 required_origin_174
theorem envelope_origin_174 : ∀ x ∈ envelope_174,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_174 j := by decide +kernel
theorem envelope_exact_174 : envelope_174 =
    insert (3, 5) (Finset.univ.biUnion childrenD_174) := by
  exact envelope_eq_combination childrenD_174 (3, 5) envelope_174
    pivot_mem_174 child_envelope_sub_174 envelope_origin_174
def checked_174 : CheckedCard where
  required := required_174
  envelope := envelope_174
  height := height_174
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_174
def height_257 : ℕ := 8
def childrenH_257 : Fin 3 → ℕ := ![height_7, height_9, height_256]
theorem height_exact_257 : height_257 = 1 + Finset.univ.sup childrenH_257 := by decide +kernel
theorem required_origin_257 : ∀ x ∈ required_257,
    (∃ j, x ∈ childrenC_257 j) ∨ ∀ j, x ∈ childrenD_257 j := by decide +kernel
theorem required_exact_257 : required_257 =
    ((Finset.univ.biUnion childrenC_257) ∪ commonEnvelope childrenD_257).erase (4, 3) := by
  exact required_eq_combination childrenC_257 childrenD_257 (4, 3) required_257
    (by decide +kernel) child_required_sub_257 common_sub_257 required_origin_257
theorem envelope_origin_257 : ∀ x ∈ envelope_257,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_257 j := by decide +kernel
theorem envelope_exact_257 : envelope_257 =
    insert (4, 3) (Finset.univ.biUnion childrenD_257) := by
  exact envelope_eq_combination childrenD_257 (4, 3) envelope_257
    pivot_mem_257 child_envelope_sub_257 envelope_origin_257
def checked_257 : CheckedCard where
  required := required_257
  envelope := envelope_257
  height := height_257
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_257
def height_258 : ℕ := 8
def childrenH_258 : Fin 4 → ℕ := ![height_8, height_161, height_162, height_256]
theorem height_exact_258 : height_258 = 1 + Finset.univ.sup childrenH_258 := by decide +kernel
theorem required_origin_258 : ∀ x ∈ required_258,
    (∃ j, x ∈ childrenC_258 j) ∨ ∀ j, x ∈ childrenD_258 j := by decide +kernel
theorem required_exact_258 : required_258 =
    ((Finset.univ.biUnion childrenC_258) ∪ commonEnvelope childrenD_258).erase (3, 3) := by
  exact required_eq_combination childrenC_258 childrenD_258 (3, 3) required_258
    (by decide +kernel) child_required_sub_258 common_sub_258 required_origin_258
theorem envelope_origin_258 : ∀ x ∈ envelope_258,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_258 j := by decide +kernel
theorem envelope_exact_258 : envelope_258 =
    insert (3, 3) (Finset.univ.biUnion childrenD_258) := by
  exact envelope_eq_combination childrenD_258 (3, 3) envelope_258
    pivot_mem_258 child_envelope_sub_258 envelope_origin_258
def checked_258 : CheckedCard where
  required := required_258
  envelope := envelope_258
  height := height_258
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_258
def height_285 : ℕ := 8
def childrenH_285 : Fin 3 → ℕ := ![height_6, height_26, height_117]
theorem height_exact_285 : height_285 = 1 + Finset.univ.sup childrenH_285 := by decide +kernel
theorem required_origin_285 : ∀ x ∈ required_285,
    (∃ j, x ∈ childrenC_285 j) ∨ ∀ j, x ∈ childrenD_285 j := by decide +kernel
theorem required_exact_285 : required_285 =
    ((Finset.univ.biUnion childrenC_285) ∪ commonEnvelope childrenD_285).erase (4, 3) := by
  exact required_eq_combination childrenC_285 childrenD_285 (4, 3) required_285
    (by decide +kernel) child_required_sub_285 common_sub_285 required_origin_285
theorem envelope_origin_285 : ∀ x ∈ envelope_285,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_285 j := by decide +kernel
theorem envelope_exact_285 : envelope_285 =
    insert (4, 3) (Finset.univ.biUnion childrenD_285) := by
  exact envelope_eq_combination childrenD_285 (4, 3) envelope_285
    pivot_mem_285 child_envelope_sub_285 envelope_origin_285
def checked_285 : CheckedCard where
  required := required_285
  envelope := envelope_285
  height := height_285
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_285
def height_319 : ℕ := 8
def childrenH_319 : Fin 2 → ℕ := ![height_52, height_318]
theorem height_exact_319 : height_319 = 1 + Finset.univ.sup childrenH_319 := by decide +kernel
theorem required_origin_319 : ∀ x ∈ required_319,
    (∃ j, x ∈ childrenC_319 j) ∨ ∀ j, x ∈ childrenD_319 j := by decide +kernel
theorem required_exact_319 : required_319 =
    ((Finset.univ.biUnion childrenC_319) ∪ commonEnvelope childrenD_319).erase (3, 4) := by
  exact required_eq_combination childrenC_319 childrenD_319 (3, 4) required_319
    (by decide +kernel) child_required_sub_319 common_sub_319 required_origin_319
theorem envelope_origin_319 : ∀ x ∈ envelope_319,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_319 j := by decide +kernel
theorem envelope_exact_319 : envelope_319 =
    insert (3, 4) (Finset.univ.biUnion childrenD_319) := by
  exact envelope_eq_combination childrenD_319 (3, 4) envelope_319
    pivot_mem_319 child_envelope_sub_319 envelope_origin_319
def checked_319 : CheckedCard where
  required := required_319
  envelope := envelope_319
  height := height_319
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_319
def height_321 : ℕ := 8
def childrenH_321 : Fin 2 → ℕ := ![height_5, height_320]
theorem height_exact_321 : height_321 = 1 + Finset.univ.sup childrenH_321 := by decide +kernel
theorem required_origin_321 : ∀ x ∈ required_321,
    (∃ j, x ∈ childrenC_321 j) ∨ ∀ j, x ∈ childrenD_321 j := by decide +kernel
theorem required_exact_321 : required_321 =
    ((Finset.univ.biUnion childrenC_321) ∪ commonEnvelope childrenD_321).erase (3, 3) := by
  exact required_eq_combination childrenC_321 childrenD_321 (3, 3) required_321
    (by decide +kernel) child_required_sub_321 common_sub_321 required_origin_321
theorem envelope_origin_321 : ∀ x ∈ envelope_321,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_321 j := by decide +kernel
theorem envelope_exact_321 : envelope_321 =
    insert (3, 3) (Finset.univ.biUnion childrenD_321) := by
  exact envelope_eq_combination childrenD_321 (3, 3) envelope_321
    pivot_mem_321 child_envelope_sub_321 envelope_origin_321
def checked_321 : CheckedCard where
  required := required_321
  envelope := envelope_321
  height := height_321
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_321
def height_323 : ℕ := 8
def childrenH_323 : Fin 2 → ℕ := ![height_11, height_320]
theorem height_exact_323 : height_323 = 1 + Finset.univ.sup childrenH_323 := by decide +kernel
theorem required_origin_323 : ∀ x ∈ required_323,
    (∃ j, x ∈ childrenC_323 j) ∨ ∀ j, x ∈ childrenD_323 j := by decide +kernel
theorem required_exact_323 : required_323 =
    ((Finset.univ.biUnion childrenC_323) ∪ commonEnvelope childrenD_323).erase (2, 4) := by
  exact required_eq_combination childrenC_323 childrenD_323 (2, 4) required_323
    (by decide +kernel) child_required_sub_323 common_sub_323 required_origin_323
theorem envelope_origin_323 : ∀ x ∈ envelope_323,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_323 j := by decide +kernel
theorem envelope_exact_323 : envelope_323 =
    insert (2, 4) (Finset.univ.biUnion childrenD_323) := by
  exact envelope_eq_combination childrenD_323 (2, 4) envelope_323
    pivot_mem_323 child_envelope_sub_323 envelope_origin_323
def checked_323 : CheckedCard where
  required := required_323
  envelope := envelope_323
  height := height_323
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_323
def height_338 : ℕ := 8
def childrenH_338 : Fin 3 → ℕ := ![height_44, height_47, height_337]
theorem height_exact_338 : height_338 = 1 + Finset.univ.sup childrenH_338 := by decide +kernel
theorem required_origin_338 : ∀ x ∈ required_338,
    (∃ j, x ∈ childrenC_338 j) ∨ ∀ j, x ∈ childrenD_338 j := by decide +kernel
theorem required_exact_338 : required_338 =
    ((Finset.univ.biUnion childrenC_338) ∪ commonEnvelope childrenD_338).erase (2, 4) := by
  exact required_eq_combination childrenC_338 childrenD_338 (2, 4) required_338
    (by decide +kernel) child_required_sub_338 common_sub_338 required_origin_338
theorem envelope_origin_338 : ∀ x ∈ envelope_338,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_338 j := by decide +kernel
theorem envelope_exact_338 : envelope_338 =
    insert (2, 4) (Finset.univ.biUnion childrenD_338) := by
  exact envelope_eq_combination childrenD_338 (2, 4) envelope_338
    pivot_mem_338 child_envelope_sub_338 envelope_origin_338
def checked_338 : CheckedCard where
  required := required_338
  envelope := envelope_338
  height := height_338
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_338
def height_345 : ℕ := 8
def childrenH_345 : Fin 3 → ℕ := ![height_8, height_11, height_344]
theorem height_exact_345 : height_345 = 1 + Finset.univ.sup childrenH_345 := by decide +kernel
theorem required_origin_345 : ∀ x ∈ required_345,
    (∃ j, x ∈ childrenC_345 j) ∨ ∀ j, x ∈ childrenD_345 j := by decide +kernel
theorem required_exact_345 : required_345 =
    ((Finset.univ.biUnion childrenC_345) ∪ commonEnvelope childrenD_345).erase (4, 2) := by
  exact required_eq_combination childrenC_345 childrenD_345 (4, 2) required_345
    (by decide +kernel) child_required_sub_345 common_sub_345 required_origin_345
theorem envelope_origin_345 : ∀ x ∈ envelope_345,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_345 j := by decide +kernel
theorem envelope_exact_345 : envelope_345 =
    insert (4, 2) (Finset.univ.biUnion childrenD_345) := by
  exact envelope_eq_combination childrenD_345 (4, 2) envelope_345
    pivot_mem_345 child_envelope_sub_345 envelope_origin_345
def checked_345 : CheckedCard where
  required := required_345
  envelope := envelope_345
  height := height_345
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_345
def height_373 : ℕ := 8
def childrenH_373 : Fin 2 → ℕ := ![height_5, height_372]
theorem height_exact_373 : height_373 = 1 + Finset.univ.sup childrenH_373 := by decide +kernel
theorem required_origin_373 : ∀ x ∈ required_373,
    (∃ j, x ∈ childrenC_373 j) ∨ ∀ j, x ∈ childrenD_373 j := by decide +kernel
theorem required_exact_373 : required_373 =
    ((Finset.univ.biUnion childrenC_373) ∪ commonEnvelope childrenD_373).erase (1, 4) := by
  exact required_eq_combination childrenC_373 childrenD_373 (1, 4) required_373
    (by decide +kernel) child_required_sub_373 common_sub_373 required_origin_373
theorem envelope_origin_373 : ∀ x ∈ envelope_373,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_373 j := by decide +kernel
theorem envelope_exact_373 : envelope_373 =
    insert (1, 4) (Finset.univ.biUnion childrenD_373) := by
  exact envelope_eq_combination childrenD_373 (1, 4) envelope_373
    pivot_mem_373 child_envelope_sub_373 envelope_origin_373
def checked_373 : CheckedCard where
  required := required_373
  envelope := envelope_373
  height := height_373
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_373
def height_395_i0 : ℕ := 7
def childrenH_395_i0 : Fin 2 → ℕ := ![height_5, height_217]
theorem height_exact_395_i0 : height_395_i0 = 1 + Finset.univ.sup childrenH_395_i0 := by decide +kernel
theorem required_origin_395_i0 : ∀ x ∈ required_395_i0,
    (∃ j, x ∈ childrenC_395_i0 j) ∨ ∀ j, x ∈ childrenD_395_i0 j := by decide +kernel
theorem required_exact_395_i0 : required_395_i0 =
    ((Finset.univ.biUnion childrenC_395_i0) ∪ commonEnvelope childrenD_395_i0).erase (3, 1) := by
  exact required_eq_combination childrenC_395_i0 childrenD_395_i0 (3, 1) required_395_i0
    (by decide +kernel) child_required_sub_395_i0 common_sub_395_i0 required_origin_395_i0
theorem envelope_origin_395_i0 : ∀ x ∈ envelope_395_i0,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_395_i0 j := by decide +kernel
theorem envelope_exact_395_i0 : envelope_395_i0 =
    insert (3, 1) (Finset.univ.biUnion childrenD_395_i0) := by
  exact envelope_eq_combination childrenD_395_i0 (3, 1) envelope_395_i0
    pivot_mem_395_i0 child_envelope_sub_395_i0 envelope_origin_395_i0
def checked_395_i0 : CheckedCard where
  required := required_395_i0
  envelope := envelope_395_i0
  height := height_395_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_395_i0
def height_395 : ℕ := 8
def childrenH_395 : Fin 2 → ℕ := ![height_5, height_395_i0]
theorem height_exact_395 : height_395 = 1 + Finset.univ.sup childrenH_395 := by decide +kernel
theorem required_origin_395 : ∀ x ∈ required_395,
    (∃ j, x ∈ childrenC_395 j) ∨ ∀ j, x ∈ childrenD_395 j := by decide +kernel
theorem required_exact_395 : required_395 =
    ((Finset.univ.biUnion childrenC_395) ∪ commonEnvelope childrenD_395).erase (3, 3) := by
  exact required_eq_combination childrenC_395 childrenD_395 (3, 3) required_395
    (by decide +kernel) child_required_sub_395 common_sub_395 required_origin_395
theorem envelope_origin_395 : ∀ x ∈ envelope_395,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_395 j := by decide +kernel
theorem envelope_exact_395 : envelope_395 =
    insert (3, 3) (Finset.univ.biUnion childrenD_395) := by
  exact envelope_eq_combination childrenD_395 (3, 3) envelope_395
    pivot_mem_395 child_envelope_sub_395 envelope_origin_395
def checked_395 : CheckedCard where
  required := required_395
  envelope := envelope_395
  height := height_395
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_395
def height_405 : ℕ := 8
def childrenH_405 : Fin 2 → ℕ := ![height_0, height_404]
theorem height_exact_405 : height_405 = 1 + Finset.univ.sup childrenH_405 := by decide +kernel
theorem required_origin_405 : ∀ x ∈ required_405,
    (∃ j, x ∈ childrenC_405 j) ∨ ∀ j, x ∈ childrenD_405 j := by decide +kernel
theorem required_exact_405 : required_405 =
    ((Finset.univ.biUnion childrenC_405) ∪ commonEnvelope childrenD_405).erase (1, 4) := by
  exact required_eq_combination childrenC_405 childrenD_405 (1, 4) required_405
    (by decide +kernel) child_required_sub_405 common_sub_405 required_origin_405
theorem envelope_origin_405 : ∀ x ∈ envelope_405,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_405 j := by decide +kernel
theorem envelope_exact_405 : envelope_405 =
    insert (1, 4) (Finset.univ.biUnion childrenD_405) := by
  exact envelope_eq_combination childrenD_405 (1, 4) envelope_405
    pivot_mem_405 child_envelope_sub_405 envelope_origin_405
def checked_405 : CheckedCard where
  required := required_405
  envelope := envelope_405
  height := height_405
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_405
def height_412_i0 : ℕ := 7
def childrenH_412_i0 : Fin 2 → ℕ := ![height_0, height_358]
theorem height_exact_412_i0 : height_412_i0 = 1 + Finset.univ.sup childrenH_412_i0 := by decide +kernel
theorem required_origin_412_i0 : ∀ x ∈ required_412_i0,
    (∃ j, x ∈ childrenC_412_i0 j) ∨ ∀ j, x ∈ childrenD_412_i0 j := by decide +kernel
theorem required_exact_412_i0 : required_412_i0 =
    ((Finset.univ.biUnion childrenC_412_i0) ∪ commonEnvelope childrenD_412_i0).erase (3, 1) := by
  exact required_eq_combination childrenC_412_i0 childrenD_412_i0 (3, 1) required_412_i0
    (by decide +kernel) child_required_sub_412_i0 common_sub_412_i0 required_origin_412_i0
theorem envelope_origin_412_i0 : ∀ x ∈ envelope_412_i0,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_412_i0 j := by decide +kernel
theorem envelope_exact_412_i0 : envelope_412_i0 =
    insert (3, 1) (Finset.univ.biUnion childrenD_412_i0) := by
  exact envelope_eq_combination childrenD_412_i0 (3, 1) envelope_412_i0
    pivot_mem_412_i0 child_envelope_sub_412_i0 envelope_origin_412_i0
def checked_412_i0 : CheckedCard where
  required := required_412_i0
  envelope := envelope_412_i0
  height := height_412_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_412_i0
def height_412 : ℕ := 8
def childrenH_412 : Fin 2 → ℕ := ![height_5, height_412_i0]
theorem height_exact_412 : height_412 = 1 + Finset.univ.sup childrenH_412 := by decide +kernel
theorem required_origin_412 : ∀ x ∈ required_412,
    (∃ j, x ∈ childrenC_412 j) ∨ ∀ j, x ∈ childrenD_412 j := by decide +kernel
theorem required_exact_412 : required_412 =
    ((Finset.univ.biUnion childrenC_412) ∪ commonEnvelope childrenD_412).erase (2, 1) := by
  exact required_eq_combination childrenC_412 childrenD_412 (2, 1) required_412
    (by decide +kernel) child_required_sub_412 common_sub_412 required_origin_412
theorem envelope_origin_412 : ∀ x ∈ envelope_412,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_412 j := by decide +kernel
theorem envelope_exact_412 : envelope_412 =
    insert (2, 1) (Finset.univ.biUnion childrenD_412) := by
  exact envelope_eq_combination childrenD_412 (2, 1) envelope_412
    pivot_mem_412 child_envelope_sub_412 envelope_origin_412
def checked_412 : CheckedCard where
  required := required_412
  envelope := envelope_412
  height := height_412
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_412
def height_419 : ℕ := 8
def childrenH_419 : Fin 2 → ℕ := ![height_5, height_418]
theorem height_exact_419 : height_419 = 1 + Finset.univ.sup childrenH_419 := by decide +kernel
theorem required_origin_419 : ∀ x ∈ required_419,
    (∃ j, x ∈ childrenC_419 j) ∨ ∀ j, x ∈ childrenD_419 j := by decide +kernel
theorem required_exact_419 : required_419 =
    ((Finset.univ.biUnion childrenC_419) ∪ commonEnvelope childrenD_419).erase (2, 1) := by
  exact required_eq_combination childrenC_419 childrenD_419 (2, 1) required_419
    (by decide +kernel) child_required_sub_419 common_sub_419 required_origin_419
theorem envelope_origin_419 : ∀ x ∈ envelope_419,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_419 j := by decide +kernel
theorem envelope_exact_419 : envelope_419 =
    insert (2, 1) (Finset.univ.biUnion childrenD_419) := by
  exact envelope_eq_combination childrenD_419 (2, 1) envelope_419
    pivot_mem_419 child_envelope_sub_419 envelope_origin_419
def checked_419 : CheckedCard where
  required := required_419
  envelope := envelope_419
  height := height_419
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_419
def height_420 : ℕ := 8
def childrenH_420 : Fin 2 → ℕ := ![height_0, height_418]
theorem height_exact_420 : height_420 = 1 + Finset.univ.sup childrenH_420 := by decide +kernel
theorem required_origin_420 : ∀ x ∈ required_420,
    (∃ j, x ∈ childrenC_420 j) ∨ ∀ j, x ∈ childrenD_420 j := by decide +kernel
theorem required_exact_420 : required_420 =
    ((Finset.univ.biUnion childrenC_420) ∪ commonEnvelope childrenD_420).erase (3, 1) := by
  exact required_eq_combination childrenC_420 childrenD_420 (3, 1) required_420
    (by decide +kernel) child_required_sub_420 common_sub_420 required_origin_420
theorem envelope_origin_420 : ∀ x ∈ envelope_420,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_420 j := by decide +kernel
theorem envelope_exact_420 : envelope_420 =
    insert (3, 1) (Finset.univ.biUnion childrenD_420) := by
  exact envelope_eq_combination childrenD_420 (3, 1) envelope_420
    pivot_mem_420 child_envelope_sub_420 envelope_origin_420
def checked_420 : CheckedCard where
  required := required_420
  envelope := envelope_420
  height := height_420
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_420
def height_438 : ℕ := 8
def childrenH_438 : Fin 3 → ℕ := ![height_10, height_47, height_436]
theorem height_exact_438 : height_438 = 1 + Finset.univ.sup childrenH_438 := by decide +kernel
theorem required_origin_438 : ∀ x ∈ required_438,
    (∃ j, x ∈ childrenC_438 j) ∨ ∀ j, x ∈ childrenD_438 j := by decide +kernel
theorem required_exact_438 : required_438 =
    ((Finset.univ.biUnion childrenC_438) ∪ commonEnvelope childrenD_438).erase (4, 3) := by
  exact required_eq_combination childrenC_438 childrenD_438 (4, 3) required_438
    (by decide +kernel) child_required_sub_438 common_sub_438 required_origin_438
theorem envelope_origin_438 : ∀ x ∈ envelope_438,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_438 j := by decide +kernel
theorem envelope_exact_438 : envelope_438 =
    insert (4, 3) (Finset.univ.biUnion childrenD_438) := by
  exact envelope_eq_combination childrenD_438 (4, 3) envelope_438
    pivot_mem_438 child_envelope_sub_438 envelope_origin_438
def checked_438 : CheckedCard where
  required := required_438
  envelope := envelope_438
  height := height_438
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_438
def height_440_i0 : ℕ := 7
def childrenH_440_i0 : Fin 2 → ℕ := ![height_5, height_439]
theorem height_exact_440_i0 : height_440_i0 = 1 + Finset.univ.sup childrenH_440_i0 := by decide +kernel
theorem required_origin_440_i0 : ∀ x ∈ required_440_i0,
    (∃ j, x ∈ childrenC_440_i0 j) ∨ ∀ j, x ∈ childrenD_440_i0 j := by decide +kernel
theorem required_exact_440_i0 : required_440_i0 =
    ((Finset.univ.biUnion childrenC_440_i0) ∪ commonEnvelope childrenD_440_i0).erase (1, 1) := by
  exact required_eq_combination childrenC_440_i0 childrenD_440_i0 (1, 1) required_440_i0
    (by decide +kernel) child_required_sub_440_i0 common_sub_440_i0 required_origin_440_i0
theorem envelope_origin_440_i0 : ∀ x ∈ envelope_440_i0,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_440_i0 j := by decide +kernel
theorem envelope_exact_440_i0 : envelope_440_i0 =
    insert (1, 1) (Finset.univ.biUnion childrenD_440_i0) := by
  exact envelope_eq_combination childrenD_440_i0 (1, 1) envelope_440_i0
    pivot_mem_440_i0 child_envelope_sub_440_i0 envelope_origin_440_i0
def checked_440_i0 : CheckedCard where
  required := required_440_i0
  envelope := envelope_440_i0
  height := height_440_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_440_i0
def height_440 : ℕ := 8
def childrenH_440 : Fin 2 → ℕ := ![height_18, height_440_i0]
theorem height_exact_440 : height_440 = 1 + Finset.univ.sup childrenH_440 := by decide +kernel
theorem required_origin_440 : ∀ x ∈ required_440,
    (∃ j, x ∈ childrenC_440 j) ∨ ∀ j, x ∈ childrenD_440 j := by decide +kernel
theorem required_exact_440 : required_440 =
    ((Finset.univ.biUnion childrenC_440) ∪ commonEnvelope childrenD_440).erase (0, 1) := by
  exact required_eq_combination childrenC_440 childrenD_440 (0, 1) required_440
    (by decide +kernel) child_required_sub_440 common_sub_440 required_origin_440
theorem envelope_origin_440 : ∀ x ∈ envelope_440,
    x = (0, 1) ∨ ∃ j, x ∈ childrenD_440 j := by decide +kernel
theorem envelope_exact_440 : envelope_440 =
    insert (0, 1) (Finset.univ.biUnion childrenD_440) := by
  exact envelope_eq_combination childrenD_440 (0, 1) envelope_440
    pivot_mem_440 child_envelope_sub_440 envelope_origin_440
def checked_440 : CheckedCard where
  required := required_440
  envelope := envelope_440
  height := height_440
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_440
def height_448 : ℕ := 8
def childrenH_448 : Fin 2 → ℕ := ![height_56, height_447]
theorem height_exact_448 : height_448 = 1 + Finset.univ.sup childrenH_448 := by decide +kernel
theorem required_origin_448 : ∀ x ∈ required_448,
    (∃ j, x ∈ childrenC_448 j) ∨ ∀ j, x ∈ childrenD_448 j := by decide +kernel
theorem required_exact_448 : required_448 =
    ((Finset.univ.biUnion childrenC_448) ∪ commonEnvelope childrenD_448).erase (1, 3) := by
  exact required_eq_combination childrenC_448 childrenD_448 (1, 3) required_448
    (by decide +kernel) child_required_sub_448 common_sub_448 required_origin_448
theorem envelope_origin_448 : ∀ x ∈ envelope_448,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_448 j := by decide +kernel
theorem envelope_exact_448 : envelope_448 =
    insert (1, 3) (Finset.univ.biUnion childrenD_448) := by
  exact envelope_eq_combination childrenD_448 (1, 3) envelope_448
    pivot_mem_448 child_envelope_sub_448 envelope_origin_448
def checked_448 : CheckedCard where
  required := required_448
  envelope := envelope_448
  height := height_448
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_448
end SnakyPrototype.Certificate21

end OAI
