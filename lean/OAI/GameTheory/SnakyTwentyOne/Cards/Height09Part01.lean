import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_322 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_322 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_322 : Fin 3 → Finset Cell := ![(placed21 3 (0, 4) required_7), (placed21 1 (0, 3) required_9), (placed21 0 (1, 0) required_321)]
def childrenD_322 : Fin 3 → Finset Cell := ![(placed21 3 (0, 4) envelope_7), (placed21 1 (0, 3) envelope_9), (placed21 0 (1, 0) envelope_321)]
theorem common_sub_322 : commonEnvelope childrenD_322 ⊆ insert (4, 4) required_322 := by decide +kernel
theorem child_required_sub_322 : ∀ j, childrenC_322 j ⊆ insert (4, 4) required_322 := by decide +kernel
theorem child_envelope_sub_322 : ∀ j, childrenD_322 j ⊆ envelope_322 := by decide +kernel
theorem pivot_mem_322 : (4, 4) ∈ envelope_322 := by decide +kernel
theorem children_work_322 : ∀ j, Template HasSnaky 8 (childrenC_322 j) (childrenD_322 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 0 (1, 0)).mono (by decide +kernel)
theorem row_works_322 : Template HasSnaky 9 required_322 envelope_322 := by
  refine compose HasSnaky 8 childrenC_322 childrenD_322 children_work_322 (4, 4)
    required_322 envelope_322 pivot_mem_322 child_required_sub_322 child_envelope_sub_322 ?_
  intro b hb
  exact common_sub_322 (mem_commonEnvelope childrenD_322 b hb)
def required_325 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_325 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_325 : Fin 2 → Finset Cell := ![(placed21 2 (4, 4) required_5), (placed21 0 (1, 0) required_321)]
def childrenD_325 : Fin 2 → Finset Cell := ![(placed21 2 (4, 4) envelope_5), (placed21 0 (1, 0) envelope_321)]
theorem common_sub_325 : commonEnvelope childrenD_325 ⊆ insert (3, 4) required_325 := by decide +kernel
theorem child_required_sub_325 : ∀ j, childrenC_325 j ⊆ insert (3, 4) required_325 := by decide +kernel
theorem child_envelope_sub_325 : ∀ j, childrenD_325 j ⊆ envelope_325 := by decide +kernel
theorem pivot_mem_325 : (3, 4) ∈ envelope_325 := by decide +kernel
theorem children_work_325 : ∀ j, Template HasSnaky 8 (childrenC_325 j) (childrenD_325 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 0 (1, 0)).mono (by decide +kernel)
theorem row_works_325 : Template HasSnaky 9 required_325 envelope_325 := by
  refine compose HasSnaky 8 childrenC_325 childrenD_325 children_work_325 (3, 4)
    required_325 envelope_325 pivot_mem_325 child_required_sub_325 child_envelope_sub_325 ?_
  intro b hb
  exact common_sub_325 (mem_commonEnvelope childrenD_325 b hb)
def required_326 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_326 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_326 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_3), (placed21 0 (2, 0) required_321)]
def childrenD_326 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_3), (placed21 0 (2, 0) envelope_321)]
theorem common_sub_326 : commonEnvelope childrenD_326 ⊆ insert (2, 4) required_326 := by decide +kernel
theorem child_required_sub_326 : ∀ j, childrenC_326 j ⊆ insert (2, 4) required_326 := by decide +kernel
theorem child_envelope_sub_326 : ∀ j, childrenD_326 j ⊆ envelope_326 := by decide +kernel
theorem pivot_mem_326 : (2, 4) ∈ envelope_326 := by decide +kernel
theorem children_work_326 : ∀ j, Template HasSnaky 8 (childrenC_326 j) (childrenD_326 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 0 (2, 0)).mono (by decide +kernel)
theorem row_works_326 : Template HasSnaky 9 required_326 envelope_326 := by
  refine compose HasSnaky 8 childrenC_326 childrenD_326 children_work_326 (2, 4)
    required_326 envelope_326 pivot_mem_326 child_required_sub_326 child_envelope_sub_326 ?_
  intro b hb
  exact common_sub_326 (mem_commonEnvelope childrenD_326 b hb)
def required_327 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_327 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_327 : Fin 2 → Finset Cell := ![(placed21 0 (1, 3) required_32), (placed21 2 (4, 0) required_321)]
def childrenD_327 : Fin 2 → Finset Cell := ![(placed21 0 (1, 3) envelope_32), (placed21 2 (4, 0) envelope_321)]
theorem common_sub_327 : commonEnvelope childrenD_327 ⊆ insert (4, 4) required_327 := by decide +kernel
theorem child_required_sub_327 : ∀ j, childrenC_327 j ⊆ insert (4, 4) required_327 := by decide +kernel
theorem child_envelope_sub_327 : ∀ j, childrenD_327 j ⊆ envelope_327 := by decide +kernel
theorem pivot_mem_327 : (4, 4) ∈ envelope_327 := by decide +kernel
theorem children_work_327 : ∀ j, Template HasSnaky 8 (childrenC_327 j) (childrenD_327 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_32 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 2 (4, 0)).mono (by decide +kernel)
theorem row_works_327 : Template HasSnaky 9 required_327 envelope_327 := by
  refine compose HasSnaky 8 childrenC_327 childrenD_327 children_work_327 (4, 4)
    required_327 envelope_327 pivot_mem_327 child_required_sub_327 child_envelope_sub_327 ?_
  intro b hb
  exact common_sub_327 (mem_commonEnvelope childrenD_327 b hb)
def required_328 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_328 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_328 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) required_7), (placed21 3 (0, 5) required_9), (placed21 0 (1, 0) required_321)]
def childrenD_328 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) envelope_7), (placed21 3 (0, 5) envelope_9), (placed21 0 (1, 0) envelope_321)]
theorem common_sub_328 : commonEnvelope childrenD_328 ⊆ insert (3, 4) required_328 := by decide +kernel
theorem child_required_sub_328 : ∀ j, childrenC_328 j ⊆ insert (3, 4) required_328 := by decide +kernel
theorem child_envelope_sub_328 : ∀ j, childrenD_328 j ⊆ envelope_328 := by decide +kernel
theorem pivot_mem_328 : (3, 4) ∈ envelope_328 := by decide +kernel
theorem children_work_328 : ∀ j, Template HasSnaky 8 (childrenC_328 j) (childrenD_328 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 0 (1, 0)).mono (by decide +kernel)
theorem row_works_328 : Template HasSnaky 9 required_328 envelope_328 := by
  refine compose HasSnaky 8 childrenC_328 childrenD_328 children_work_328 (3, 4)
    required_328 envelope_328 pivot_mem_328 child_required_sub_328 child_envelope_sub_328 ?_
  intro b hb
  exact common_sub_328 (mem_commonEnvelope childrenD_328 b hb)
def required_330 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_330 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_330 : Fin 3 → Finset Cell := ![(placed21 3 (0, 4) required_7), (placed21 1 (0, 3) required_9), (placed21 0 (1, 0) required_321)]
def childrenD_330 : Fin 3 → Finset Cell := ![(placed21 3 (0, 4) envelope_7), (placed21 1 (0, 3) envelope_9), (placed21 0 (1, 0) envelope_321)]
theorem common_sub_330 : commonEnvelope childrenD_330 ⊆ insert (3, 4) required_330 := by decide +kernel
theorem child_required_sub_330 : ∀ j, childrenC_330 j ⊆ insert (3, 4) required_330 := by decide +kernel
theorem child_envelope_sub_330 : ∀ j, childrenD_330 j ⊆ envelope_330 := by decide +kernel
theorem pivot_mem_330 : (3, 4) ∈ envelope_330 := by decide +kernel
theorem children_work_330 : ∀ j, Template HasSnaky 8 (childrenC_330 j) (childrenD_330 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 0 (1, 0)).mono (by decide +kernel)
theorem row_works_330 : Template HasSnaky 9 required_330 envelope_330 := by
  refine compose HasSnaky 8 childrenC_330 childrenD_330 children_work_330 (3, 4)
    required_330 envelope_330 pivot_mem_330 child_required_sub_330 child_envelope_sub_330 ?_
  intro b hb
  exact common_sub_330 (mem_commonEnvelope childrenD_330 b hb)
def required_368 : Finset Cell := ⟨(([(1, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_368 : Finset Cell := ⟨(([(0, 6), (0, 7), (1, 4), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5), (6, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_368 : Fin 7 → Finset Cell := ![(placed21 4 (3, 7) required_14), (placed21 4 (3, 7) required_31), (placed21 5 (6, 2) required_181), (placed21 0 (3, 1) required_189), (placed21 5 (7, 2) required_257), (placed21 4 (1, 6) required_355), (placed21 6 (5, 7) required_367)]
def childrenD_368 : Fin 7 → Finset Cell := ![(placed21 4 (3, 7) envelope_14), (placed21 4 (3, 7) envelope_31), (placed21 5 (6, 2) envelope_181), (placed21 0 (3, 1) envelope_189), (placed21 5 (7, 2) envelope_257), (placed21 4 (1, 6) envelope_355), (placed21 6 (5, 7) envelope_367)]
theorem common_sub_368 : commonEnvelope childrenD_368 ⊆ insert (4, 5) required_368 := by decide +kernel
theorem child_required_sub_368 : ∀ j, childrenC_368 j ⊆ insert (4, 5) required_368 := by decide +kernel
theorem child_envelope_sub_368 : ∀ j, childrenD_368 j ⊆ envelope_368 := by decide +kernel
theorem pivot_mem_368 : (4, 5) ∈ envelope_368 := by decide +kernel
theorem children_work_368 : ∀ j, Template HasSnaky 8 (childrenC_368 j) (childrenD_368 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_257 5 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_355 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 6 (5, 7)).mono (by decide +kernel)
theorem row_works_368 : Template HasSnaky 9 required_368 envelope_368 := by
  refine compose HasSnaky 8 childrenC_368 childrenD_368 children_work_368 (4, 5)
    required_368 envelope_368 pivot_mem_368 child_required_sub_368 child_envelope_sub_368 ?_
  intro b hb
  exact common_sub_368 (mem_commonEnvelope childrenD_368 b hb)
def required_380_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_380_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_380_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 1 (1, 0) required_379)]
def childrenD_380_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 1 (1, 0) envelope_379)]
theorem common_sub_380_i0 : commonEnvelope childrenD_380_i0 ⊆ insert (3, 0) required_380_i0 := by decide +kernel
theorem child_required_sub_380_i0 : ∀ j, childrenC_380_i0 j ⊆ insert (3, 0) required_380_i0 := by decide +kernel
theorem child_envelope_sub_380_i0 : ∀ j, childrenD_380_i0 j ⊆ envelope_380_i0 := by decide +kernel
theorem pivot_mem_380_i0 : (3, 0) ∈ envelope_380_i0 := by decide +kernel
theorem children_work_380_i0 : ∀ j, Template HasSnaky 7 (childrenC_380_i0 j) (childrenD_380_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_379 1 (1, 0)).mono (by decide +kernel)
theorem row_works_380_i0 : Template HasSnaky 8 required_380_i0 envelope_380_i0 := by
  refine compose HasSnaky 7 childrenC_380_i0 childrenD_380_i0 children_work_380_i0 (3, 0)
    required_380_i0 envelope_380_i0 pivot_mem_380_i0 child_required_sub_380_i0 child_envelope_sub_380_i0 ?_
  intro b hb
  exact common_sub_380_i0 (mem_commonEnvelope childrenD_380_i0 b hb)
def required_380 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_380 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_380 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_380_i0]
def childrenD_380 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_380_i0]
theorem common_sub_380 : commonEnvelope childrenD_380 ⊆ insert (3, 2) required_380 := by decide +kernel
theorem child_required_sub_380 : ∀ j, childrenC_380 j ⊆ insert (3, 2) required_380 := by decide +kernel
theorem child_envelope_sub_380 : ∀ j, childrenD_380 j ⊆ envelope_380 := by decide +kernel
theorem pivot_mem_380 : (3, 2) ∈ envelope_380 := by decide +kernel
theorem children_work_380 : ∀ j, Template HasSnaky 8 (childrenC_380 j) (childrenD_380 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_380_i0.mono (by decide +kernel)
theorem row_works_380 : Template HasSnaky 9 required_380 envelope_380 := by
  refine compose HasSnaky 8 childrenC_380 childrenD_380 children_work_380 (3, 2)
    required_380 envelope_380 pivot_mem_380 child_required_sub_380 child_envelope_sub_380 ?_
  intro b hb
  exact common_sub_380 (mem_commonEnvelope childrenD_380 b hb)
def required_396 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_396 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_396 : Fin 3 → Finset Cell := ![(placed21 2 (2, 2) required_7), (placed21 2 (3, 2) required_9), (placed21 3 (0, 6) required_395)]
def childrenD_396 : Fin 3 → Finset Cell := ![(placed21 2 (2, 2) envelope_7), (placed21 2 (3, 2) envelope_9), (placed21 3 (0, 6) envelope_395)]
theorem common_sub_396 : commonEnvelope childrenD_396 ⊆ insert (2, 6) required_396 := by decide +kernel
theorem child_required_sub_396 : ∀ j, childrenC_396 j ⊆ insert (2, 6) required_396 := by decide +kernel
theorem child_envelope_sub_396 : ∀ j, childrenD_396 j ⊆ envelope_396 := by decide +kernel
theorem pivot_mem_396 : (2, 6) ∈ envelope_396 := by decide +kernel
theorem children_work_396 : ∀ j, Template HasSnaky 8 (childrenC_396 j) (childrenD_396 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_395 3 (0, 6)).mono (by decide +kernel)
theorem row_works_396 : Template HasSnaky 9 required_396 envelope_396 := by
  refine compose HasSnaky 8 childrenC_396 childrenD_396 children_work_396 (2, 6)
    required_396 envelope_396 pivot_mem_396 child_required_sub_396 child_envelope_sub_396 ?_
  intro b hb
  exact common_sub_396 (mem_commonEnvelope childrenD_396 b hb)
def required_397 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_397 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_397 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) required_8), required_161, required_162, (placed21 0 (0, 1) required_395)]
def childrenD_397 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) envelope_8), envelope_161, envelope_162, (placed21 0 (0, 1) envelope_395)]
theorem common_sub_397 : commonEnvelope childrenD_397 ⊆ insert (3, 3) required_397 := by decide +kernel
theorem child_required_sub_397 : ∀ j, childrenC_397 j ⊆ insert (3, 3) required_397 := by decide +kernel
theorem child_envelope_sub_397 : ∀ j, childrenD_397 j ⊆ envelope_397 := by decide +kernel
theorem pivot_mem_397 : (3, 3) ∈ envelope_397 := by decide +kernel
theorem children_work_397 : ∀ j, Template HasSnaky 8 (childrenC_397 j) (childrenD_397 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_161.mono (by decide +kernel)
  · exact row_works_162.mono (by decide +kernel)
  · exact (placed21_template row_works_395 0 (0, 1)).mono (by decide +kernel)
theorem row_works_397 : Template HasSnaky 9 required_397 envelope_397 := by
  refine compose HasSnaky 8 childrenC_397 childrenD_397 children_work_397 (3, 3)
    required_397 envelope_397 pivot_mem_397 child_required_sub_397 child_envelope_sub_397 ?_
  intro b hb
  exact common_sub_397 (mem_commonEnvelope childrenD_397 b hb)
def required_398 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_398 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_398 : Fin 5 → Finset Cell := ![required_171, (placed21 0 (0, 2) required_197), (placed21 4 (0, 4) required_197), required_285, (placed21 0 (0, 1) required_395)]
def childrenD_398 : Fin 5 → Finset Cell := ![envelope_171, (placed21 0 (0, 2) envelope_197), (placed21 4 (0, 4) envelope_197), envelope_285, (placed21 0 (0, 1) envelope_395)]
theorem common_sub_398 : commonEnvelope childrenD_398 ⊆ insert (3, 3) required_398 := by decide +kernel
theorem child_required_sub_398 : ∀ j, childrenC_398 j ⊆ insert (3, 3) required_398 := by decide +kernel
theorem child_envelope_sub_398 : ∀ j, childrenD_398 j ⊆ envelope_398 := by decide +kernel
theorem pivot_mem_398 : (3, 3) ∈ envelope_398 := by decide +kernel
theorem children_work_398 : ∀ j, Template HasSnaky 8 (childrenC_398 j) (childrenD_398 j) := by
  intro j
  fin_cases j
  · exact row_works_171.mono (by decide +kernel)
  · exact (placed21_template row_works_197 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 4 (0, 4)).mono (by decide +kernel)
  · exact row_works_285.mono (by decide +kernel)
  · exact (placed21_template row_works_395 0 (0, 1)).mono (by decide +kernel)
theorem row_works_398 : Template HasSnaky 9 required_398 envelope_398 := by
  refine compose HasSnaky 8 childrenC_398 childrenD_398 children_work_398 (3, 3)
    required_398 envelope_398 pivot_mem_398 child_required_sub_398 child_envelope_sub_398 ?_
  intro b hb
  exact common_sub_398 (mem_commonEnvelope childrenD_398 b hb)
def required_400 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_400 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3), (5, 4), (5, 5), (5, 6), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_400 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), (placed21 0 (1, 0) required_395)]
def childrenD_400 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_395)]
theorem common_sub_400 : commonEnvelope childrenD_400 ⊆ insert (3, 2) required_400 := by decide +kernel
theorem child_required_sub_400 : ∀ j, childrenC_400 j ⊆ insert (3, 2) required_400 := by decide +kernel
theorem child_envelope_sub_400 : ∀ j, childrenD_400 j ⊆ envelope_400 := by decide +kernel
theorem pivot_mem_400 : (3, 2) ∈ envelope_400 := by decide +kernel
theorem children_work_400 : ∀ j, Template HasSnaky 8 (childrenC_400 j) (childrenD_400 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_395 0 (1, 0)).mono (by decide +kernel)
theorem row_works_400 : Template HasSnaky 9 required_400 envelope_400 := by
  refine compose HasSnaky 8 childrenC_400 childrenD_400 children_work_400 (3, 2)
    required_400 envelope_400 pivot_mem_400 child_required_sub_400 child_envelope_sub_400 ?_
  intro b hb
  exact common_sub_400 (mem_commonEnvelope childrenD_400 b hb)
def required_406 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_406 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_406 : Fin 4 → Finset Cell := ![required_199, (placed21 4 (0, 6) required_199), (placed21 0 (0, 1) required_405), (placed21 4 (0, 5) required_405)]
def childrenD_406 : Fin 4 → Finset Cell := ![envelope_199, (placed21 4 (0, 6) envelope_199), (placed21 0 (0, 1) envelope_405), (placed21 4 (0, 5) envelope_405)]
theorem common_sub_406 : commonEnvelope childrenD_406 ⊆ insert (1, 4) required_406 := by decide +kernel
theorem child_required_sub_406 : ∀ j, childrenC_406 j ⊆ insert (1, 4) required_406 := by decide +kernel
theorem child_envelope_sub_406 : ∀ j, childrenD_406 j ⊆ envelope_406 := by decide +kernel
theorem pivot_mem_406 : (1, 4) ∈ envelope_406 := by decide +kernel
theorem children_work_406 : ∀ j, Template HasSnaky 8 (childrenC_406 j) (childrenD_406 j) := by
  intro j
  fin_cases j
  · exact row_works_199.mono (by decide +kernel)
  · exact (placed21_template row_works_199 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_405 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_405 4 (0, 5)).mono (by decide +kernel)
theorem row_works_406 : Template HasSnaky 9 required_406 envelope_406 := by
  refine compose HasSnaky 8 childrenC_406 childrenD_406 children_work_406 (1, 4)
    required_406 envelope_406 pivot_mem_406 child_required_sub_406 child_envelope_sub_406 ?_
  intro b hb
  exact common_sub_406 (mem_commonEnvelope childrenD_406 b hb)
def required_407_i0 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_407_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_407_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) required_5), (placed21 4 (0, 5) required_404)]
def childrenD_407_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) envelope_5), (placed21 4 (0, 5) envelope_404)]
theorem common_sub_407_i0 : commonEnvelope childrenD_407_i0 ⊆ insert (0, 4) required_407_i0 := by decide +kernel
theorem child_required_sub_407_i0 : ∀ j, childrenC_407_i0 j ⊆ insert (0, 4) required_407_i0 := by decide +kernel
theorem child_envelope_sub_407_i0 : ∀ j, childrenD_407_i0 j ⊆ envelope_407_i0 := by decide +kernel
theorem pivot_mem_407_i0 : (0, 4) ∈ envelope_407_i0 := by decide +kernel
theorem children_work_407_i0 : ∀ j, Template HasSnaky 7 (childrenC_407_i0 j) (childrenD_407_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_404 4 (0, 5)).mono (by decide +kernel)
theorem row_works_407_i0 : Template HasSnaky 8 required_407_i0 envelope_407_i0 := by
  refine compose HasSnaky 7 childrenC_407_i0 childrenD_407_i0 children_work_407_i0 (0, 4)
    required_407_i0 envelope_407_i0 pivot_mem_407_i0 child_required_sub_407_i0 child_envelope_sub_407_i0 ?_
  intro b hb
  exact common_sub_407_i0 (mem_commonEnvelope childrenD_407_i0 b hb)
def required_407 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_407 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_407 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) required_7), (placed21 1 (0, 1) required_8), (placed21 2 (2, 0) required_9), required_407_i0]
def childrenD_407 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) envelope_7), (placed21 1 (0, 1) envelope_8), (placed21 2 (2, 0) envelope_9), envelope_407_i0]
theorem common_sub_407 : commonEnvelope childrenD_407 ⊆ insert (1, 4) required_407 := by decide +kernel
theorem child_required_sub_407 : ∀ j, childrenC_407 j ⊆ insert (1, 4) required_407 := by decide +kernel
theorem child_envelope_sub_407 : ∀ j, childrenD_407 j ⊆ envelope_407 := by decide +kernel
theorem pivot_mem_407 : (1, 4) ∈ envelope_407 := by decide +kernel
theorem children_work_407 : ∀ j, Template HasSnaky 8 (childrenC_407 j) (childrenD_407 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact row_works_407_i0.mono (by decide +kernel)
theorem row_works_407 : Template HasSnaky 9 required_407 envelope_407 := by
  refine compose HasSnaky 8 childrenC_407 childrenD_407 children_work_407 (1, 4)
    required_407 envelope_407 pivot_mem_407 child_required_sub_407 child_envelope_sub_407 ?_
  intro b hb
  exact common_sub_407 (mem_commonEnvelope childrenD_407 b hb)
def required_421 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_421 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_421 : Fin 3 → Finset Cell := ![(placed21 1 (0, 1) required_8), (placed21 0 (1, 0) required_11), required_419]
def childrenD_421 : Fin 3 → Finset Cell := ![(placed21 1 (0, 1) envelope_8), (placed21 0 (1, 0) envelope_11), envelope_419]
theorem common_sub_421 : commonEnvelope childrenD_421 ⊆ insert (1, 4) required_421 := by decide +kernel
theorem child_required_sub_421 : ∀ j, childrenC_421 j ⊆ insert (1, 4) required_421 := by decide +kernel
theorem child_envelope_sub_421 : ∀ j, childrenD_421 j ⊆ envelope_421 := by decide +kernel
theorem pivot_mem_421 : (1, 4) ∈ envelope_421 := by decide +kernel
theorem children_work_421 : ∀ j, Template HasSnaky 8 (childrenC_421 j) (childrenD_421 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_419.mono (by decide +kernel)
theorem row_works_421 : Template HasSnaky 9 required_421 envelope_421 := by
  refine compose HasSnaky 8 childrenC_421 childrenD_421 children_work_421 (1, 4)
    required_421 envelope_421 pivot_mem_421 child_required_sub_421 child_envelope_sub_421 ?_
  intro b hb
  exact common_sub_421 (mem_commonEnvelope childrenD_421 b hb)
def required_434_i0 : Finset Cell := ⟨(([(1, 2), (3, 2), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_434_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_434_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 2) required_1), (placed21 2 (5, 0) required_10)]
def childrenD_434_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 2) envelope_1), (placed21 2 (5, 0) envelope_10)]
theorem common_sub_434_i0 : commonEnvelope childrenD_434_i0 ⊆ insert (5, 1) required_434_i0 := by decide +kernel
theorem child_required_sub_434_i0 : ∀ j, childrenC_434_i0 j ⊆ insert (5, 1) required_434_i0 := by decide +kernel
theorem child_envelope_sub_434_i0 : ∀ j, childrenD_434_i0 j ⊆ envelope_434_i0 := by decide +kernel
theorem pivot_mem_434_i0 : (5, 1) ∈ envelope_434_i0 := by decide +kernel
theorem children_work_434_i0 : ∀ j, Template HasSnaky 4 (childrenC_434_i0 j) (childrenD_434_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 4 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_10 2 (5, 0)).mono (by decide +kernel)
theorem row_works_434_i0 : Template HasSnaky 5 required_434_i0 envelope_434_i0 := by
  refine compose HasSnaky 4 childrenC_434_i0 childrenD_434_i0 children_work_434_i0 (5, 1)
    required_434_i0 envelope_434_i0 pivot_mem_434_i0 child_required_sub_434_i0 child_envelope_sub_434_i0 ?_
  intro b hb
  exact common_sub_434_i0 (mem_commonEnvelope childrenD_434_i0 b hb)
def required_434_i1 : Finset Cell := ⟨(([(3, 2), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_434_i1 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_434_i1 : Fin 5 → Finset Cell := ![(placed21 5 (5, 1) required_8), (placed21 0 (3, 1) required_41), (placed21 1 (1, 1) required_253), (placed21 5 (7, 1) required_256), (placed21 0 (3, 1) required_336)]
def childrenD_434_i1 : Fin 5 → Finset Cell := ![(placed21 5 (5, 1) envelope_8), (placed21 0 (3, 1) envelope_41), (placed21 1 (1, 1) envelope_253), (placed21 5 (7, 1) envelope_256), (placed21 0 (3, 1) envelope_336)]
theorem common_sub_434_i1 : commonEnvelope childrenD_434_i1 ⊆ insert (4, 4) required_434_i1 := by decide +kernel
theorem child_required_sub_434_i1 : ∀ j, childrenC_434_i1 j ⊆ insert (4, 4) required_434_i1 := by decide +kernel
theorem child_envelope_sub_434_i1 : ∀ j, childrenD_434_i1 j ⊆ envelope_434_i1 := by decide +kernel
theorem pivot_mem_434_i1 : (4, 4) ∈ envelope_434_i1 := by decide +kernel
theorem children_work_434_i1 : ∀ j, Template HasSnaky 7 (childrenC_434_i1 j) (childrenD_434_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 5 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_41 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_253 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_256 5 (7, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_336 0 (3, 1)).mono (by decide +kernel)
theorem row_works_434_i1 : Template HasSnaky 8 required_434_i1 envelope_434_i1 := by
  refine compose HasSnaky 7 childrenC_434_i1 childrenD_434_i1 children_work_434_i1 (4, 4)
    required_434_i1 envelope_434_i1 pivot_mem_434_i1 child_required_sub_434_i1 child_envelope_sub_434_i1 ?_
  intro b hb
  exact common_sub_434_i1 (mem_commonEnvelope childrenD_434_i1 b hb)
def required_434 : Finset Cell := ⟨(([(1, 2), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_434 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_434 : Fin 3 → Finset Cell := ![(placed21 5 (5, 1) required_80), required_434_i0, required_434_i1]
def childrenD_434 : Fin 3 → Finset Cell := ![(placed21 5 (5, 1) envelope_80), envelope_434_i0, envelope_434_i1]
theorem common_sub_434 : commonEnvelope childrenD_434 ⊆ insert (3, 2) required_434 := by decide +kernel
theorem child_required_sub_434 : ∀ j, childrenC_434 j ⊆ insert (3, 2) required_434 := by decide +kernel
theorem child_envelope_sub_434 : ∀ j, childrenD_434 j ⊆ envelope_434 := by decide +kernel
theorem pivot_mem_434 : (3, 2) ∈ envelope_434 := by decide +kernel
theorem children_work_434 : ∀ j, Template HasSnaky 8 (childrenC_434 j) (childrenD_434 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_80 5 (5, 1)).mono (by decide +kernel)
  · exact row_works_434_i0.mono (by decide +kernel)
  · exact row_works_434_i1.mono (by decide +kernel)
theorem row_works_434 : Template HasSnaky 9 required_434 envelope_434 := by
  refine compose HasSnaky 8 childrenC_434 childrenD_434 children_work_434 (3, 2)
    required_434 envelope_434 pivot_mem_434 child_required_sub_434 child_envelope_sub_434 ?_
  intro b hb
  exact common_sub_434 (mem_commonEnvelope childrenD_434 b hb)
def required_441 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_441 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 3), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_441 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_28), (placed21 2 (4, 1) required_58), required_440]
def childrenD_441 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_28), (placed21 2 (4, 1) envelope_58), envelope_440]
theorem common_sub_441 : commonEnvelope childrenD_441 ⊆ insert (3, 3) required_441 := by decide +kernel
theorem child_required_sub_441 : ∀ j, childrenC_441 j ⊆ insert (3, 3) required_441 := by decide +kernel
theorem child_envelope_sub_441 : ∀ j, childrenD_441 j ⊆ envelope_441 := by decide +kernel
theorem pivot_mem_441 : (3, 3) ∈ envelope_441 := by decide +kernel
theorem children_work_441 : ∀ j, Template HasSnaky 8 (childrenC_441 j) (childrenD_441 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 2 (4, 1)).mono (by decide +kernel)
  · exact row_works_440.mono (by decide +kernel)
theorem row_works_441 : Template HasSnaky 9 required_441 envelope_441 := by
  refine compose HasSnaky 8 childrenC_441 childrenD_441 children_work_441 (3, 3)
    required_441 envelope_441 pivot_mem_441 child_required_sub_441 child_envelope_sub_441 ?_
  intro b hb
  exact common_sub_441 (mem_commonEnvelope childrenD_441 b hb)
def required_442 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_442 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 3), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_442 : Fin 3 → Finset Cell := ![(placed21 7 (5, 4) required_40), (placed21 7 (5, 4) required_149), required_440]
def childrenD_442 : Fin 3 → Finset Cell := ![(placed21 7 (5, 4) envelope_40), (placed21 7 (5, 4) envelope_149), envelope_440]
theorem common_sub_442 : commonEnvelope childrenD_442 ⊆ insert (3, 3) required_442 := by decide +kernel
theorem child_required_sub_442 : ∀ j, childrenC_442 j ⊆ insert (3, 3) required_442 := by decide +kernel
theorem child_envelope_sub_442 : ∀ j, childrenD_442 j ⊆ envelope_442 := by decide +kernel
theorem pivot_mem_442 : (3, 3) ∈ envelope_442 := by decide +kernel
theorem children_work_442 : ∀ j, Template HasSnaky 8 (childrenC_442 j) (childrenD_442 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 7 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_149 7 (5, 4)).mono (by decide +kernel)
  · exact row_works_440.mono (by decide +kernel)
theorem row_works_442 : Template HasSnaky 9 required_442 envelope_442 := by
  refine compose HasSnaky 8 childrenC_442 childrenD_442 children_work_442 (3, 3)
    required_442 envelope_442 pivot_mem_442 child_required_sub_442 child_envelope_sub_442 ?_
  intro b hb
  exact common_sub_442 (mem_commonEnvelope childrenD_442 b hb)
def height_322 : ℕ := 9
def childrenH_322 : Fin 3 → ℕ := ![height_7, height_9, height_321]
theorem height_exact_322 : height_322 = 1 + Finset.univ.sup childrenH_322 := by decide +kernel
theorem required_origin_322 : ∀ x ∈ required_322,
    (∃ j, x ∈ childrenC_322 j) ∨ ∀ j, x ∈ childrenD_322 j := by decide +kernel
theorem required_exact_322 : required_322 =
    ((Finset.univ.biUnion childrenC_322) ∪ commonEnvelope childrenD_322).erase (4, 4) := by
  exact required_eq_combination childrenC_322 childrenD_322 (4, 4) required_322
    (by decide +kernel) child_required_sub_322 common_sub_322 required_origin_322
theorem envelope_origin_322 : ∀ x ∈ envelope_322,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_322 j := by decide +kernel
theorem envelope_exact_322 : envelope_322 =
    insert (4, 4) (Finset.univ.biUnion childrenD_322) := by
  exact envelope_eq_combination childrenD_322 (4, 4) envelope_322
    pivot_mem_322 child_envelope_sub_322 envelope_origin_322
def checked_322 : CheckedCard where
  required := required_322
  envelope := envelope_322
  height := height_322
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_322
def height_325 : ℕ := 9
def childrenH_325 : Fin 2 → ℕ := ![height_5, height_321]
theorem height_exact_325 : height_325 = 1 + Finset.univ.sup childrenH_325 := by decide +kernel
theorem required_origin_325 : ∀ x ∈ required_325,
    (∃ j, x ∈ childrenC_325 j) ∨ ∀ j, x ∈ childrenD_325 j := by decide +kernel
theorem required_exact_325 : required_325 =
    ((Finset.univ.biUnion childrenC_325) ∪ commonEnvelope childrenD_325).erase (3, 4) := by
  exact required_eq_combination childrenC_325 childrenD_325 (3, 4) required_325
    (by decide +kernel) child_required_sub_325 common_sub_325 required_origin_325
theorem envelope_origin_325 : ∀ x ∈ envelope_325,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_325 j := by decide +kernel
theorem envelope_exact_325 : envelope_325 =
    insert (3, 4) (Finset.univ.biUnion childrenD_325) := by
  exact envelope_eq_combination childrenD_325 (3, 4) envelope_325
    pivot_mem_325 child_envelope_sub_325 envelope_origin_325
def checked_325 : CheckedCard where
  required := required_325
  envelope := envelope_325
  height := height_325
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_325
def height_326 : ℕ := 9
def childrenH_326 : Fin 2 → ℕ := ![height_3, height_321]
theorem height_exact_326 : height_326 = 1 + Finset.univ.sup childrenH_326 := by decide +kernel
theorem required_origin_326 : ∀ x ∈ required_326,
    (∃ j, x ∈ childrenC_326 j) ∨ ∀ j, x ∈ childrenD_326 j := by decide +kernel
theorem required_exact_326 : required_326 =
    ((Finset.univ.biUnion childrenC_326) ∪ commonEnvelope childrenD_326).erase (2, 4) := by
  exact required_eq_combination childrenC_326 childrenD_326 (2, 4) required_326
    (by decide +kernel) child_required_sub_326 common_sub_326 required_origin_326
theorem envelope_origin_326 : ∀ x ∈ envelope_326,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_326 j := by decide +kernel
theorem envelope_exact_326 : envelope_326 =
    insert (2, 4) (Finset.univ.biUnion childrenD_326) := by
  exact envelope_eq_combination childrenD_326 (2, 4) envelope_326
    pivot_mem_326 child_envelope_sub_326 envelope_origin_326
def checked_326 : CheckedCard where
  required := required_326
  envelope := envelope_326
  height := height_326
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_326
def height_327 : ℕ := 9
def childrenH_327 : Fin 2 → ℕ := ![height_32, height_321]
theorem height_exact_327 : height_327 = 1 + Finset.univ.sup childrenH_327 := by decide +kernel
theorem required_origin_327 : ∀ x ∈ required_327,
    (∃ j, x ∈ childrenC_327 j) ∨ ∀ j, x ∈ childrenD_327 j := by decide +kernel
theorem required_exact_327 : required_327 =
    ((Finset.univ.biUnion childrenC_327) ∪ commonEnvelope childrenD_327).erase (4, 4) := by
  exact required_eq_combination childrenC_327 childrenD_327 (4, 4) required_327
    (by decide +kernel) child_required_sub_327 common_sub_327 required_origin_327
theorem envelope_origin_327 : ∀ x ∈ envelope_327,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_327 j := by decide +kernel
theorem envelope_exact_327 : envelope_327 =
    insert (4, 4) (Finset.univ.biUnion childrenD_327) := by
  exact envelope_eq_combination childrenD_327 (4, 4) envelope_327
    pivot_mem_327 child_envelope_sub_327 envelope_origin_327
def checked_327 : CheckedCard where
  required := required_327
  envelope := envelope_327
  height := height_327
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_327
def height_328 : ℕ := 9
def childrenH_328 : Fin 3 → ℕ := ![height_7, height_9, height_321]
theorem height_exact_328 : height_328 = 1 + Finset.univ.sup childrenH_328 := by decide +kernel
theorem required_origin_328 : ∀ x ∈ required_328,
    (∃ j, x ∈ childrenC_328 j) ∨ ∀ j, x ∈ childrenD_328 j := by decide +kernel
theorem required_exact_328 : required_328 =
    ((Finset.univ.biUnion childrenC_328) ∪ commonEnvelope childrenD_328).erase (3, 4) := by
  exact required_eq_combination childrenC_328 childrenD_328 (3, 4) required_328
    (by decide +kernel) child_required_sub_328 common_sub_328 required_origin_328
theorem envelope_origin_328 : ∀ x ∈ envelope_328,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_328 j := by decide +kernel
theorem envelope_exact_328 : envelope_328 =
    insert (3, 4) (Finset.univ.biUnion childrenD_328) := by
  exact envelope_eq_combination childrenD_328 (3, 4) envelope_328
    pivot_mem_328 child_envelope_sub_328 envelope_origin_328
def checked_328 : CheckedCard where
  required := required_328
  envelope := envelope_328
  height := height_328
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_328
def height_330 : ℕ := 9
def childrenH_330 : Fin 3 → ℕ := ![height_7, height_9, height_321]
theorem height_exact_330 : height_330 = 1 + Finset.univ.sup childrenH_330 := by decide +kernel
theorem required_origin_330 : ∀ x ∈ required_330,
    (∃ j, x ∈ childrenC_330 j) ∨ ∀ j, x ∈ childrenD_330 j := by decide +kernel
theorem required_exact_330 : required_330 =
    ((Finset.univ.biUnion childrenC_330) ∪ commonEnvelope childrenD_330).erase (3, 4) := by
  exact required_eq_combination childrenC_330 childrenD_330 (3, 4) required_330
    (by decide +kernel) child_required_sub_330 common_sub_330 required_origin_330
theorem envelope_origin_330 : ∀ x ∈ envelope_330,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_330 j := by decide +kernel
theorem envelope_exact_330 : envelope_330 =
    insert (3, 4) (Finset.univ.biUnion childrenD_330) := by
  exact envelope_eq_combination childrenD_330 (3, 4) envelope_330
    pivot_mem_330 child_envelope_sub_330 envelope_origin_330
def checked_330 : CheckedCard where
  required := required_330
  envelope := envelope_330
  height := height_330
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_330
def height_368 : ℕ := 9
def childrenH_368 : Fin 7 → ℕ := ![height_14, height_31, height_181, height_189, height_257, height_355, height_367]
theorem height_exact_368 : height_368 = 1 + Finset.univ.sup childrenH_368 := by decide +kernel
theorem required_origin_368 : ∀ x ∈ required_368,
    (∃ j, x ∈ childrenC_368 j) ∨ ∀ j, x ∈ childrenD_368 j := by decide +kernel
theorem required_exact_368 : required_368 =
    ((Finset.univ.biUnion childrenC_368) ∪ commonEnvelope childrenD_368).erase (4, 5) := by
  exact required_eq_combination childrenC_368 childrenD_368 (4, 5) required_368
    (by decide +kernel) child_required_sub_368 common_sub_368 required_origin_368
theorem envelope_origin_368 : ∀ x ∈ envelope_368,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_368 j := by decide +kernel
theorem envelope_exact_368 : envelope_368 =
    insert (4, 5) (Finset.univ.biUnion childrenD_368) := by
  exact envelope_eq_combination childrenD_368 (4, 5) envelope_368
    pivot_mem_368 child_envelope_sub_368 envelope_origin_368
def checked_368 : CheckedCard where
  required := required_368
  envelope := envelope_368
  height := height_368
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_368
def height_380_i0 : ℕ := 8
def childrenH_380_i0 : Fin 2 → ℕ := ![height_5, height_379]
theorem height_exact_380_i0 : height_380_i0 = 1 + Finset.univ.sup childrenH_380_i0 := by decide +kernel
theorem required_origin_380_i0 : ∀ x ∈ required_380_i0,
    (∃ j, x ∈ childrenC_380_i0 j) ∨ ∀ j, x ∈ childrenD_380_i0 j := by decide +kernel
theorem required_exact_380_i0 : required_380_i0 =
    ((Finset.univ.biUnion childrenC_380_i0) ∪ commonEnvelope childrenD_380_i0).erase (3, 0) := by
  exact required_eq_combination childrenC_380_i0 childrenD_380_i0 (3, 0) required_380_i0
    (by decide +kernel) child_required_sub_380_i0 common_sub_380_i0 required_origin_380_i0
theorem envelope_origin_380_i0 : ∀ x ∈ envelope_380_i0,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_380_i0 j := by decide +kernel
theorem envelope_exact_380_i0 : envelope_380_i0 =
    insert (3, 0) (Finset.univ.biUnion childrenD_380_i0) := by
  exact envelope_eq_combination childrenD_380_i0 (3, 0) envelope_380_i0
    pivot_mem_380_i0 child_envelope_sub_380_i0 envelope_origin_380_i0
def checked_380_i0 : CheckedCard where
  required := required_380_i0
  envelope := envelope_380_i0
  height := height_380_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_380_i0
def height_380 : ℕ := 9
def childrenH_380 : Fin 2 → ℕ := ![height_5, height_380_i0]
theorem height_exact_380 : height_380 = 1 + Finset.univ.sup childrenH_380 := by decide +kernel
theorem required_origin_380 : ∀ x ∈ required_380,
    (∃ j, x ∈ childrenC_380 j) ∨ ∀ j, x ∈ childrenD_380 j := by decide +kernel
theorem required_exact_380 : required_380 =
    ((Finset.univ.biUnion childrenC_380) ∪ commonEnvelope childrenD_380).erase (3, 2) := by
  exact required_eq_combination childrenC_380 childrenD_380 (3, 2) required_380
    (by decide +kernel) child_required_sub_380 common_sub_380 required_origin_380
theorem envelope_origin_380 : ∀ x ∈ envelope_380,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_380 j := by decide +kernel
theorem envelope_exact_380 : envelope_380 =
    insert (3, 2) (Finset.univ.biUnion childrenD_380) := by
  exact envelope_eq_combination childrenD_380 (3, 2) envelope_380
    pivot_mem_380 child_envelope_sub_380 envelope_origin_380
def checked_380 : CheckedCard where
  required := required_380
  envelope := envelope_380
  height := height_380
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_380
def height_396 : ℕ := 9
def childrenH_396 : Fin 3 → ℕ := ![height_7, height_9, height_395]
theorem height_exact_396 : height_396 = 1 + Finset.univ.sup childrenH_396 := by decide +kernel
theorem required_origin_396 : ∀ x ∈ required_396,
    (∃ j, x ∈ childrenC_396 j) ∨ ∀ j, x ∈ childrenD_396 j := by decide +kernel
theorem required_exact_396 : required_396 =
    ((Finset.univ.biUnion childrenC_396) ∪ commonEnvelope childrenD_396).erase (2, 6) := by
  exact required_eq_combination childrenC_396 childrenD_396 (2, 6) required_396
    (by decide +kernel) child_required_sub_396 common_sub_396 required_origin_396
theorem envelope_origin_396 : ∀ x ∈ envelope_396,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_396 j := by decide +kernel
theorem envelope_exact_396 : envelope_396 =
    insert (2, 6) (Finset.univ.biUnion childrenD_396) := by
  exact envelope_eq_combination childrenD_396 (2, 6) envelope_396
    pivot_mem_396 child_envelope_sub_396 envelope_origin_396
def checked_396 : CheckedCard where
  required := required_396
  envelope := envelope_396
  height := height_396
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_396
def height_397 : ℕ := 9
def childrenH_397 : Fin 4 → ℕ := ![height_8, height_161, height_162, height_395]
theorem height_exact_397 : height_397 = 1 + Finset.univ.sup childrenH_397 := by decide +kernel
theorem required_origin_397 : ∀ x ∈ required_397,
    (∃ j, x ∈ childrenC_397 j) ∨ ∀ j, x ∈ childrenD_397 j := by decide +kernel
theorem required_exact_397 : required_397 =
    ((Finset.univ.biUnion childrenC_397) ∪ commonEnvelope childrenD_397).erase (3, 3) := by
  exact required_eq_combination childrenC_397 childrenD_397 (3, 3) required_397
    (by decide +kernel) child_required_sub_397 common_sub_397 required_origin_397
theorem envelope_origin_397 : ∀ x ∈ envelope_397,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_397 j := by decide +kernel
theorem envelope_exact_397 : envelope_397 =
    insert (3, 3) (Finset.univ.biUnion childrenD_397) := by
  exact envelope_eq_combination childrenD_397 (3, 3) envelope_397
    pivot_mem_397 child_envelope_sub_397 envelope_origin_397
def checked_397 : CheckedCard where
  required := required_397
  envelope := envelope_397
  height := height_397
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_397
def height_398 : ℕ := 9
def childrenH_398 : Fin 5 → ℕ := ![height_171, height_197, height_197, height_285, height_395]
theorem height_exact_398 : height_398 = 1 + Finset.univ.sup childrenH_398 := by decide +kernel
theorem required_origin_398 : ∀ x ∈ required_398,
    (∃ j, x ∈ childrenC_398 j) ∨ ∀ j, x ∈ childrenD_398 j := by decide +kernel
theorem required_exact_398 : required_398 =
    ((Finset.univ.biUnion childrenC_398) ∪ commonEnvelope childrenD_398).erase (3, 3) := by
  exact required_eq_combination childrenC_398 childrenD_398 (3, 3) required_398
    (by decide +kernel) child_required_sub_398 common_sub_398 required_origin_398
theorem envelope_origin_398 : ∀ x ∈ envelope_398,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_398 j := by decide +kernel
theorem envelope_exact_398 : envelope_398 =
    insert (3, 3) (Finset.univ.biUnion childrenD_398) := by
  exact envelope_eq_combination childrenD_398 (3, 3) envelope_398
    pivot_mem_398 child_envelope_sub_398 envelope_origin_398
def checked_398 : CheckedCard where
  required := required_398
  envelope := envelope_398
  height := height_398
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_398
def height_400 : ℕ := 9
def childrenH_400 : Fin 2 → ℕ := ![height_5, height_395]
theorem height_exact_400 : height_400 = 1 + Finset.univ.sup childrenH_400 := by decide +kernel
theorem required_origin_400 : ∀ x ∈ required_400,
    (∃ j, x ∈ childrenC_400 j) ∨ ∀ j, x ∈ childrenD_400 j := by decide +kernel
theorem required_exact_400 : required_400 =
    ((Finset.univ.biUnion childrenC_400) ∪ commonEnvelope childrenD_400).erase (3, 2) := by
  exact required_eq_combination childrenC_400 childrenD_400 (3, 2) required_400
    (by decide +kernel) child_required_sub_400 common_sub_400 required_origin_400
theorem envelope_origin_400 : ∀ x ∈ envelope_400,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_400 j := by decide +kernel
theorem envelope_exact_400 : envelope_400 =
    insert (3, 2) (Finset.univ.biUnion childrenD_400) := by
  exact envelope_eq_combination childrenD_400 (3, 2) envelope_400
    pivot_mem_400 child_envelope_sub_400 envelope_origin_400
def checked_400 : CheckedCard where
  required := required_400
  envelope := envelope_400
  height := height_400
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_400
def height_406 : ℕ := 9
def childrenH_406 : Fin 4 → ℕ := ![height_199, height_199, height_405, height_405]
theorem height_exact_406 : height_406 = 1 + Finset.univ.sup childrenH_406 := by decide +kernel
theorem required_origin_406 : ∀ x ∈ required_406,
    (∃ j, x ∈ childrenC_406 j) ∨ ∀ j, x ∈ childrenD_406 j := by decide +kernel
theorem required_exact_406 : required_406 =
    ((Finset.univ.biUnion childrenC_406) ∪ commonEnvelope childrenD_406).erase (1, 4) := by
  exact required_eq_combination childrenC_406 childrenD_406 (1, 4) required_406
    (by decide +kernel) child_required_sub_406 common_sub_406 required_origin_406
theorem envelope_origin_406 : ∀ x ∈ envelope_406,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_406 j := by decide +kernel
theorem envelope_exact_406 : envelope_406 =
    insert (1, 4) (Finset.univ.biUnion childrenD_406) := by
  exact envelope_eq_combination childrenD_406 (1, 4) envelope_406
    pivot_mem_406 child_envelope_sub_406 envelope_origin_406
def checked_406 : CheckedCard where
  required := required_406
  envelope := envelope_406
  height := height_406
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_406
def height_407_i0 : ℕ := 8
def childrenH_407_i0 : Fin 2 → ℕ := ![height_5, height_404]
theorem height_exact_407_i0 : height_407_i0 = 1 + Finset.univ.sup childrenH_407_i0 := by decide +kernel
theorem required_origin_407_i0 : ∀ x ∈ required_407_i0,
    (∃ j, x ∈ childrenC_407_i0 j) ∨ ∀ j, x ∈ childrenD_407_i0 j := by decide +kernel
theorem required_exact_407_i0 : required_407_i0 =
    ((Finset.univ.biUnion childrenC_407_i0) ∪ commonEnvelope childrenD_407_i0).erase (0, 4) := by
  exact required_eq_combination childrenC_407_i0 childrenD_407_i0 (0, 4) required_407_i0
    (by decide +kernel) child_required_sub_407_i0 common_sub_407_i0 required_origin_407_i0
theorem envelope_origin_407_i0 : ∀ x ∈ envelope_407_i0,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_407_i0 j := by decide +kernel
theorem envelope_exact_407_i0 : envelope_407_i0 =
    insert (0, 4) (Finset.univ.biUnion childrenD_407_i0) := by
  exact envelope_eq_combination childrenD_407_i0 (0, 4) envelope_407_i0
    pivot_mem_407_i0 child_envelope_sub_407_i0 envelope_origin_407_i0
def checked_407_i0 : CheckedCard where
  required := required_407_i0
  envelope := envelope_407_i0
  height := height_407_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_407_i0
def height_407 : ℕ := 9
def childrenH_407 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_407_i0]
theorem height_exact_407 : height_407 = 1 + Finset.univ.sup childrenH_407 := by decide +kernel
theorem required_origin_407 : ∀ x ∈ required_407,
    (∃ j, x ∈ childrenC_407 j) ∨ ∀ j, x ∈ childrenD_407 j := by decide +kernel
theorem required_exact_407 : required_407 =
    ((Finset.univ.biUnion childrenC_407) ∪ commonEnvelope childrenD_407).erase (1, 4) := by
  exact required_eq_combination childrenC_407 childrenD_407 (1, 4) required_407
    (by decide +kernel) child_required_sub_407 common_sub_407 required_origin_407
theorem envelope_origin_407 : ∀ x ∈ envelope_407,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_407 j := by decide +kernel
theorem envelope_exact_407 : envelope_407 =
    insert (1, 4) (Finset.univ.biUnion childrenD_407) := by
  exact envelope_eq_combination childrenD_407 (1, 4) envelope_407
    pivot_mem_407 child_envelope_sub_407 envelope_origin_407
def checked_407 : CheckedCard where
  required := required_407
  envelope := envelope_407
  height := height_407
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_407
def height_421 : ℕ := 9
def childrenH_421 : Fin 3 → ℕ := ![height_8, height_11, height_419]
theorem height_exact_421 : height_421 = 1 + Finset.univ.sup childrenH_421 := by decide +kernel
theorem required_origin_421 : ∀ x ∈ required_421,
    (∃ j, x ∈ childrenC_421 j) ∨ ∀ j, x ∈ childrenD_421 j := by decide +kernel
theorem required_exact_421 : required_421 =
    ((Finset.univ.biUnion childrenC_421) ∪ commonEnvelope childrenD_421).erase (1, 4) := by
  exact required_eq_combination childrenC_421 childrenD_421 (1, 4) required_421
    (by decide +kernel) child_required_sub_421 common_sub_421 required_origin_421
theorem envelope_origin_421 : ∀ x ∈ envelope_421,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_421 j := by decide +kernel
theorem envelope_exact_421 : envelope_421 =
    insert (1, 4) (Finset.univ.biUnion childrenD_421) := by
  exact envelope_eq_combination childrenD_421 (1, 4) envelope_421
    pivot_mem_421 child_envelope_sub_421 envelope_origin_421
def checked_421 : CheckedCard where
  required := required_421
  envelope := envelope_421
  height := height_421
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_421
def height_434_i0 : ℕ := 5
def childrenH_434_i0 : Fin 2 → ℕ := ![height_1, height_10]
theorem height_exact_434_i0 : height_434_i0 = 1 + Finset.univ.sup childrenH_434_i0 := by decide +kernel
theorem required_origin_434_i0 : ∀ x ∈ required_434_i0,
    (∃ j, x ∈ childrenC_434_i0 j) ∨ ∀ j, x ∈ childrenD_434_i0 j := by decide +kernel
theorem required_exact_434_i0 : required_434_i0 =
    ((Finset.univ.biUnion childrenC_434_i0) ∪ commonEnvelope childrenD_434_i0).erase (5, 1) := by
  exact required_eq_combination childrenC_434_i0 childrenD_434_i0 (5, 1) required_434_i0
    (by decide +kernel) child_required_sub_434_i0 common_sub_434_i0 required_origin_434_i0
theorem envelope_origin_434_i0 : ∀ x ∈ envelope_434_i0,
    x = (5, 1) ∨ ∃ j, x ∈ childrenD_434_i0 j := by decide +kernel
theorem envelope_exact_434_i0 : envelope_434_i0 =
    insert (5, 1) (Finset.univ.biUnion childrenD_434_i0) := by
  exact envelope_eq_combination childrenD_434_i0 (5, 1) envelope_434_i0
    pivot_mem_434_i0 child_envelope_sub_434_i0 envelope_origin_434_i0
def checked_434_i0 : CheckedCard where
  required := required_434_i0
  envelope := envelope_434_i0
  height := height_434_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_434_i0
def height_434_i1 : ℕ := 8
def childrenH_434_i1 : Fin 5 → ℕ := ![height_8, height_41, height_253, height_256, height_336]
theorem height_exact_434_i1 : height_434_i1 = 1 + Finset.univ.sup childrenH_434_i1 := by decide +kernel
theorem required_origin_434_i1 : ∀ x ∈ required_434_i1,
    (∃ j, x ∈ childrenC_434_i1 j) ∨ ∀ j, x ∈ childrenD_434_i1 j := by decide +kernel
theorem required_exact_434_i1 : required_434_i1 =
    ((Finset.univ.biUnion childrenC_434_i1) ∪ commonEnvelope childrenD_434_i1).erase (4, 4) := by
  exact required_eq_combination childrenC_434_i1 childrenD_434_i1 (4, 4) required_434_i1
    (by decide +kernel) child_required_sub_434_i1 common_sub_434_i1 required_origin_434_i1
theorem envelope_origin_434_i1 : ∀ x ∈ envelope_434_i1,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_434_i1 j := by decide +kernel
theorem envelope_exact_434_i1 : envelope_434_i1 =
    insert (4, 4) (Finset.univ.biUnion childrenD_434_i1) := by
  exact envelope_eq_combination childrenD_434_i1 (4, 4) envelope_434_i1
    pivot_mem_434_i1 child_envelope_sub_434_i1 envelope_origin_434_i1
def checked_434_i1 : CheckedCard where
  required := required_434_i1
  envelope := envelope_434_i1
  height := height_434_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_434_i1
def height_434 : ℕ := 9
def childrenH_434 : Fin 3 → ℕ := ![height_80, height_434_i0, height_434_i1]
theorem height_exact_434 : height_434 = 1 + Finset.univ.sup childrenH_434 := by decide +kernel
theorem required_origin_434 : ∀ x ∈ required_434,
    (∃ j, x ∈ childrenC_434 j) ∨ ∀ j, x ∈ childrenD_434 j := by decide +kernel
theorem required_exact_434 : required_434 =
    ((Finset.univ.biUnion childrenC_434) ∪ commonEnvelope childrenD_434).erase (3, 2) := by
  exact required_eq_combination childrenC_434 childrenD_434 (3, 2) required_434
    (by decide +kernel) child_required_sub_434 common_sub_434 required_origin_434
theorem envelope_origin_434 : ∀ x ∈ envelope_434,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_434 j := by decide +kernel
theorem envelope_exact_434 : envelope_434 =
    insert (3, 2) (Finset.univ.biUnion childrenD_434) := by
  exact envelope_eq_combination childrenD_434 (3, 2) envelope_434
    pivot_mem_434 child_envelope_sub_434 envelope_origin_434
def checked_434 : CheckedCard where
  required := required_434
  envelope := envelope_434
  height := height_434
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_434
def height_441 : ℕ := 9
def childrenH_441 : Fin 3 → ℕ := ![height_28, height_58, height_440]
theorem height_exact_441 : height_441 = 1 + Finset.univ.sup childrenH_441 := by decide +kernel
theorem required_origin_441 : ∀ x ∈ required_441,
    (∃ j, x ∈ childrenC_441 j) ∨ ∀ j, x ∈ childrenD_441 j := by decide +kernel
theorem required_exact_441 : required_441 =
    ((Finset.univ.biUnion childrenC_441) ∪ commonEnvelope childrenD_441).erase (3, 3) := by
  exact required_eq_combination childrenC_441 childrenD_441 (3, 3) required_441
    (by decide +kernel) child_required_sub_441 common_sub_441 required_origin_441
theorem envelope_origin_441 : ∀ x ∈ envelope_441,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_441 j := by decide +kernel
theorem envelope_exact_441 : envelope_441 =
    insert (3, 3) (Finset.univ.biUnion childrenD_441) := by
  exact envelope_eq_combination childrenD_441 (3, 3) envelope_441
    pivot_mem_441 child_envelope_sub_441 envelope_origin_441
def checked_441 : CheckedCard where
  required := required_441
  envelope := envelope_441
  height := height_441
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_441
def height_442 : ℕ := 9
def childrenH_442 : Fin 3 → ℕ := ![height_40, height_149, height_440]
theorem height_exact_442 : height_442 = 1 + Finset.univ.sup childrenH_442 := by decide +kernel
theorem required_origin_442 : ∀ x ∈ required_442,
    (∃ j, x ∈ childrenC_442 j) ∨ ∀ j, x ∈ childrenD_442 j := by decide +kernel
theorem required_exact_442 : required_442 =
    ((Finset.univ.biUnion childrenC_442) ∪ commonEnvelope childrenD_442).erase (3, 3) := by
  exact required_eq_combination childrenC_442 childrenD_442 (3, 3) required_442
    (by decide +kernel) child_required_sub_442 common_sub_442 required_origin_442
theorem envelope_origin_442 : ∀ x ∈ envelope_442,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_442 j := by decide +kernel
theorem envelope_exact_442 : envelope_442 =
    insert (3, 3) (Finset.univ.biUnion childrenD_442) := by
  exact envelope_eq_combination childrenD_442 (3, 3) envelope_442
    pivot_mem_442 child_envelope_sub_442 envelope_origin_442
def checked_442 : CheckedCard where
  required := required_442
  envelope := envelope_442
  height := height_442
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_442
end SnakyPrototype.Certificate21

end OAI
