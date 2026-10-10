import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_356_i0 : Finset Cell := ⟨(([(0, 3), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_356_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_356_i0 : Fin 2 → Finset Cell := ![(placed21 2 (3, 2) required_21), (placed21 7 (4, 5) required_121)]
def childrenD_356_i0 : Fin 2 → Finset Cell := ![(placed21 2 (3, 2) envelope_21), (placed21 7 (4, 5) envelope_121)]
theorem common_sub_356_i0 : commonEnvelope childrenD_356_i0 ⊆ insert (2, 3) required_356_i0 := by decide +kernel
theorem child_required_sub_356_i0 : ∀ j, childrenC_356_i0 j ⊆ insert (2, 3) required_356_i0 := by decide +kernel
theorem child_envelope_sub_356_i0 : ∀ j, childrenD_356_i0 j ⊆ envelope_356_i0 := by decide +kernel
theorem pivot_mem_356_i0 : (2, 3) ∈ envelope_356_i0 := by decide +kernel
theorem children_work_356_i0 : ∀ j, Template HasSnaky 3 (childrenC_356_i0 j) (childrenD_356_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_121 7 (4, 5)).mono (by decide +kernel)
theorem row_works_356_i0 : Template HasSnaky 4 required_356_i0 envelope_356_i0 := by
  refine compose HasSnaky 3 childrenC_356_i0 childrenD_356_i0 children_work_356_i0 (2, 3)
    required_356_i0 envelope_356_i0 pivot_mem_356_i0 child_required_sub_356_i0 child_envelope_sub_356_i0 ?_
  intro b hb
  exact common_sub_356_i0 (mem_commonEnvelope childrenD_356_i0 b hb)
def required_356 : Finset Cell := ⟨(([(0, 3), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_356 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_356 : Fin 3 → Finset Cell := ![(placed21 4 (3, 6) required_7), (placed21 1 (2, 2) required_8), required_356_i0]
def childrenD_356 : Fin 3 → Finset Cell := ![(placed21 4 (3, 6) envelope_7), (placed21 1 (2, 2) envelope_8), envelope_356_i0]
theorem common_sub_356 : commonEnvelope childrenD_356 ⊆ insert (3, 5) required_356 := by decide +kernel
theorem child_required_sub_356 : ∀ j, childrenC_356 j ⊆ insert (3, 5) required_356 := by decide +kernel
theorem child_envelope_sub_356 : ∀ j, childrenD_356 j ⊆ envelope_356 := by decide +kernel
theorem pivot_mem_356 : (3, 5) ∈ envelope_356 := by decide +kernel
theorem children_work_356 : ∀ j, Template HasSnaky 4 (childrenC_356 j) (childrenD_356 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (2, 2)).mono (by decide +kernel)
  · exact row_works_356_i0.mono (by decide +kernel)
theorem row_works_356 : Template HasSnaky 5 required_356 envelope_356 := by
  refine compose HasSnaky 4 childrenC_356 childrenD_356 children_work_356 (3, 5)
    required_356 envelope_356 pivot_mem_356 child_required_sub_356 child_envelope_sub_356 ?_
  intro b hb
  exact common_sub_356 (mem_commonEnvelope childrenD_356 b hb)
def required_357_i2 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_357_i2 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_357_i2 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_3), (placed21 2 (4, 3) required_5)]
def childrenD_357_i2 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_3), (placed21 2 (4, 3) envelope_5)]
theorem common_sub_357_i2 : commonEnvelope childrenD_357_i2 ⊆ insert (1, 4) required_357_i2 := by decide +kernel
theorem child_required_sub_357_i2 : ∀ j, childrenC_357_i2 j ⊆ insert (1, 4) required_357_i2 := by decide +kernel
theorem child_envelope_sub_357_i2 : ∀ j, childrenD_357_i2 j ⊆ envelope_357_i2 := by decide +kernel
theorem pivot_mem_357_i2 : (1, 4) ∈ envelope_357_i2 := by decide +kernel
theorem children_work_357_i2 : ∀ j, Template HasSnaky 1 (childrenC_357_i2 j) (childrenD_357_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 2 (4, 3)).mono (by decide +kernel)
theorem row_works_357_i2 : Template HasSnaky 2 required_357_i2 envelope_357_i2 := by
  refine compose HasSnaky 1 childrenC_357_i2 childrenD_357_i2 children_work_357_i2 (1, 4)
    required_357_i2 envelope_357_i2 pivot_mem_357_i2 child_required_sub_357_i2 child_envelope_sub_357_i2 ?_
  intro b hb
  exact common_sub_357_i2 (mem_commonEnvelope childrenD_357_i2 b hb)
def required_357_i1 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_357_i1 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_357_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_4), required_357_i2]
def childrenD_357_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_4), envelope_357_i2]
theorem common_sub_357_i1 : commonEnvelope childrenD_357_i1 ⊆ insert (1, 3) required_357_i1 := by decide +kernel
theorem child_required_sub_357_i1 : ∀ j, childrenC_357_i1 j ⊆ insert (1, 3) required_357_i1 := by decide +kernel
theorem child_envelope_sub_357_i1 : ∀ j, childrenD_357_i1 j ⊆ envelope_357_i1 := by decide +kernel
theorem pivot_mem_357_i1 : (1, 3) ∈ envelope_357_i1 := by decide +kernel
theorem children_work_357_i1 : ∀ j, Template HasSnaky 2 (childrenC_357_i1 j) (childrenD_357_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 6 (4, 3)).mono (by decide +kernel)
  · exact row_works_357_i2.mono (by decide +kernel)
theorem row_works_357_i1 : Template HasSnaky 3 required_357_i1 envelope_357_i1 := by
  refine compose HasSnaky 2 childrenC_357_i1 childrenD_357_i1 children_work_357_i1 (1, 3)
    required_357_i1 envelope_357_i1 pivot_mem_357_i1 child_required_sub_357_i1 child_envelope_sub_357_i1 ?_
  intro b hb
  exact common_sub_357_i1 (mem_commonEnvelope childrenD_357_i1 b hb)
def required_357_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_357_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_357_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 0) required_5), required_357_i1]
def childrenD_357_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 0) envelope_5), envelope_357_i1]
theorem common_sub_357_i0 : commonEnvelope childrenD_357_i0 ⊆ insert (4, 3) required_357_i0 := by decide +kernel
theorem child_required_sub_357_i0 : ∀ j, childrenC_357_i0 j ⊆ insert (4, 3) required_357_i0 := by decide +kernel
theorem child_envelope_sub_357_i0 : ∀ j, childrenD_357_i0 j ⊆ envelope_357_i0 := by decide +kernel
theorem pivot_mem_357_i0 : (4, 3) ∈ envelope_357_i0 := by decide +kernel
theorem children_work_357_i0 : ∀ j, Template HasSnaky 3 (childrenC_357_i0 j) (childrenD_357_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 0)).mono (by decide +kernel)
  · exact row_works_357_i1.mono (by decide +kernel)
theorem row_works_357_i0 : Template HasSnaky 4 required_357_i0 envelope_357_i0 := by
  refine compose HasSnaky 3 childrenC_357_i0 childrenD_357_i0 children_work_357_i0 (4, 3)
    required_357_i0 envelope_357_i0 pivot_mem_357_i0 child_required_sub_357_i0 child_envelope_sub_357_i0 ?_
  intro b hb
  exact common_sub_357_i0 (mem_commonEnvelope childrenD_357_i0 b hb)
def required_357 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_357 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_357 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) required_5), required_357_i0]
def childrenD_357 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) envelope_5), envelope_357_i0]
theorem common_sub_357 : commonEnvelope childrenD_357 ⊆ insert (2, 3) required_357 := by decide +kernel
theorem child_required_sub_357 : ∀ j, childrenC_357 j ⊆ insert (2, 3) required_357 := by decide +kernel
theorem child_envelope_sub_357 : ∀ j, childrenD_357 j ⊆ envelope_357 := by decide +kernel
theorem pivot_mem_357 : (2, 3) ∈ envelope_357 := by decide +kernel
theorem children_work_357 : ∀ j, Template HasSnaky 4 (childrenC_357 j) (childrenD_357 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (3, 0)).mono (by decide +kernel)
  · exact row_works_357_i0.mono (by decide +kernel)
theorem row_works_357 : Template HasSnaky 5 required_357 envelope_357 := by
  refine compose HasSnaky 4 childrenC_357 childrenD_357 children_work_357 (2, 3)
    required_357 envelope_357 pivot_mem_357 child_required_sub_357 child_envelope_sub_357 ?_
  intro b hb
  exact common_sub_357 (mem_commonEnvelope childrenD_357 b hb)
def required_359_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_359_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 6), (0, 7), (0, 8), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_359_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) required_5), (placed21 2 (2, 2) required_9)]
def childrenD_359_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) envelope_5), (placed21 2 (2, 2) envelope_9)]
theorem common_sub_359_i0 : commonEnvelope childrenD_359_i0 ⊆ insert (1, 6) required_359_i0 := by decide +kernel
theorem child_required_sub_359_i0 : ∀ j, childrenC_359_i0 j ⊆ insert (1, 6) required_359_i0 := by decide +kernel
theorem child_envelope_sub_359_i0 : ∀ j, childrenD_359_i0 j ⊆ envelope_359_i0 := by decide +kernel
theorem pivot_mem_359_i0 : (1, 6) ∈ envelope_359_i0 := by decide +kernel
theorem children_work_359_i0 : ∀ j, Template HasSnaky 3 (childrenC_359_i0 j) (childrenD_359_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (2, 2)).mono (by decide +kernel)
theorem row_works_359_i0 : Template HasSnaky 4 required_359_i0 envelope_359_i0 := by
  refine compose HasSnaky 3 childrenC_359_i0 childrenD_359_i0 children_work_359_i0 (1, 6)
    required_359_i0 envelope_359_i0 pivot_mem_359_i0 child_required_sub_359_i0 child_envelope_sub_359_i0 ?_
  intro b hb
  exact common_sub_359_i0 (mem_commonEnvelope childrenD_359_i0 b hb)
def required_359 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_359 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_359 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) required_10), (placed21 2 (1, 2) required_52), (placed21 6 (1, 6) required_52), required_359_i0]
def childrenD_359 : Fin 4 → Finset Cell := ![(placed21 4 (0, 6) envelope_10), (placed21 2 (1, 2) envelope_52), (placed21 6 (1, 6) envelope_52), envelope_359_i0]
theorem common_sub_359 : commonEnvelope childrenD_359 ⊆ insert (1, 4) required_359 := by decide +kernel
theorem child_required_sub_359 : ∀ j, childrenC_359 j ⊆ insert (1, 4) required_359 := by decide +kernel
theorem child_envelope_sub_359 : ∀ j, childrenD_359 j ⊆ envelope_359 := by decide +kernel
theorem pivot_mem_359 : (1, 4) ∈ envelope_359 := by decide +kernel
theorem children_work_359 : ∀ j, Template HasSnaky 4 (childrenC_359 j) (childrenD_359 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact row_works_359_i0.mono (by decide +kernel)
theorem row_works_359 : Template HasSnaky 5 required_359 envelope_359 := by
  refine compose HasSnaky 4 childrenC_359 childrenD_359 children_work_359 (1, 4)
    required_359 envelope_359 pivot_mem_359 child_required_sub_359 child_envelope_sub_359 ?_
  intro b hb
  exact common_sub_359 (mem_commonEnvelope childrenD_359 b hb)
def required_362_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_362_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_362_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_2), (placed21 6 (1, 6) required_53)]
def childrenD_362_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_2), (placed21 6 (1, 6) envelope_53)]
theorem common_sub_362_i0 : commonEnvelope childrenD_362_i0 ⊆ insert (1, 4) required_362_i0 := by decide +kernel
theorem child_required_sub_362_i0 : ∀ j, childrenC_362_i0 j ⊆ insert (1, 4) required_362_i0 := by decide +kernel
theorem child_envelope_sub_362_i0 : ∀ j, childrenD_362_i0 j ⊆ envelope_362_i0 := by decide +kernel
theorem pivot_mem_362_i0 : (1, 4) ∈ envelope_362_i0 := by decide +kernel
theorem children_work_362_i0 : ∀ j, Template HasSnaky 3 (childrenC_362_i0 j) (childrenD_362_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 6 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 6 (1, 6)).mono (by decide +kernel)
theorem row_works_362_i0 : Template HasSnaky 4 required_362_i0 envelope_362_i0 := by
  refine compose HasSnaky 3 childrenC_362_i0 childrenD_362_i0 children_work_362_i0 (1, 4)
    required_362_i0 envelope_362_i0 pivot_mem_362_i0 child_required_sub_362_i0 child_envelope_sub_362_i0 ?_
  intro b hb
  exact common_sub_362_i0 (mem_commonEnvelope childrenD_362_i0 b hb)
def required_362 : Finset Cell := ⟨(([(0, 2), (0, 3), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_362 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_362 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_2), required_362_i0]
def childrenD_362 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_2), envelope_362_i0]
theorem common_sub_362 : commonEnvelope childrenD_362 ⊆ insert (1, 3) required_362 := by decide +kernel
theorem child_required_sub_362 : ∀ j, childrenC_362 j ⊆ insert (1, 3) required_362 := by decide +kernel
theorem child_envelope_sub_362 : ∀ j, childrenD_362 j ⊆ envelope_362 := by decide +kernel
theorem pivot_mem_362 : (1, 3) ∈ envelope_362 := by decide +kernel
theorem children_work_362 : ∀ j, Template HasSnaky 4 (childrenC_362 j) (childrenD_362 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_362_i0.mono (by decide +kernel)
theorem row_works_362 : Template HasSnaky 5 required_362 envelope_362 := by
  refine compose HasSnaky 4 childrenC_362 childrenD_362 children_work_362 (1, 3)
    required_362 envelope_362 pivot_mem_362 child_required_sub_362 child_envelope_sub_362 ?_
  intro b hb
  exact common_sub_362 (mem_commonEnvelope childrenD_362 b hb)
def required_366 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_366 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_366 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) required_6), (placed21 2 (2, 0) required_365)]
def childrenD_366 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) envelope_6), (placed21 2 (2, 0) envelope_365)]
theorem common_sub_366 : commonEnvelope childrenD_366 ⊆ insert (1, 1) required_366 := by decide +kernel
theorem child_required_sub_366 : ∀ j, childrenC_366 j ⊆ insert (1, 1) required_366 := by decide +kernel
theorem child_envelope_sub_366 : ∀ j, childrenD_366 j ⊆ envelope_366 := by decide +kernel
theorem pivot_mem_366 : (1, 1) ∈ envelope_366 := by decide +kernel
theorem children_work_366 : ∀ j, Template HasSnaky 4 (childrenC_366 j) (childrenD_366 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_365 2 (2, 0)).mono (by decide +kernel)
theorem row_works_366 : Template HasSnaky 5 required_366 envelope_366 := by
  refine compose HasSnaky 4 childrenC_366 childrenD_366 children_work_366 (1, 1)
    required_366 envelope_366 pivot_mem_366 child_required_sub_366 child_envelope_sub_366 ?_
  intro b hb
  exact common_sub_366 (mem_commonEnvelope childrenD_366 b hb)
def required_370_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_370_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (3, 1), (4, 1), (4, 2), (5, 1), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_370_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_16), required_210]
def childrenD_370_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_16), envelope_210]
theorem common_sub_370_i0 : commonEnvelope childrenD_370_i0 ⊆ insert (1, 2) required_370_i0 := by decide +kernel
theorem child_required_sub_370_i0 : ∀ j, childrenC_370_i0 j ⊆ insert (1, 2) required_370_i0 := by decide +kernel
theorem child_envelope_sub_370_i0 : ∀ j, childrenD_370_i0 j ⊆ envelope_370_i0 := by decide +kernel
theorem pivot_mem_370_i0 : (1, 2) ∈ envelope_370_i0 := by decide +kernel
theorem children_work_370_i0 : ∀ j, Template HasSnaky 3 (childrenC_370_i0 j) (childrenD_370_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_210.mono (by decide +kernel)
theorem row_works_370_i0 : Template HasSnaky 4 required_370_i0 envelope_370_i0 := by
  refine compose HasSnaky 3 childrenC_370_i0 childrenD_370_i0 children_work_370_i0 (1, 2)
    required_370_i0 envelope_370_i0 pivot_mem_370_i0 child_required_sub_370_i0 child_envelope_sub_370_i0 ?_
  intro b hb
  exact common_sub_370_i0 (mem_commonEnvelope childrenD_370_i0 b hb)
def required_370 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_370 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_370 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) required_6), required_370_i0]
def childrenD_370 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) envelope_6), envelope_370_i0]
theorem common_sub_370 : commonEnvelope childrenD_370 ⊆ insert (4, 1) required_370 := by decide +kernel
theorem child_required_sub_370 : ∀ j, childrenC_370 j ⊆ insert (4, 1) required_370 := by decide +kernel
theorem child_envelope_sub_370 : ∀ j, childrenD_370 j ⊆ envelope_370 := by decide +kernel
theorem pivot_mem_370 : (4, 1) ∈ envelope_370 := by decide +kernel
theorem children_work_370 : ∀ j, Template HasSnaky 4 (childrenC_370 j) (childrenD_370 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact row_works_370_i0.mono (by decide +kernel)
theorem row_works_370 : Template HasSnaky 5 required_370 envelope_370 := by
  refine compose HasSnaky 4 childrenC_370 childrenD_370 children_work_370 (4, 1)
    required_370 envelope_370 pivot_mem_370 child_required_sub_370 child_envelope_sub_370 ?_
  intro b hb
  exact common_sub_370 (mem_commonEnvelope childrenD_370 b hb)
def required_377 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_377 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_377 : Fin 3 → Finset Cell := ![(placed21 2 (1, 0) required_7), required_9, (placed21 1 (0, 1) required_376)]
def childrenD_377 : Fin 3 → Finset Cell := ![(placed21 2 (1, 0) envelope_7), envelope_9, (placed21 1 (0, 1) envelope_376)]
theorem common_sub_377 : commonEnvelope childrenD_377 ⊆ insert (1, 4) required_377 := by decide +kernel
theorem child_required_sub_377 : ∀ j, childrenC_377 j ⊆ insert (1, 4) required_377 := by decide +kernel
theorem child_envelope_sub_377 : ∀ j, childrenD_377 j ⊆ envelope_377 := by decide +kernel
theorem pivot_mem_377 : (1, 4) ∈ envelope_377 := by decide +kernel
theorem children_work_377 : ∀ j, Template HasSnaky 4 (childrenC_377 j) (childrenD_377 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (1, 0)).mono (by decide +kernel)
  · exact row_works_9.mono (by decide +kernel)
  · exact (placed21_template row_works_376 1 (0, 1)).mono (by decide +kernel)
theorem row_works_377 : Template HasSnaky 5 required_377 envelope_377 := by
  refine compose HasSnaky 4 childrenC_377 childrenD_377 children_work_377 (1, 4)
    required_377 envelope_377 pivot_mem_377 child_required_sub_377 child_envelope_sub_377 ?_
  intro b hb
  exact common_sub_377 (mem_commonEnvelope childrenD_377 b hb)
def required_382 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 4), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_382 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_382 : Fin 2 → Finset Cell := ![(placed21 2 (1, 0) required_22), (placed21 5 (4, 1) required_381)]
def childrenD_382 : Fin 2 → Finset Cell := ![(placed21 2 (1, 0) envelope_22), (placed21 5 (4, 1) envelope_381)]
theorem common_sub_382 : commonEnvelope childrenD_382 ⊆ insert (1, 4) required_382 := by decide +kernel
theorem child_required_sub_382 : ∀ j, childrenC_382 j ⊆ insert (1, 4) required_382 := by decide +kernel
theorem child_envelope_sub_382 : ∀ j, childrenD_382 j ⊆ envelope_382 := by decide +kernel
theorem pivot_mem_382 : (1, 4) ∈ envelope_382 := by decide +kernel
theorem children_work_382 : ∀ j, Template HasSnaky 4 (childrenC_382 j) (childrenD_382 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 2 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_381 5 (4, 1)).mono (by decide +kernel)
theorem row_works_382 : Template HasSnaky 5 required_382 envelope_382 := by
  refine compose HasSnaky 4 childrenC_382 childrenD_382 children_work_382 (1, 4)
    required_382 envelope_382 pivot_mem_382 child_required_sub_382 child_envelope_sub_382 ?_
  intro b hb
  exact common_sub_382 (mem_commonEnvelope childrenD_382 b hb)
def required_383_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 5), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_383_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_383_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), (placed21 4 (2, 5) required_219)]
def childrenD_383_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), (placed21 4 (2, 5) envelope_219)]
theorem common_sub_383_i0 : commonEnvelope childrenD_383_i0 ⊆ insert (3, 3) required_383_i0 := by decide +kernel
theorem child_required_sub_383_i0 : ∀ j, childrenC_383_i0 j ⊆ insert (3, 3) required_383_i0 := by decide +kernel
theorem child_envelope_sub_383_i0 : ∀ j, childrenD_383_i0 j ⊆ envelope_383_i0 := by decide +kernel
theorem pivot_mem_383_i0 : (3, 3) ∈ envelope_383_i0 := by decide +kernel
theorem children_work_383_i0 : ∀ j, Template HasSnaky 3 (childrenC_383_i0 j) (childrenD_383_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_219 4 (2, 5)).mono (by decide +kernel)
theorem row_works_383_i0 : Template HasSnaky 4 required_383_i0 envelope_383_i0 := by
  refine compose HasSnaky 3 childrenC_383_i0 childrenD_383_i0 children_work_383_i0 (3, 3)
    required_383_i0 envelope_383_i0 pivot_mem_383_i0 child_required_sub_383_i0 child_envelope_sub_383_i0 ?_
  intro b hb
  exact common_sub_383_i0 (mem_commonEnvelope childrenD_383_i0 b hb)
def required_383 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 5), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_383 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_383 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), required_383_i0]
def childrenD_383 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), envelope_383_i0]
theorem common_sub_383 : commonEnvelope childrenD_383 ⊆ insert (3, 1) required_383 := by decide +kernel
theorem child_required_sub_383 : ∀ j, childrenC_383 j ⊆ insert (3, 1) required_383 := by decide +kernel
theorem child_envelope_sub_383 : ∀ j, childrenD_383 j ⊆ envelope_383 := by decide +kernel
theorem pivot_mem_383 : (3, 1) ∈ envelope_383 := by decide +kernel
theorem children_work_383 : ∀ j, Template HasSnaky 4 (childrenC_383 j) (childrenD_383 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact row_works_383_i0.mono (by decide +kernel)
theorem row_works_383 : Template HasSnaky 5 required_383 envelope_383 := by
  refine compose HasSnaky 4 childrenC_383 childrenD_383 children_work_383 (3, 1)
    required_383 envelope_383 pivot_mem_383 child_required_sub_383 child_envelope_sub_383 ?_
  intro b hb
  exact common_sub_383 (mem_commonEnvelope childrenD_383 b hb)
def required_386_i1 : Finset Cell := ⟨(([(2, 2), (2, 4), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_386_i1 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_386_i1 : Fin 2 → Finset Cell := ![(placed21 5 (3, 1) required_5), (placed21 2 (3, 0) required_11)]
def childrenD_386_i1 : Fin 2 → Finset Cell := ![(placed21 5 (3, 1) envelope_5), (placed21 2 (3, 0) envelope_11)]
theorem common_sub_386_i1 : commonEnvelope childrenD_386_i1 ⊆ insert (3, 4) required_386_i1 := by decide +kernel
theorem child_required_sub_386_i1 : ∀ j, childrenC_386_i1 j ⊆ insert (3, 4) required_386_i1 := by decide +kernel
theorem child_envelope_sub_386_i1 : ∀ j, childrenD_386_i1 j ⊆ envelope_386_i1 := by decide +kernel
theorem pivot_mem_386_i1 : (3, 4) ∈ envelope_386_i1 := by decide +kernel
theorem children_work_386_i1 : ∀ j, Template HasSnaky 2 (childrenC_386_i1 j) (childrenD_386_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 2 (3, 0)).mono (by decide +kernel)
theorem row_works_386_i1 : Template HasSnaky 3 required_386_i1 envelope_386_i1 := by
  refine compose HasSnaky 2 childrenC_386_i1 childrenD_386_i1 children_work_386_i1 (3, 4)
    required_386_i1 envelope_386_i1 pivot_mem_386_i1 child_required_sub_386_i1 child_envelope_sub_386_i1 ?_
  intro b hb
  exact common_sub_386_i1 (mem_commonEnvelope childrenD_386_i1 b hb)
def required_386_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_386_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_386_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), required_386_i1]
def childrenD_386_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), envelope_386_i1]
theorem common_sub_386_i0 : commonEnvelope childrenD_386_i0 ⊆ insert (3, 3) required_386_i0 := by decide +kernel
theorem child_required_sub_386_i0 : ∀ j, childrenC_386_i0 j ⊆ insert (3, 3) required_386_i0 := by decide +kernel
theorem child_envelope_sub_386_i0 : ∀ j, childrenD_386_i0 j ⊆ envelope_386_i0 := by decide +kernel
theorem pivot_mem_386_i0 : (3, 3) ∈ envelope_386_i0 := by decide +kernel
theorem children_work_386_i0 : ∀ j, Template HasSnaky 3 (childrenC_386_i0 j) (childrenD_386_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_386_i1.mono (by decide +kernel)
theorem row_works_386_i0 : Template HasSnaky 4 required_386_i0 envelope_386_i0 := by
  refine compose HasSnaky 3 childrenC_386_i0 childrenD_386_i0 children_work_386_i0 (3, 3)
    required_386_i0 envelope_386_i0 pivot_mem_386_i0 child_required_sub_386_i0 child_envelope_sub_386_i0 ?_
  intro b hb
  exact common_sub_386_i0 (mem_commonEnvelope childrenD_386_i0 b hb)
def required_386 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 4), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_386 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_386 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), required_386_i0]
def childrenD_386 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), envelope_386_i0]
theorem common_sub_386 : commonEnvelope childrenD_386 ⊆ insert (3, 1) required_386 := by decide +kernel
theorem child_required_sub_386 : ∀ j, childrenC_386 j ⊆ insert (3, 1) required_386 := by decide +kernel
theorem child_envelope_sub_386 : ∀ j, childrenD_386 j ⊆ envelope_386 := by decide +kernel
theorem pivot_mem_386 : (3, 1) ∈ envelope_386 := by decide +kernel
theorem children_work_386 : ∀ j, Template HasSnaky 4 (childrenC_386 j) (childrenD_386 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact row_works_386_i0.mono (by decide +kernel)
theorem row_works_386 : Template HasSnaky 5 required_386 envelope_386 := by
  refine compose HasSnaky 4 childrenC_386 childrenD_386 children_work_386 (3, 1)
    required_386 envelope_386 pivot_mem_386 child_required_sub_386 child_envelope_sub_386 ?_
  intro b hb
  exact common_sub_386 (mem_commonEnvelope childrenD_386 b hb)
def required_389_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_389_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_389_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_5), (placed21 0 (0, 1) required_23)]
def childrenD_389_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_5), (placed21 0 (0, 1) envelope_23)]
theorem common_sub_389_i0 : commonEnvelope childrenD_389_i0 ⊆ insert (1, 3) required_389_i0 := by decide +kernel
theorem child_required_sub_389_i0 : ∀ j, childrenC_389_i0 j ⊆ insert (1, 3) required_389_i0 := by decide +kernel
theorem child_envelope_sub_389_i0 : ∀ j, childrenD_389_i0 j ⊆ envelope_389_i0 := by decide +kernel
theorem pivot_mem_389_i0 : (1, 3) ∈ envelope_389_i0 := by decide +kernel
theorem children_work_389_i0 : ∀ j, Template HasSnaky 2 (childrenC_389_i0 j) (childrenD_389_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_23 0 (0, 1)).mono (by decide +kernel)
theorem row_works_389_i0 : Template HasSnaky 3 required_389_i0 envelope_389_i0 := by
  refine compose HasSnaky 2 childrenC_389_i0 childrenD_389_i0 children_work_389_i0 (1, 3)
    required_389_i0 envelope_389_i0 pivot_mem_389_i0 child_required_sub_389_i0 child_envelope_sub_389_i0 ?_
  intro b hb
  exact common_sub_389_i0 (mem_commonEnvelope childrenD_389_i0 b hb)
def required_389 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_389 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_389 : Fin 4 → Finset Cell := ![required_6, (placed21 0 (0, 1) required_21), (placed21 0 (0, 1) required_27), required_389_i0]
def childrenD_389 : Fin 4 → Finset Cell := ![envelope_6, (placed21 0 (0, 1) envelope_21), (placed21 0 (0, 1) envelope_27), envelope_389_i0]
theorem common_sub_389 : commonEnvelope childrenD_389 ⊆ insert (0, 4) required_389 := by decide +kernel
theorem child_required_sub_389 : ∀ j, childrenC_389 j ⊆ insert (0, 4) required_389 := by decide +kernel
theorem child_envelope_sub_389 : ∀ j, childrenD_389 j ⊆ envelope_389 := by decide +kernel
theorem pivot_mem_389 : (0, 4) ∈ envelope_389 := by decide +kernel
theorem children_work_389 : ∀ j, Template HasSnaky 4 (childrenC_389 j) (childrenD_389 j) := by
  intro j
  fin_cases j
  · exact row_works_6.mono (by decide +kernel)
  · exact (placed21_template row_works_21 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_27 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_389_i0.mono (by decide +kernel)
theorem row_works_389 : Template HasSnaky 5 required_389 envelope_389 := by
  refine compose HasSnaky 4 childrenC_389 childrenD_389 children_work_389 (0, 4)
    required_389 envelope_389 pivot_mem_389 child_required_sub_389 child_envelope_sub_389 ?_
  intro b hb
  exact common_sub_389 (mem_commonEnvelope childrenD_389 b hb)
def height_356_i0 : ℕ := 4
def childrenH_356_i0 : Fin 2 → ℕ := ![height_21, height_121]
theorem height_exact_356_i0 : height_356_i0 = 1 + Finset.univ.sup childrenH_356_i0 := by decide +kernel
theorem required_origin_356_i0 : ∀ x ∈ required_356_i0,
    (∃ j, x ∈ childrenC_356_i0 j) ∨ ∀ j, x ∈ childrenD_356_i0 j := by decide +kernel
theorem required_exact_356_i0 : required_356_i0 =
    ((Finset.univ.biUnion childrenC_356_i0) ∪ commonEnvelope childrenD_356_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_356_i0 childrenD_356_i0 (2, 3) required_356_i0
    (by decide +kernel) child_required_sub_356_i0 common_sub_356_i0 required_origin_356_i0
theorem envelope_origin_356_i0 : ∀ x ∈ envelope_356_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_356_i0 j := by decide +kernel
theorem envelope_exact_356_i0 : envelope_356_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_356_i0) := by
  exact envelope_eq_combination childrenD_356_i0 (2, 3) envelope_356_i0
    pivot_mem_356_i0 child_envelope_sub_356_i0 envelope_origin_356_i0
def checked_356_i0 : CheckedCard where
  required := required_356_i0
  envelope := envelope_356_i0
  height := height_356_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_356_i0
def height_356 : ℕ := 5
def childrenH_356 : Fin 3 → ℕ := ![height_7, height_8, height_356_i0]
theorem height_exact_356 : height_356 = 1 + Finset.univ.sup childrenH_356 := by decide +kernel
theorem required_origin_356 : ∀ x ∈ required_356,
    (∃ j, x ∈ childrenC_356 j) ∨ ∀ j, x ∈ childrenD_356 j := by decide +kernel
theorem required_exact_356 : required_356 =
    ((Finset.univ.biUnion childrenC_356) ∪ commonEnvelope childrenD_356).erase (3, 5) := by
  exact required_eq_combination childrenC_356 childrenD_356 (3, 5) required_356
    (by decide +kernel) child_required_sub_356 common_sub_356 required_origin_356
theorem envelope_origin_356 : ∀ x ∈ envelope_356,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_356 j := by decide +kernel
theorem envelope_exact_356 : envelope_356 =
    insert (3, 5) (Finset.univ.biUnion childrenD_356) := by
  exact envelope_eq_combination childrenD_356 (3, 5) envelope_356
    pivot_mem_356 child_envelope_sub_356 envelope_origin_356
def checked_356 : CheckedCard where
  required := required_356
  envelope := envelope_356
  height := height_356
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_356
def height_357_i2 : ℕ := 2
def childrenH_357_i2 : Fin 2 → ℕ := ![height_3, height_5]
theorem height_exact_357_i2 : height_357_i2 = 1 + Finset.univ.sup childrenH_357_i2 := by decide +kernel
theorem required_origin_357_i2 : ∀ x ∈ required_357_i2,
    (∃ j, x ∈ childrenC_357_i2 j) ∨ ∀ j, x ∈ childrenD_357_i2 j := by decide +kernel
theorem required_exact_357_i2 : required_357_i2 =
    ((Finset.univ.biUnion childrenC_357_i2) ∪ commonEnvelope childrenD_357_i2).erase (1, 4) := by
  exact required_eq_combination childrenC_357_i2 childrenD_357_i2 (1, 4) required_357_i2
    (by decide +kernel) child_required_sub_357_i2 common_sub_357_i2 required_origin_357_i2
theorem envelope_origin_357_i2 : ∀ x ∈ envelope_357_i2,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_357_i2 j := by decide +kernel
theorem envelope_exact_357_i2 : envelope_357_i2 =
    insert (1, 4) (Finset.univ.biUnion childrenD_357_i2) := by
  exact envelope_eq_combination childrenD_357_i2 (1, 4) envelope_357_i2
    pivot_mem_357_i2 child_envelope_sub_357_i2 envelope_origin_357_i2
def checked_357_i2 : CheckedCard where
  required := required_357_i2
  envelope := envelope_357_i2
  height := height_357_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_357_i2
def height_357_i1 : ℕ := 3
def childrenH_357_i1 : Fin 2 → ℕ := ![height_4, height_357_i2]
theorem height_exact_357_i1 : height_357_i1 = 1 + Finset.univ.sup childrenH_357_i1 := by decide +kernel
theorem required_origin_357_i1 : ∀ x ∈ required_357_i1,
    (∃ j, x ∈ childrenC_357_i1 j) ∨ ∀ j, x ∈ childrenD_357_i1 j := by decide +kernel
theorem required_exact_357_i1 : required_357_i1 =
    ((Finset.univ.biUnion childrenC_357_i1) ∪ commonEnvelope childrenD_357_i1).erase (1, 3) := by
  exact required_eq_combination childrenC_357_i1 childrenD_357_i1 (1, 3) required_357_i1
    (by decide +kernel) child_required_sub_357_i1 common_sub_357_i1 required_origin_357_i1
theorem envelope_origin_357_i1 : ∀ x ∈ envelope_357_i1,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_357_i1 j := by decide +kernel
theorem envelope_exact_357_i1 : envelope_357_i1 =
    insert (1, 3) (Finset.univ.biUnion childrenD_357_i1) := by
  exact envelope_eq_combination childrenD_357_i1 (1, 3) envelope_357_i1
    pivot_mem_357_i1 child_envelope_sub_357_i1 envelope_origin_357_i1
def checked_357_i1 : CheckedCard where
  required := required_357_i1
  envelope := envelope_357_i1
  height := height_357_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_357_i1
def height_357_i0 : ℕ := 4
def childrenH_357_i0 : Fin 2 → ℕ := ![height_5, height_357_i1]
theorem height_exact_357_i0 : height_357_i0 = 1 + Finset.univ.sup childrenH_357_i0 := by decide +kernel
theorem required_origin_357_i0 : ∀ x ∈ required_357_i0,
    (∃ j, x ∈ childrenC_357_i0 j) ∨ ∀ j, x ∈ childrenD_357_i0 j := by decide +kernel
theorem required_exact_357_i0 : required_357_i0 =
    ((Finset.univ.biUnion childrenC_357_i0) ∪ commonEnvelope childrenD_357_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_357_i0 childrenD_357_i0 (4, 3) required_357_i0
    (by decide +kernel) child_required_sub_357_i0 common_sub_357_i0 required_origin_357_i0
theorem envelope_origin_357_i0 : ∀ x ∈ envelope_357_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_357_i0 j := by decide +kernel
theorem envelope_exact_357_i0 : envelope_357_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_357_i0) := by
  exact envelope_eq_combination childrenD_357_i0 (4, 3) envelope_357_i0
    pivot_mem_357_i0 child_envelope_sub_357_i0 envelope_origin_357_i0
def checked_357_i0 : CheckedCard where
  required := required_357_i0
  envelope := envelope_357_i0
  height := height_357_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_357_i0
def height_357 : ℕ := 5
def childrenH_357 : Fin 2 → ℕ := ![height_5, height_357_i0]
theorem height_exact_357 : height_357 = 1 + Finset.univ.sup childrenH_357 := by decide +kernel
theorem required_origin_357 : ∀ x ∈ required_357,
    (∃ j, x ∈ childrenC_357 j) ∨ ∀ j, x ∈ childrenD_357 j := by decide +kernel
theorem required_exact_357 : required_357 =
    ((Finset.univ.biUnion childrenC_357) ∪ commonEnvelope childrenD_357).erase (2, 3) := by
  exact required_eq_combination childrenC_357 childrenD_357 (2, 3) required_357
    (by decide +kernel) child_required_sub_357 common_sub_357 required_origin_357
theorem envelope_origin_357 : ∀ x ∈ envelope_357,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_357 j := by decide +kernel
theorem envelope_exact_357 : envelope_357 =
    insert (2, 3) (Finset.univ.biUnion childrenD_357) := by
  exact envelope_eq_combination childrenD_357 (2, 3) envelope_357
    pivot_mem_357 child_envelope_sub_357 envelope_origin_357
def checked_357 : CheckedCard where
  required := required_357
  envelope := envelope_357
  height := height_357
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_357
def height_359_i0 : ℕ := 4
def childrenH_359_i0 : Fin 2 → ℕ := ![height_5, height_9]
theorem height_exact_359_i0 : height_359_i0 = 1 + Finset.univ.sup childrenH_359_i0 := by decide +kernel
theorem required_origin_359_i0 : ∀ x ∈ required_359_i0,
    (∃ j, x ∈ childrenC_359_i0 j) ∨ ∀ j, x ∈ childrenD_359_i0 j := by decide +kernel
theorem required_exact_359_i0 : required_359_i0 =
    ((Finset.univ.biUnion childrenC_359_i0) ∪ commonEnvelope childrenD_359_i0).erase (1, 6) := by
  exact required_eq_combination childrenC_359_i0 childrenD_359_i0 (1, 6) required_359_i0
    (by decide +kernel) child_required_sub_359_i0 common_sub_359_i0 required_origin_359_i0
theorem envelope_origin_359_i0 : ∀ x ∈ envelope_359_i0,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_359_i0 j := by decide +kernel
theorem envelope_exact_359_i0 : envelope_359_i0 =
    insert (1, 6) (Finset.univ.biUnion childrenD_359_i0) := by
  exact envelope_eq_combination childrenD_359_i0 (1, 6) envelope_359_i0
    pivot_mem_359_i0 child_envelope_sub_359_i0 envelope_origin_359_i0
def checked_359_i0 : CheckedCard where
  required := required_359_i0
  envelope := envelope_359_i0
  height := height_359_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_359_i0
def height_359 : ℕ := 5
def childrenH_359 : Fin 4 → ℕ := ![height_10, height_52, height_52, height_359_i0]
theorem height_exact_359 : height_359 = 1 + Finset.univ.sup childrenH_359 := by decide +kernel
theorem required_origin_359 : ∀ x ∈ required_359,
    (∃ j, x ∈ childrenC_359 j) ∨ ∀ j, x ∈ childrenD_359 j := by decide +kernel
theorem required_exact_359 : required_359 =
    ((Finset.univ.biUnion childrenC_359) ∪ commonEnvelope childrenD_359).erase (1, 4) := by
  exact required_eq_combination childrenC_359 childrenD_359 (1, 4) required_359
    (by decide +kernel) child_required_sub_359 common_sub_359 required_origin_359
theorem envelope_origin_359 : ∀ x ∈ envelope_359,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_359 j := by decide +kernel
theorem envelope_exact_359 : envelope_359 =
    insert (1, 4) (Finset.univ.biUnion childrenD_359) := by
  exact envelope_eq_combination childrenD_359 (1, 4) envelope_359
    pivot_mem_359 child_envelope_sub_359 envelope_origin_359
def checked_359 : CheckedCard where
  required := required_359
  envelope := envelope_359
  height := height_359
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_359
def height_362_i0 : ℕ := 4
def childrenH_362_i0 : Fin 2 → ℕ := ![height_2, height_53]
theorem height_exact_362_i0 : height_362_i0 = 1 + Finset.univ.sup childrenH_362_i0 := by decide +kernel
theorem required_origin_362_i0 : ∀ x ∈ required_362_i0,
    (∃ j, x ∈ childrenC_362_i0 j) ∨ ∀ j, x ∈ childrenD_362_i0 j := by decide +kernel
theorem required_exact_362_i0 : required_362_i0 =
    ((Finset.univ.biUnion childrenC_362_i0) ∪ commonEnvelope childrenD_362_i0).erase (1, 4) := by
  exact required_eq_combination childrenC_362_i0 childrenD_362_i0 (1, 4) required_362_i0
    (by decide +kernel) child_required_sub_362_i0 common_sub_362_i0 required_origin_362_i0
theorem envelope_origin_362_i0 : ∀ x ∈ envelope_362_i0,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_362_i0 j := by decide +kernel
theorem envelope_exact_362_i0 : envelope_362_i0 =
    insert (1, 4) (Finset.univ.biUnion childrenD_362_i0) := by
  exact envelope_eq_combination childrenD_362_i0 (1, 4) envelope_362_i0
    pivot_mem_362_i0 child_envelope_sub_362_i0 envelope_origin_362_i0
def checked_362_i0 : CheckedCard where
  required := required_362_i0
  envelope := envelope_362_i0
  height := height_362_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_362_i0
def height_362 : ℕ := 5
def childrenH_362 : Fin 2 → ℕ := ![height_2, height_362_i0]
theorem height_exact_362 : height_362 = 1 + Finset.univ.sup childrenH_362 := by decide +kernel
theorem required_origin_362 : ∀ x ∈ required_362,
    (∃ j, x ∈ childrenC_362 j) ∨ ∀ j, x ∈ childrenD_362 j := by decide +kernel
theorem required_exact_362 : required_362 =
    ((Finset.univ.biUnion childrenC_362) ∪ commonEnvelope childrenD_362).erase (1, 3) := by
  exact required_eq_combination childrenC_362 childrenD_362 (1, 3) required_362
    (by decide +kernel) child_required_sub_362 common_sub_362 required_origin_362
theorem envelope_origin_362 : ∀ x ∈ envelope_362,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_362 j := by decide +kernel
theorem envelope_exact_362 : envelope_362 =
    insert (1, 3) (Finset.univ.biUnion childrenD_362) := by
  exact envelope_eq_combination childrenD_362 (1, 3) envelope_362
    pivot_mem_362 child_envelope_sub_362 envelope_origin_362
def checked_362 : CheckedCard where
  required := required_362
  envelope := envelope_362
  height := height_362
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_362
def height_366 : ℕ := 5
def childrenH_366 : Fin 2 → ℕ := ![height_6, height_365]
theorem height_exact_366 : height_366 = 1 + Finset.univ.sup childrenH_366 := by decide +kernel
theorem required_origin_366 : ∀ x ∈ required_366,
    (∃ j, x ∈ childrenC_366 j) ∨ ∀ j, x ∈ childrenD_366 j := by decide +kernel
theorem required_exact_366 : required_366 =
    ((Finset.univ.biUnion childrenC_366) ∪ commonEnvelope childrenD_366).erase (1, 1) := by
  exact required_eq_combination childrenC_366 childrenD_366 (1, 1) required_366
    (by decide +kernel) child_required_sub_366 common_sub_366 required_origin_366
theorem envelope_origin_366 : ∀ x ∈ envelope_366,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_366 j := by decide +kernel
theorem envelope_exact_366 : envelope_366 =
    insert (1, 1) (Finset.univ.biUnion childrenD_366) := by
  exact envelope_eq_combination childrenD_366 (1, 1) envelope_366
    pivot_mem_366 child_envelope_sub_366 envelope_origin_366
def checked_366 : CheckedCard where
  required := required_366
  envelope := envelope_366
  height := height_366
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_366
def height_370_i0 : ℕ := 4
def childrenH_370_i0 : Fin 2 → ℕ := ![height_16, height_210]
theorem height_exact_370_i0 : height_370_i0 = 1 + Finset.univ.sup childrenH_370_i0 := by decide +kernel
theorem required_origin_370_i0 : ∀ x ∈ required_370_i0,
    (∃ j, x ∈ childrenC_370_i0 j) ∨ ∀ j, x ∈ childrenD_370_i0 j := by decide +kernel
theorem required_exact_370_i0 : required_370_i0 =
    ((Finset.univ.biUnion childrenC_370_i0) ∪ commonEnvelope childrenD_370_i0).erase (1, 2) := by
  exact required_eq_combination childrenC_370_i0 childrenD_370_i0 (1, 2) required_370_i0
    (by decide +kernel) child_required_sub_370_i0 common_sub_370_i0 required_origin_370_i0
theorem envelope_origin_370_i0 : ∀ x ∈ envelope_370_i0,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_370_i0 j := by decide +kernel
theorem envelope_exact_370_i0 : envelope_370_i0 =
    insert (1, 2) (Finset.univ.biUnion childrenD_370_i0) := by
  exact envelope_eq_combination childrenD_370_i0 (1, 2) envelope_370_i0
    pivot_mem_370_i0 child_envelope_sub_370_i0 envelope_origin_370_i0
def checked_370_i0 : CheckedCard where
  required := required_370_i0
  envelope := envelope_370_i0
  height := height_370_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_370_i0
def height_370 : ℕ := 5
def childrenH_370 : Fin 2 → ℕ := ![height_6, height_370_i0]
theorem height_exact_370 : height_370 = 1 + Finset.univ.sup childrenH_370 := by decide +kernel
theorem required_origin_370 : ∀ x ∈ required_370,
    (∃ j, x ∈ childrenC_370 j) ∨ ∀ j, x ∈ childrenD_370 j := by decide +kernel
theorem required_exact_370 : required_370 =
    ((Finset.univ.biUnion childrenC_370) ∪ commonEnvelope childrenD_370).erase (4, 1) := by
  exact required_eq_combination childrenC_370 childrenD_370 (4, 1) required_370
    (by decide +kernel) child_required_sub_370 common_sub_370 required_origin_370
theorem envelope_origin_370 : ∀ x ∈ envelope_370,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_370 j := by decide +kernel
theorem envelope_exact_370 : envelope_370 =
    insert (4, 1) (Finset.univ.biUnion childrenD_370) := by
  exact envelope_eq_combination childrenD_370 (4, 1) envelope_370
    pivot_mem_370 child_envelope_sub_370 envelope_origin_370
def checked_370 : CheckedCard where
  required := required_370
  envelope := envelope_370
  height := height_370
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_370
def height_377 : ℕ := 5
def childrenH_377 : Fin 3 → ℕ := ![height_7, height_9, height_376]
theorem height_exact_377 : height_377 = 1 + Finset.univ.sup childrenH_377 := by decide +kernel
theorem required_origin_377 : ∀ x ∈ required_377,
    (∃ j, x ∈ childrenC_377 j) ∨ ∀ j, x ∈ childrenD_377 j := by decide +kernel
theorem required_exact_377 : required_377 =
    ((Finset.univ.biUnion childrenC_377) ∪ commonEnvelope childrenD_377).erase (1, 4) := by
  exact required_eq_combination childrenC_377 childrenD_377 (1, 4) required_377
    (by decide +kernel) child_required_sub_377 common_sub_377 required_origin_377
theorem envelope_origin_377 : ∀ x ∈ envelope_377,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_377 j := by decide +kernel
theorem envelope_exact_377 : envelope_377 =
    insert (1, 4) (Finset.univ.biUnion childrenD_377) := by
  exact envelope_eq_combination childrenD_377 (1, 4) envelope_377
    pivot_mem_377 child_envelope_sub_377 envelope_origin_377
def checked_377 : CheckedCard where
  required := required_377
  envelope := envelope_377
  height := height_377
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_377
def height_382 : ℕ := 5
def childrenH_382 : Fin 2 → ℕ := ![height_22, height_381]
theorem height_exact_382 : height_382 = 1 + Finset.univ.sup childrenH_382 := by decide +kernel
theorem required_origin_382 : ∀ x ∈ required_382,
    (∃ j, x ∈ childrenC_382 j) ∨ ∀ j, x ∈ childrenD_382 j := by decide +kernel
theorem required_exact_382 : required_382 =
    ((Finset.univ.biUnion childrenC_382) ∪ commonEnvelope childrenD_382).erase (1, 4) := by
  exact required_eq_combination childrenC_382 childrenD_382 (1, 4) required_382
    (by decide +kernel) child_required_sub_382 common_sub_382 required_origin_382
theorem envelope_origin_382 : ∀ x ∈ envelope_382,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_382 j := by decide +kernel
theorem envelope_exact_382 : envelope_382 =
    insert (1, 4) (Finset.univ.biUnion childrenD_382) := by
  exact envelope_eq_combination childrenD_382 (1, 4) envelope_382
    pivot_mem_382 child_envelope_sub_382 envelope_origin_382
def checked_382 : CheckedCard where
  required := required_382
  envelope := envelope_382
  height := height_382
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_382
def height_383_i0 : ℕ := 4
def childrenH_383_i0 : Fin 2 → ℕ := ![height_5, height_219]
theorem height_exact_383_i0 : height_383_i0 = 1 + Finset.univ.sup childrenH_383_i0 := by decide +kernel
theorem required_origin_383_i0 : ∀ x ∈ required_383_i0,
    (∃ j, x ∈ childrenC_383_i0 j) ∨ ∀ j, x ∈ childrenD_383_i0 j := by decide +kernel
theorem required_exact_383_i0 : required_383_i0 =
    ((Finset.univ.biUnion childrenC_383_i0) ∪ commonEnvelope childrenD_383_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_383_i0 childrenD_383_i0 (3, 3) required_383_i0
    (by decide +kernel) child_required_sub_383_i0 common_sub_383_i0 required_origin_383_i0
theorem envelope_origin_383_i0 : ∀ x ∈ envelope_383_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_383_i0 j := by decide +kernel
theorem envelope_exact_383_i0 : envelope_383_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_383_i0) := by
  exact envelope_eq_combination childrenD_383_i0 (3, 3) envelope_383_i0
    pivot_mem_383_i0 child_envelope_sub_383_i0 envelope_origin_383_i0
def checked_383_i0 : CheckedCard where
  required := required_383_i0
  envelope := envelope_383_i0
  height := height_383_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_383_i0
def height_383 : ℕ := 5
def childrenH_383 : Fin 2 → ℕ := ![height_5, height_383_i0]
theorem height_exact_383 : height_383 = 1 + Finset.univ.sup childrenH_383 := by decide +kernel
theorem required_origin_383 : ∀ x ∈ required_383,
    (∃ j, x ∈ childrenC_383 j) ∨ ∀ j, x ∈ childrenD_383 j := by decide +kernel
theorem required_exact_383 : required_383 =
    ((Finset.univ.biUnion childrenC_383) ∪ commonEnvelope childrenD_383).erase (3, 1) := by
  exact required_eq_combination childrenC_383 childrenD_383 (3, 1) required_383
    (by decide +kernel) child_required_sub_383 common_sub_383 required_origin_383
theorem envelope_origin_383 : ∀ x ∈ envelope_383,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_383 j := by decide +kernel
theorem envelope_exact_383 : envelope_383 =
    insert (3, 1) (Finset.univ.biUnion childrenD_383) := by
  exact envelope_eq_combination childrenD_383 (3, 1) envelope_383
    pivot_mem_383 child_envelope_sub_383 envelope_origin_383
def checked_383 : CheckedCard where
  required := required_383
  envelope := envelope_383
  height := height_383
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_383
def height_386_i1 : ℕ := 3
def childrenH_386_i1 : Fin 2 → ℕ := ![height_5, height_11]
theorem height_exact_386_i1 : height_386_i1 = 1 + Finset.univ.sup childrenH_386_i1 := by decide +kernel
theorem required_origin_386_i1 : ∀ x ∈ required_386_i1,
    (∃ j, x ∈ childrenC_386_i1 j) ∨ ∀ j, x ∈ childrenD_386_i1 j := by decide +kernel
theorem required_exact_386_i1 : required_386_i1 =
    ((Finset.univ.biUnion childrenC_386_i1) ∪ commonEnvelope childrenD_386_i1).erase (3, 4) := by
  exact required_eq_combination childrenC_386_i1 childrenD_386_i1 (3, 4) required_386_i1
    (by decide +kernel) child_required_sub_386_i1 common_sub_386_i1 required_origin_386_i1
theorem envelope_origin_386_i1 : ∀ x ∈ envelope_386_i1,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_386_i1 j := by decide +kernel
theorem envelope_exact_386_i1 : envelope_386_i1 =
    insert (3, 4) (Finset.univ.biUnion childrenD_386_i1) := by
  exact envelope_eq_combination childrenD_386_i1 (3, 4) envelope_386_i1
    pivot_mem_386_i1 child_envelope_sub_386_i1 envelope_origin_386_i1
def checked_386_i1 : CheckedCard where
  required := required_386_i1
  envelope := envelope_386_i1
  height := height_386_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_386_i1
def height_386_i0 : ℕ := 4
def childrenH_386_i0 : Fin 2 → ℕ := ![height_5, height_386_i1]
theorem height_exact_386_i0 : height_386_i0 = 1 + Finset.univ.sup childrenH_386_i0 := by decide +kernel
theorem required_origin_386_i0 : ∀ x ∈ required_386_i0,
    (∃ j, x ∈ childrenC_386_i0 j) ∨ ∀ j, x ∈ childrenD_386_i0 j := by decide +kernel
theorem required_exact_386_i0 : required_386_i0 =
    ((Finset.univ.biUnion childrenC_386_i0) ∪ commonEnvelope childrenD_386_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_386_i0 childrenD_386_i0 (3, 3) required_386_i0
    (by decide +kernel) child_required_sub_386_i0 common_sub_386_i0 required_origin_386_i0
theorem envelope_origin_386_i0 : ∀ x ∈ envelope_386_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_386_i0 j := by decide +kernel
theorem envelope_exact_386_i0 : envelope_386_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_386_i0) := by
  exact envelope_eq_combination childrenD_386_i0 (3, 3) envelope_386_i0
    pivot_mem_386_i0 child_envelope_sub_386_i0 envelope_origin_386_i0
def checked_386_i0 : CheckedCard where
  required := required_386_i0
  envelope := envelope_386_i0
  height := height_386_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_386_i0
def height_386 : ℕ := 5
def childrenH_386 : Fin 2 → ℕ := ![height_5, height_386_i0]
theorem height_exact_386 : height_386 = 1 + Finset.univ.sup childrenH_386 := by decide +kernel
theorem required_origin_386 : ∀ x ∈ required_386,
    (∃ j, x ∈ childrenC_386 j) ∨ ∀ j, x ∈ childrenD_386 j := by decide +kernel
theorem required_exact_386 : required_386 =
    ((Finset.univ.biUnion childrenC_386) ∪ commonEnvelope childrenD_386).erase (3, 1) := by
  exact required_eq_combination childrenC_386 childrenD_386 (3, 1) required_386
    (by decide +kernel) child_required_sub_386 common_sub_386 required_origin_386
theorem envelope_origin_386 : ∀ x ∈ envelope_386,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_386 j := by decide +kernel
theorem envelope_exact_386 : envelope_386 =
    insert (3, 1) (Finset.univ.biUnion childrenD_386) := by
  exact envelope_eq_combination childrenD_386 (3, 1) envelope_386
    pivot_mem_386 child_envelope_sub_386 envelope_origin_386
def checked_386 : CheckedCard where
  required := required_386
  envelope := envelope_386
  height := height_386
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_386
def height_389_i0 : ℕ := 3
def childrenH_389_i0 : Fin 2 → ℕ := ![height_5, height_23]
theorem height_exact_389_i0 : height_389_i0 = 1 + Finset.univ.sup childrenH_389_i0 := by decide +kernel
theorem required_origin_389_i0 : ∀ x ∈ required_389_i0,
    (∃ j, x ∈ childrenC_389_i0 j) ∨ ∀ j, x ∈ childrenD_389_i0 j := by decide +kernel
theorem required_exact_389_i0 : required_389_i0 =
    ((Finset.univ.biUnion childrenC_389_i0) ∪ commonEnvelope childrenD_389_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_389_i0 childrenD_389_i0 (1, 3) required_389_i0
    (by decide +kernel) child_required_sub_389_i0 common_sub_389_i0 required_origin_389_i0
theorem envelope_origin_389_i0 : ∀ x ∈ envelope_389_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_389_i0 j := by decide +kernel
theorem envelope_exact_389_i0 : envelope_389_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_389_i0) := by
  exact envelope_eq_combination childrenD_389_i0 (1, 3) envelope_389_i0
    pivot_mem_389_i0 child_envelope_sub_389_i0 envelope_origin_389_i0
def checked_389_i0 : CheckedCard where
  required := required_389_i0
  envelope := envelope_389_i0
  height := height_389_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_389_i0
def height_389 : ℕ := 5
def childrenH_389 : Fin 4 → ℕ := ![height_6, height_21, height_27, height_389_i0]
theorem height_exact_389 : height_389 = 1 + Finset.univ.sup childrenH_389 := by decide +kernel
theorem required_origin_389 : ∀ x ∈ required_389,
    (∃ j, x ∈ childrenC_389 j) ∨ ∀ j, x ∈ childrenD_389 j := by decide +kernel
theorem required_exact_389 : required_389 =
    ((Finset.univ.biUnion childrenC_389) ∪ commonEnvelope childrenD_389).erase (0, 4) := by
  exact required_eq_combination childrenC_389 childrenD_389 (0, 4) required_389
    (by decide +kernel) child_required_sub_389 common_sub_389 required_origin_389
theorem envelope_origin_389 : ∀ x ∈ envelope_389,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_389 j := by decide +kernel
theorem envelope_exact_389 : envelope_389 =
    insert (0, 4) (Finset.univ.biUnion childrenD_389) := by
  exact envelope_eq_combination childrenD_389 (0, 4) envelope_389
    pivot_mem_389 child_envelope_sub_389 envelope_origin_389
def checked_389 : CheckedCard where
  required := required_389
  envelope := envelope_389
  height := height_389
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_389
end SnakyPrototype.Certificate21

end OAI
