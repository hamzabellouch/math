import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_391_i1 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_391_i1 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_391_i1 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), (placed21 4 (2, 4) required_36)]
def childrenD_391_i1 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), (placed21 4 (2, 4) envelope_36)]
theorem common_sub_391_i1 : commonEnvelope childrenD_391_i1 ⊆ insert (3, 1) required_391_i1 := by decide +kernel
theorem child_required_sub_391_i1 : ∀ j, childrenC_391_i1 j ⊆ insert (3, 1) required_391_i1 := by decide +kernel
theorem child_envelope_sub_391_i1 : ∀ j, childrenD_391_i1 j ⊆ envelope_391_i1 := by decide +kernel
theorem pivot_mem_391_i1 : (3, 1) ∈ envelope_391_i1 := by decide +kernel
theorem children_work_391_i1 : ∀ j, Template HasSnaky 2 (childrenC_391_i1 j) (childrenD_391_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_36 4 (2, 4)).mono (by decide +kernel)
theorem row_works_391_i1 : Template HasSnaky 3 required_391_i1 envelope_391_i1 := by
  refine compose HasSnaky 2 childrenC_391_i1 childrenD_391_i1 children_work_391_i1 (3, 1)
    required_391_i1 envelope_391_i1 pivot_mem_391_i1 child_required_sub_391_i1 child_envelope_sub_391_i1 ?_
  intro b hb
  exact common_sub_391_i1 (mem_commonEnvelope childrenD_391_i1 b hb)
def required_391_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_391_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_391_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), required_391_i1]
def childrenD_391_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), envelope_391_i1]
theorem common_sub_391_i0 : commonEnvelope childrenD_391_i0 ⊆ insert (2, 1) required_391_i0 := by decide +kernel
theorem child_required_sub_391_i0 : ∀ j, childrenC_391_i0 j ⊆ insert (2, 1) required_391_i0 := by decide +kernel
theorem child_envelope_sub_391_i0 : ∀ j, childrenD_391_i0 j ⊆ envelope_391_i0 := by decide +kernel
theorem pivot_mem_391_i0 : (2, 1) ∈ envelope_391_i0 := by decide +kernel
theorem children_work_391_i0 : ∀ j, Template HasSnaky 3 (childrenC_391_i0 j) (childrenD_391_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_391_i1.mono (by decide +kernel)
theorem row_works_391_i0 : Template HasSnaky 4 required_391_i0 envelope_391_i0 := by
  refine compose HasSnaky 3 childrenC_391_i0 childrenD_391_i0 children_work_391_i0 (2, 1)
    required_391_i0 envelope_391_i0 pivot_mem_391_i0 child_required_sub_391_i0 child_envelope_sub_391_i0 ?_
  intro b hb
  exact common_sub_391_i0 (mem_commonEnvelope childrenD_391_i0 b hb)
def required_391 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_391 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_391 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_391_i0]
def childrenD_391 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_391_i0]
theorem common_sub_391 : commonEnvelope childrenD_391 ⊆ insert (2, 4) required_391 := by decide +kernel
theorem child_required_sub_391 : ∀ j, childrenC_391 j ⊆ insert (2, 4) required_391 := by decide +kernel
theorem child_envelope_sub_391 : ∀ j, childrenD_391 j ⊆ envelope_391 := by decide +kernel
theorem pivot_mem_391 : (2, 4) ∈ envelope_391 := by decide +kernel
theorem children_work_391 : ∀ j, Template HasSnaky 4 (childrenC_391 j) (childrenD_391 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_391_i0.mono (by decide +kernel)
theorem row_works_391 : Template HasSnaky 5 required_391 envelope_391 := by
  refine compose HasSnaky 4 childrenC_391 childrenD_391 children_work_391 (2, 4)
    required_391 envelope_391 pivot_mem_391 child_required_sub_391 child_envelope_sub_391 ?_
  intro b hb
  exact common_sub_391 (mem_commonEnvelope childrenD_391 b hb)
def required_413_i0 : Finset Cell := ⟨(([(1, 1), (1, 3), (1, 4), (2, 1), (2, 2), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_413_i0 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 4), (3, 5), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_413_i0 : Fin 2 → Finset Cell := ![(placed21 7 (2, 4) required_5), (placed21 1 (0, 1) required_45)]
def childrenD_413_i0 : Fin 2 → Finset Cell := ![(placed21 7 (2, 4) envelope_5), (placed21 1 (0, 1) envelope_45)]
theorem common_sub_413_i0 : commonEnvelope childrenD_413_i0 ⊆ insert (2, 3) required_413_i0 := by decide +kernel
theorem child_required_sub_413_i0 : ∀ j, childrenC_413_i0 j ⊆ insert (2, 3) required_413_i0 := by decide +kernel
theorem child_envelope_sub_413_i0 : ∀ j, childrenD_413_i0 j ⊆ envelope_413_i0 := by decide +kernel
theorem pivot_mem_413_i0 : (2, 3) ∈ envelope_413_i0 := by decide +kernel
theorem children_work_413_i0 : ∀ j, Template HasSnaky 3 (childrenC_413_i0 j) (childrenD_413_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_45 1 (0, 1)).mono (by decide +kernel)
theorem row_works_413_i0 : Template HasSnaky 4 required_413_i0 envelope_413_i0 := by
  refine compose HasSnaky 3 childrenC_413_i0 childrenD_413_i0 children_work_413_i0 (2, 3)
    required_413_i0 envelope_413_i0 pivot_mem_413_i0 child_required_sub_413_i0 child_envelope_sub_413_i0 ?_
  intro b hb
  exact common_sub_413_i0 (mem_commonEnvelope childrenD_413_i0 b hb)
def required_413 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_413 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_413 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_413_i0]
def childrenD_413 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_413_i0]
theorem common_sub_413 : commonEnvelope childrenD_413 ⊆ insert (2, 4) required_413 := by decide +kernel
theorem child_required_sub_413 : ∀ j, childrenC_413 j ⊆ insert (2, 4) required_413 := by decide +kernel
theorem child_envelope_sub_413 : ∀ j, childrenD_413 j ⊆ envelope_413 := by decide +kernel
theorem pivot_mem_413 : (2, 4) ∈ envelope_413 := by decide +kernel
theorem children_work_413 : ∀ j, Template HasSnaky 4 (childrenC_413 j) (childrenD_413 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_413_i0.mono (by decide +kernel)
theorem row_works_413 : Template HasSnaky 5 required_413 envelope_413 := by
  refine compose HasSnaky 4 childrenC_413 childrenD_413 children_work_413 (2, 4)
    required_413 envelope_413 pivot_mem_413 child_required_sub_413 child_envelope_sub_413 ?_
  intro b hb
  exact common_sub_413 (mem_commonEnvelope childrenD_413 b hb)
def required_416_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_416_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_416_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), (placed21 4 (0, 5) required_239)]
def childrenD_416_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), (placed21 4 (0, 5) envelope_239)]
theorem common_sub_416_i0 : commonEnvelope childrenD_416_i0 ⊆ insert (3, 1) required_416_i0 := by decide +kernel
theorem child_required_sub_416_i0 : ∀ j, childrenC_416_i0 j ⊆ insert (3, 1) required_416_i0 := by decide +kernel
theorem child_envelope_sub_416_i0 : ∀ j, childrenD_416_i0 j ⊆ envelope_416_i0 := by decide +kernel
theorem pivot_mem_416_i0 : (3, 1) ∈ envelope_416_i0 := by decide +kernel
theorem children_work_416_i0 : ∀ j, Template HasSnaky 3 (childrenC_416_i0 j) (childrenD_416_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_239 4 (0, 5)).mono (by decide +kernel)
theorem row_works_416_i0 : Template HasSnaky 4 required_416_i0 envelope_416_i0 := by
  refine compose HasSnaky 3 childrenC_416_i0 childrenD_416_i0 children_work_416_i0 (3, 1)
    required_416_i0 envelope_416_i0 pivot_mem_416_i0 child_required_sub_416_i0 child_envelope_sub_416_i0 ?_
  intro b hb
  exact common_sub_416_i0 (mem_commonEnvelope childrenD_416_i0 b hb)
def required_416 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_416 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_416 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), required_416_i0]
def childrenD_416 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), envelope_416_i0]
theorem common_sub_416 : commonEnvelope childrenD_416 ⊆ insert (3, 3) required_416 := by decide +kernel
theorem child_required_sub_416 : ∀ j, childrenC_416 j ⊆ insert (3, 3) required_416 := by decide +kernel
theorem child_envelope_sub_416 : ∀ j, childrenD_416 j ⊆ envelope_416 := by decide +kernel
theorem pivot_mem_416 : (3, 3) ∈ envelope_416 := by decide +kernel
theorem children_work_416 : ∀ j, Template HasSnaky 4 (childrenC_416 j) (childrenD_416 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_416_i0.mono (by decide +kernel)
theorem row_works_416 : Template HasSnaky 5 required_416 envelope_416 := by
  refine compose HasSnaky 4 childrenC_416 childrenD_416 children_work_416 (3, 3)
    required_416 envelope_416 pivot_mem_416 child_required_sub_416 child_envelope_sub_416 ?_
  intro b hb
  exact common_sub_416 (mem_commonEnvelope childrenD_416 b hb)
def required_425_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_425_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_425_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_2), (placed21 0 (3, 0) required_44)]
def childrenD_425_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_2), (placed21 0 (3, 0) envelope_44)]
theorem common_sub_425_i0 : commonEnvelope childrenD_425_i0 ⊆ insert (3, 2) required_425_i0 := by decide +kernel
theorem child_required_sub_425_i0 : ∀ j, childrenC_425_i0 j ⊆ insert (3, 2) required_425_i0 := by decide +kernel
theorem child_envelope_sub_425_i0 : ∀ j, childrenD_425_i0 j ⊆ envelope_425_i0 := by decide +kernel
theorem pivot_mem_425_i0 : (3, 2) ∈ envelope_425_i0 := by decide +kernel
theorem children_work_425_i0 : ∀ j, Template HasSnaky 3 (childrenC_425_i0 j) (childrenD_425_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 0 (3, 0)).mono (by decide +kernel)
theorem row_works_425_i0 : Template HasSnaky 4 required_425_i0 envelope_425_i0 := by
  refine compose HasSnaky 3 childrenC_425_i0 childrenD_425_i0 children_work_425_i0 (3, 2)
    required_425_i0 envelope_425_i0 pivot_mem_425_i0 child_required_sub_425_i0 child_envelope_sub_425_i0 ?_
  intro b hb
  exact common_sub_425_i0 (mem_commonEnvelope childrenD_425_i0 b hb)
def required_425 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (3, 1), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_425 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_425 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_2), required_425_i0]
def childrenD_425 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_2), envelope_425_i0]
theorem common_sub_425 : commonEnvelope childrenD_425 ⊆ insert (4, 3) required_425 := by decide +kernel
theorem child_required_sub_425 : ∀ j, childrenC_425 j ⊆ insert (4, 3) required_425 := by decide +kernel
theorem child_envelope_sub_425 : ∀ j, childrenD_425 j ⊆ envelope_425 := by decide +kernel
theorem pivot_mem_425 : (4, 3) ∈ envelope_425 := by decide +kernel
theorem children_work_425 : ∀ j, Template HasSnaky 4 (childrenC_425 j) (childrenD_425 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 6 (4, 3)).mono (by decide +kernel)
  · exact row_works_425_i0.mono (by decide +kernel)
theorem row_works_425 : Template HasSnaky 5 required_425 envelope_425 := by
  refine compose HasSnaky 4 childrenC_425 childrenD_425 children_work_425 (4, 3)
    required_425 envelope_425 pivot_mem_425 child_required_sub_425 child_envelope_sub_425 ?_
  intro b hb
  exact common_sub_425 (mem_commonEnvelope childrenD_425 b hb)
def required_426_i0 : Finset Cell := ⟨(([(1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_426_i0 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_426_i0 : Fin 2 → Finset Cell := ![(placed21 6 (5, 3) required_0), (placed21 2 (4, 1) required_221)]
def childrenD_426_i0 : Fin 2 → Finset Cell := ![(placed21 6 (5, 3) envelope_0), (placed21 2 (4, 1) envelope_221)]
theorem common_sub_426_i0 : commonEnvelope childrenD_426_i0 ⊆ insert (3, 3) required_426_i0 := by decide +kernel
theorem child_required_sub_426_i0 : ∀ j, childrenC_426_i0 j ⊆ insert (3, 3) required_426_i0 := by decide +kernel
theorem child_envelope_sub_426_i0 : ∀ j, childrenD_426_i0 j ⊆ envelope_426_i0 := by decide +kernel
theorem pivot_mem_426_i0 : (3, 3) ∈ envelope_426_i0 := by decide +kernel
theorem children_work_426_i0 : ∀ j, Template HasSnaky 3 (childrenC_426_i0 j) (childrenD_426_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_221 2 (4, 1)).mono (by decide +kernel)
theorem row_works_426_i0 : Template HasSnaky 4 required_426_i0 envelope_426_i0 := by
  refine compose HasSnaky 3 childrenC_426_i0 childrenD_426_i0 children_work_426_i0 (3, 3)
    required_426_i0 envelope_426_i0 pivot_mem_426_i0 child_required_sub_426_i0 child_envelope_sub_426_i0 ?_
  intro b hb
  exact common_sub_426_i0 (mem_commonEnvelope childrenD_426_i0 b hb)
def required_426 : Finset Cell := ⟨(([(1, 2), (2, 1), (2, 2), (2, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_426 : Finset Cell := ⟨(([(0, 4), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_426 : Fin 2 → Finset Cell := ![(placed21 2 (2, 0) required_11), required_426_i0]
def childrenD_426 : Fin 2 → Finset Cell := ![(placed21 2 (2, 0) envelope_11), envelope_426_i0]
theorem common_sub_426 : commonEnvelope childrenD_426 ⊆ insert (2, 4) required_426 := by decide +kernel
theorem child_required_sub_426 : ∀ j, childrenC_426 j ⊆ insert (2, 4) required_426 := by decide +kernel
theorem child_envelope_sub_426 : ∀ j, childrenD_426 j ⊆ envelope_426 := by decide +kernel
theorem pivot_mem_426 : (2, 4) ∈ envelope_426 := by decide +kernel
theorem children_work_426 : ∀ j, Template HasSnaky 4 (childrenC_426 j) (childrenD_426 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 2 (2, 0)).mono (by decide +kernel)
  · exact row_works_426_i0.mono (by decide +kernel)
theorem row_works_426 : Template HasSnaky 5 required_426 envelope_426 := by
  refine compose HasSnaky 4 childrenC_426 childrenD_426 children_work_426 (2, 4)
    required_426 envelope_426 pivot_mem_426 child_required_sub_426 child_envelope_sub_426 ?_
  intro b hb
  exact common_sub_426 (mem_commonEnvelope childrenD_426 b hb)
def required_433 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_433 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_433 : Fin 2 → Finset Cell := ![required_86, (placed21 5 (4, 1) required_432)]
def childrenD_433 : Fin 2 → Finset Cell := ![envelope_86, (placed21 5 (4, 1) envelope_432)]
theorem common_sub_433 : commonEnvelope childrenD_433 ⊆ insert (3, 4) required_433 := by decide +kernel
theorem child_required_sub_433 : ∀ j, childrenC_433 j ⊆ insert (3, 4) required_433 := by decide +kernel
theorem child_envelope_sub_433 : ∀ j, childrenD_433 j ⊆ envelope_433 := by decide +kernel
theorem pivot_mem_433 : (3, 4) ∈ envelope_433 := by decide +kernel
theorem children_work_433 : ∀ j, Template HasSnaky 4 (childrenC_433 j) (childrenD_433 j) := by
  intro j
  fin_cases j
  · exact row_works_86.mono (by decide +kernel)
  · exact (placed21_template row_works_432 5 (4, 1)).mono (by decide +kernel)
theorem row_works_433 : Template HasSnaky 5 required_433 envelope_433 := by
  refine compose HasSnaky 4 childrenC_433 childrenD_433 children_work_433 (3, 4)
    required_433 envelope_433 pivot_mem_433 child_required_sub_433 child_envelope_sub_433 ?_
  intro b hb
  exact common_sub_433 (mem_commonEnvelope childrenD_433 b hb)
def required_445_i0 : Finset Cell := ⟨(([(1, 2), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_445_i0 : Finset Cell := ⟨(([(1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_445_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) required_20), (placed21 2 (3, 0) required_29), (placed21 0 (1, 0) required_221)]
def childrenD_445_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) envelope_20), (placed21 2 (3, 0) envelope_29), (placed21 0 (1, 0) envelope_221)]
theorem common_sub_445_i0 : commonEnvelope childrenD_445_i0 ⊆ insert (3, 3) required_445_i0 := by decide +kernel
theorem child_required_sub_445_i0 : ∀ j, childrenC_445_i0 j ⊆ insert (3, 3) required_445_i0 := by decide +kernel
theorem child_envelope_sub_445_i0 : ∀ j, childrenD_445_i0 j ⊆ envelope_445_i0 := by decide +kernel
theorem pivot_mem_445_i0 : (3, 3) ∈ envelope_445_i0 := by decide +kernel
theorem children_work_445_i0 : ∀ j, Template HasSnaky 3 (childrenC_445_i0 j) (childrenD_445_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_221 0 (1, 0)).mono (by decide +kernel)
theorem row_works_445_i0 : Template HasSnaky 4 required_445_i0 envelope_445_i0 := by
  refine compose HasSnaky 3 childrenC_445_i0 childrenD_445_i0 children_work_445_i0 (3, 3)
    required_445_i0 envelope_445_i0 pivot_mem_445_i0 child_required_sub_445_i0 child_envelope_sub_445_i0 ?_
  intro b hb
  exact common_sub_445_i0 (mem_commonEnvelope childrenD_445_i0 b hb)
def required_445 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_445 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_445 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), required_445_i0]
def childrenD_445 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), envelope_445_i0]
theorem common_sub_445 : commonEnvelope childrenD_445 ⊆ insert (3, 0) required_445 := by decide +kernel
theorem child_required_sub_445 : ∀ j, childrenC_445 j ⊆ insert (3, 0) required_445 := by decide +kernel
theorem child_envelope_sub_445 : ∀ j, childrenD_445 j ⊆ envelope_445 := by decide +kernel
theorem pivot_mem_445 : (3, 0) ∈ envelope_445 := by decide +kernel
theorem children_work_445 : ∀ j, Template HasSnaky 4 (childrenC_445 j) (childrenD_445 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_445_i0.mono (by decide +kernel)
theorem row_works_445 : Template HasSnaky 5 required_445 envelope_445 := by
  refine compose HasSnaky 4 childrenC_445 childrenD_445 children_work_445 (3, 0)
    required_445 envelope_445 pivot_mem_445 child_required_sub_445 child_envelope_sub_445 ?_
  intro b hb
  exact common_sub_445 (mem_commonEnvelope childrenD_445 b hb)
def required_451_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_451_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_451_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), required_402]
def childrenD_451_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), envelope_402]
theorem common_sub_451_i0 : commonEnvelope childrenD_451_i0 ⊆ insert (2, 3) required_451_i0 := by decide +kernel
theorem child_required_sub_451_i0 : ∀ j, childrenC_451_i0 j ⊆ insert (2, 3) required_451_i0 := by decide +kernel
theorem child_envelope_sub_451_i0 : ∀ j, childrenD_451_i0 j ⊆ envelope_451_i0 := by decide +kernel
theorem pivot_mem_451_i0 : (2, 3) ∈ envelope_451_i0 := by decide +kernel
theorem children_work_451_i0 : ∀ j, Template HasSnaky 3 (childrenC_451_i0 j) (childrenD_451_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact row_works_402.mono (by decide +kernel)
theorem row_works_451_i0 : Template HasSnaky 4 required_451_i0 envelope_451_i0 := by
  refine compose HasSnaky 3 childrenC_451_i0 childrenD_451_i0 children_work_451_i0 (2, 3)
    required_451_i0 envelope_451_i0 pivot_mem_451_i0 child_required_sub_451_i0 child_envelope_sub_451_i0 ?_
  intro b hb
  exact common_sub_451_i0 (mem_commonEnvelope childrenD_451_i0 b hb)
def required_451 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_451 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_451 : Fin 2 → Finset Cell := ![(placed21 2 (1, 0) required_11), required_451_i0]
def childrenD_451 : Fin 2 → Finset Cell := ![(placed21 2 (1, 0) envelope_11), envelope_451_i0]
theorem common_sub_451 : commonEnvelope childrenD_451 ⊆ insert (1, 4) required_451 := by decide +kernel
theorem child_required_sub_451 : ∀ j, childrenC_451 j ⊆ insert (1, 4) required_451 := by decide +kernel
theorem child_envelope_sub_451 : ∀ j, childrenD_451 j ⊆ envelope_451 := by decide +kernel
theorem pivot_mem_451 : (1, 4) ∈ envelope_451 := by decide +kernel
theorem children_work_451 : ∀ j, Template HasSnaky 4 (childrenC_451 j) (childrenD_451 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 2 (1, 0)).mono (by decide +kernel)
  · exact row_works_451_i0.mono (by decide +kernel)
theorem row_works_451 : Template HasSnaky 5 required_451 envelope_451 := by
  refine compose HasSnaky 4 childrenC_451 childrenD_451 children_work_451 (1, 4)
    required_451 envelope_451 pivot_mem_451 child_required_sub_451 child_envelope_sub_451 ?_
  intro b hb
  exact common_sub_451 (mem_commonEnvelope childrenD_451 b hb)
def required_464_i1 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_464_i1 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_464_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) required_0), (placed21 0 (1, 0) required_11)]
def childrenD_464_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 0) envelope_0), (placed21 0 (1, 0) envelope_11)]
theorem common_sub_464_i1 : commonEnvelope childrenD_464_i1 ⊆ insert (1, 1) required_464_i1 := by decide +kernel
theorem child_required_sub_464_i1 : ∀ j, childrenC_464_i1 j ⊆ insert (1, 1) required_464_i1 := by decide +kernel
theorem child_envelope_sub_464_i1 : ∀ j, childrenD_464_i1 j ⊆ envelope_464_i1 := by decide +kernel
theorem pivot_mem_464_i1 : (1, 1) ∈ envelope_464_i1 := by decide +kernel
theorem children_work_464_i1 : ∀ j, Template HasSnaky 2 (childrenC_464_i1 j) (childrenD_464_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 0 (1, 0)).mono (by decide +kernel)
theorem row_works_464_i1 : Template HasSnaky 3 required_464_i1 envelope_464_i1 := by
  refine compose HasSnaky 2 childrenC_464_i1 childrenD_464_i1 children_work_464_i1 (1, 1)
    required_464_i1 envelope_464_i1 pivot_mem_464_i1 child_required_sub_464_i1 child_envelope_sub_464_i1 ?_
  intro b hb
  exact common_sub_464_i1 (mem_commonEnvelope childrenD_464_i1 b hb)
def required_464_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_464_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_464_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_0), required_464_i1]
def childrenD_464_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_0), envelope_464_i1]
theorem common_sub_464_i0 : commonEnvelope childrenD_464_i0 ⊆ insert (2, 2) required_464_i0 := by decide +kernel
theorem child_required_sub_464_i0 : ∀ j, childrenC_464_i0 j ⊆ insert (2, 2) required_464_i0 := by decide +kernel
theorem child_envelope_sub_464_i0 : ∀ j, childrenD_464_i0 j ⊆ envelope_464_i0 := by decide +kernel
theorem pivot_mem_464_i0 : (2, 2) ∈ envelope_464_i0 := by decide +kernel
theorem children_work_464_i0 : ∀ j, Template HasSnaky 3 (childrenC_464_i0 j) (childrenD_464_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact row_works_464_i1.mono (by decide +kernel)
theorem row_works_464_i0 : Template HasSnaky 4 required_464_i0 envelope_464_i0 := by
  refine compose HasSnaky 3 childrenC_464_i0 childrenD_464_i0 children_work_464_i0 (2, 2)
    required_464_i0 envelope_464_i0 pivot_mem_464_i0 child_required_sub_464_i0 child_envelope_sub_464_i0 ?_
  intro b hb
  exact common_sub_464_i0 (mem_commonEnvelope childrenD_464_i0 b hb)
def required_464_i2 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_464_i2 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_464_i2 : Fin 2 → Finset Cell := ![(placed21 2 (1, 2) required_29), (placed21 3 (0, 5) required_38)]
def childrenD_464_i2 : Fin 2 → Finset Cell := ![(placed21 2 (1, 2) envelope_29), (placed21 3 (0, 5) envelope_38)]
theorem common_sub_464_i2 : commonEnvelope childrenD_464_i2 ⊆ insert (1, 5) required_464_i2 := by decide +kernel
theorem child_required_sub_464_i2 : ∀ j, childrenC_464_i2 j ⊆ insert (1, 5) required_464_i2 := by decide +kernel
theorem child_envelope_sub_464_i2 : ∀ j, childrenD_464_i2 j ⊆ envelope_464_i2 := by decide +kernel
theorem pivot_mem_464_i2 : (1, 5) ∈ envelope_464_i2 := by decide +kernel
theorem children_work_464_i2 : ∀ j, Template HasSnaky 3 (childrenC_464_i2 j) (childrenD_464_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_29 2 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_38 3 (0, 5)).mono (by decide +kernel)
theorem row_works_464_i2 : Template HasSnaky 4 required_464_i2 envelope_464_i2 := by
  refine compose HasSnaky 3 childrenC_464_i2 childrenD_464_i2 children_work_464_i2 (1, 5)
    required_464_i2 envelope_464_i2 pivot_mem_464_i2 child_required_sub_464_i2 child_envelope_sub_464_i2 ?_
  intro b hb
  exact common_sub_464_i2 (mem_commonEnvelope childrenD_464_i2 b hb)
def required_464 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 3), (1, 4), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_464 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_464 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) required_15), required_464_i0, required_464_i2]
def childrenD_464 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) envelope_15), envelope_464_i0, envelope_464_i2]
theorem common_sub_464 : commonEnvelope childrenD_464 ⊆ insert (1, 2) required_464 := by decide +kernel
theorem child_required_sub_464 : ∀ j, childrenC_464 j ⊆ insert (1, 2) required_464 := by decide +kernel
theorem child_envelope_sub_464 : ∀ j, childrenD_464 j ⊆ envelope_464 := by decide +kernel
theorem pivot_mem_464 : (1, 2) ∈ envelope_464 := by decide +kernel
theorem children_work_464 : ∀ j, Template HasSnaky 4 (childrenC_464 j) (childrenD_464 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 2 (1, 1)).mono (by decide +kernel)
  · exact row_works_464_i0.mono (by decide +kernel)
  · exact row_works_464_i2.mono (by decide +kernel)
theorem row_works_464 : Template HasSnaky 5 required_464 envelope_464 := by
  refine compose HasSnaky 4 childrenC_464 childrenD_464 children_work_464 (1, 2)
    required_464 envelope_464 pivot_mem_464 child_required_sub_464 child_envelope_sub_464 ?_
  intro b hb
  exact common_sub_464 (mem_commonEnvelope childrenD_464 b hb)
def required_492_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_492_i1 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_492_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), (placed21 5 (4, 1) required_32)]
def childrenD_492_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), (placed21 5 (4, 1) envelope_32)]
theorem common_sub_492_i1 : commonEnvelope childrenD_492_i1 ⊆ insert (2, 3) required_492_i1 := by decide +kernel
theorem child_required_sub_492_i1 : ∀ j, childrenC_492_i1 j ⊆ insert (2, 3) required_492_i1 := by decide +kernel
theorem child_envelope_sub_492_i1 : ∀ j, childrenD_492_i1 j ⊆ envelope_492_i1 := by decide +kernel
theorem pivot_mem_492_i1 : (2, 3) ∈ envelope_492_i1 := by decide +kernel
theorem children_work_492_i1 : ∀ j, Template HasSnaky 2 (childrenC_492_i1 j) (childrenD_492_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 5 (4, 1)).mono (by decide +kernel)
theorem row_works_492_i1 : Template HasSnaky 3 required_492_i1 envelope_492_i1 := by
  refine compose HasSnaky 2 childrenC_492_i1 childrenD_492_i1 children_work_492_i1 (2, 3)
    required_492_i1 envelope_492_i1 pivot_mem_492_i1 child_required_sub_492_i1 child_envelope_sub_492_i1 ?_
  intro b hb
  exact common_sub_492_i1 (mem_commonEnvelope childrenD_492_i1 b hb)
def required_492_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 2), (1, 4), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_492_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_492_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), required_492_i1]
def childrenD_492_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), envelope_492_i1]
theorem common_sub_492_i0 : commonEnvelope childrenD_492_i0 ⊆ insert (1, 3) required_492_i0 := by decide +kernel
theorem child_required_sub_492_i0 : ∀ j, childrenC_492_i0 j ⊆ insert (1, 3) required_492_i0 := by decide +kernel
theorem child_envelope_sub_492_i0 : ∀ j, childrenD_492_i0 j ⊆ envelope_492_i0 := by decide +kernel
theorem pivot_mem_492_i0 : (1, 3) ∈ envelope_492_i0 := by decide +kernel
theorem children_work_492_i0 : ∀ j, Template HasSnaky 3 (childrenC_492_i0 j) (childrenD_492_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact row_works_492_i1.mono (by decide +kernel)
theorem row_works_492_i0 : Template HasSnaky 4 required_492_i0 envelope_492_i0 := by
  refine compose HasSnaky 3 childrenC_492_i0 childrenD_492_i0 children_work_492_i0 (1, 3)
    required_492_i0 envelope_492_i0 pivot_mem_492_i0 child_required_sub_492_i0 child_envelope_sub_492_i0 ?_
  intro b hb
  exact common_sub_492_i0 (mem_commonEnvelope childrenD_492_i0 b hb)
def required_492 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_492 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_492 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) required_78), required_492_i0]
def childrenD_492 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) envelope_78), envelope_492_i0]
theorem common_sub_492 : commonEnvelope childrenD_492 ⊆ insert (1, 2) required_492 := by decide +kernel
theorem child_required_sub_492 : ∀ j, childrenC_492 j ⊆ insert (1, 2) required_492 := by decide +kernel
theorem child_envelope_sub_492 : ∀ j, childrenD_492 j ⊆ envelope_492 := by decide +kernel
theorem pivot_mem_492 : (1, 2) ∈ envelope_492 := by decide +kernel
theorem children_work_492 : ∀ j, Template HasSnaky 4 (childrenC_492 j) (childrenD_492 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_78 7 (4, 4)).mono (by decide +kernel)
  · exact row_works_492_i0.mono (by decide +kernel)
theorem row_works_492 : Template HasSnaky 5 required_492 envelope_492 := by
  refine compose HasSnaky 4 childrenC_492 childrenD_492 children_work_492 (1, 2)
    required_492 envelope_492 pivot_mem_492 child_required_sub_492 child_envelope_sub_492 ?_
  intro b hb
  exact common_sub_492 (mem_commonEnvelope childrenD_492 b hb)
def height_391_i1 : ℕ := 3
def childrenH_391_i1 : Fin 2 → ℕ := ![height_0, height_36]
theorem height_exact_391_i1 : height_391_i1 = 1 + Finset.univ.sup childrenH_391_i1 := by decide +kernel
theorem required_origin_391_i1 : ∀ x ∈ required_391_i1,
    (∃ j, x ∈ childrenC_391_i1 j) ∨ ∀ j, x ∈ childrenD_391_i1 j := by decide +kernel
theorem required_exact_391_i1 : required_391_i1 =
    ((Finset.univ.biUnion childrenC_391_i1) ∪ commonEnvelope childrenD_391_i1).erase (3, 1) := by
  exact required_eq_combination childrenC_391_i1 childrenD_391_i1 (3, 1) required_391_i1
    (by decide +kernel) child_required_sub_391_i1 common_sub_391_i1 required_origin_391_i1
theorem envelope_origin_391_i1 : ∀ x ∈ envelope_391_i1,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_391_i1 j := by decide +kernel
theorem envelope_exact_391_i1 : envelope_391_i1 =
    insert (3, 1) (Finset.univ.biUnion childrenD_391_i1) := by
  exact envelope_eq_combination childrenD_391_i1 (3, 1) envelope_391_i1
    pivot_mem_391_i1 child_envelope_sub_391_i1 envelope_origin_391_i1
def checked_391_i1 : CheckedCard where
  required := required_391_i1
  envelope := envelope_391_i1
  height := height_391_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_391_i1
def height_391_i0 : ℕ := 4
def childrenH_391_i0 : Fin 2 → ℕ := ![height_5, height_391_i1]
theorem height_exact_391_i0 : height_391_i0 = 1 + Finset.univ.sup childrenH_391_i0 := by decide +kernel
theorem required_origin_391_i0 : ∀ x ∈ required_391_i0,
    (∃ j, x ∈ childrenC_391_i0 j) ∨ ∀ j, x ∈ childrenD_391_i0 j := by decide +kernel
theorem required_exact_391_i0 : required_391_i0 =
    ((Finset.univ.biUnion childrenC_391_i0) ∪ commonEnvelope childrenD_391_i0).erase (2, 1) := by
  exact required_eq_combination childrenC_391_i0 childrenD_391_i0 (2, 1) required_391_i0
    (by decide +kernel) child_required_sub_391_i0 common_sub_391_i0 required_origin_391_i0
theorem envelope_origin_391_i0 : ∀ x ∈ envelope_391_i0,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_391_i0 j := by decide +kernel
theorem envelope_exact_391_i0 : envelope_391_i0 =
    insert (2, 1) (Finset.univ.biUnion childrenD_391_i0) := by
  exact envelope_eq_combination childrenD_391_i0 (2, 1) envelope_391_i0
    pivot_mem_391_i0 child_envelope_sub_391_i0 envelope_origin_391_i0
def checked_391_i0 : CheckedCard where
  required := required_391_i0
  envelope := envelope_391_i0
  height := height_391_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_391_i0
def height_391 : ℕ := 5
def childrenH_391 : Fin 2 → ℕ := ![height_5, height_391_i0]
theorem height_exact_391 : height_391 = 1 + Finset.univ.sup childrenH_391 := by decide +kernel
theorem required_origin_391 : ∀ x ∈ required_391,
    (∃ j, x ∈ childrenC_391 j) ∨ ∀ j, x ∈ childrenD_391 j := by decide +kernel
theorem required_exact_391 : required_391 =
    ((Finset.univ.biUnion childrenC_391) ∪ commonEnvelope childrenD_391).erase (2, 4) := by
  exact required_eq_combination childrenC_391 childrenD_391 (2, 4) required_391
    (by decide +kernel) child_required_sub_391 common_sub_391 required_origin_391
theorem envelope_origin_391 : ∀ x ∈ envelope_391,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_391 j := by decide +kernel
theorem envelope_exact_391 : envelope_391 =
    insert (2, 4) (Finset.univ.biUnion childrenD_391) := by
  exact envelope_eq_combination childrenD_391 (2, 4) envelope_391
    pivot_mem_391 child_envelope_sub_391 envelope_origin_391
def checked_391 : CheckedCard where
  required := required_391
  envelope := envelope_391
  height := height_391
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_391
def height_413_i0 : ℕ := 4
def childrenH_413_i0 : Fin 2 → ℕ := ![height_5, height_45]
theorem height_exact_413_i0 : height_413_i0 = 1 + Finset.univ.sup childrenH_413_i0 := by decide +kernel
theorem required_origin_413_i0 : ∀ x ∈ required_413_i0,
    (∃ j, x ∈ childrenC_413_i0 j) ∨ ∀ j, x ∈ childrenD_413_i0 j := by decide +kernel
theorem required_exact_413_i0 : required_413_i0 =
    ((Finset.univ.biUnion childrenC_413_i0) ∪ commonEnvelope childrenD_413_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_413_i0 childrenD_413_i0 (2, 3) required_413_i0
    (by decide +kernel) child_required_sub_413_i0 common_sub_413_i0 required_origin_413_i0
theorem envelope_origin_413_i0 : ∀ x ∈ envelope_413_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_413_i0 j := by decide +kernel
theorem envelope_exact_413_i0 : envelope_413_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_413_i0) := by
  exact envelope_eq_combination childrenD_413_i0 (2, 3) envelope_413_i0
    pivot_mem_413_i0 child_envelope_sub_413_i0 envelope_origin_413_i0
def checked_413_i0 : CheckedCard where
  required := required_413_i0
  envelope := envelope_413_i0
  height := height_413_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_413_i0
def height_413 : ℕ := 5
def childrenH_413 : Fin 2 → ℕ := ![height_5, height_413_i0]
theorem height_exact_413 : height_413 = 1 + Finset.univ.sup childrenH_413 := by decide +kernel
theorem required_origin_413 : ∀ x ∈ required_413,
    (∃ j, x ∈ childrenC_413 j) ∨ ∀ j, x ∈ childrenD_413 j := by decide +kernel
theorem required_exact_413 : required_413 =
    ((Finset.univ.biUnion childrenC_413) ∪ commonEnvelope childrenD_413).erase (2, 4) := by
  exact required_eq_combination childrenC_413 childrenD_413 (2, 4) required_413
    (by decide +kernel) child_required_sub_413 common_sub_413 required_origin_413
theorem envelope_origin_413 : ∀ x ∈ envelope_413,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_413 j := by decide +kernel
theorem envelope_exact_413 : envelope_413 =
    insert (2, 4) (Finset.univ.biUnion childrenD_413) := by
  exact envelope_eq_combination childrenD_413 (2, 4) envelope_413
    pivot_mem_413 child_envelope_sub_413 envelope_origin_413
def checked_413 : CheckedCard where
  required := required_413
  envelope := envelope_413
  height := height_413
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_413
def height_416_i0 : ℕ := 4
def childrenH_416_i0 : Fin 2 → ℕ := ![height_5, height_239]
theorem height_exact_416_i0 : height_416_i0 = 1 + Finset.univ.sup childrenH_416_i0 := by decide +kernel
theorem required_origin_416_i0 : ∀ x ∈ required_416_i0,
    (∃ j, x ∈ childrenC_416_i0 j) ∨ ∀ j, x ∈ childrenD_416_i0 j := by decide +kernel
theorem required_exact_416_i0 : required_416_i0 =
    ((Finset.univ.biUnion childrenC_416_i0) ∪ commonEnvelope childrenD_416_i0).erase (3, 1) := by
  exact required_eq_combination childrenC_416_i0 childrenD_416_i0 (3, 1) required_416_i0
    (by decide +kernel) child_required_sub_416_i0 common_sub_416_i0 required_origin_416_i0
theorem envelope_origin_416_i0 : ∀ x ∈ envelope_416_i0,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_416_i0 j := by decide +kernel
theorem envelope_exact_416_i0 : envelope_416_i0 =
    insert (3, 1) (Finset.univ.biUnion childrenD_416_i0) := by
  exact envelope_eq_combination childrenD_416_i0 (3, 1) envelope_416_i0
    pivot_mem_416_i0 child_envelope_sub_416_i0 envelope_origin_416_i0
def checked_416_i0 : CheckedCard where
  required := required_416_i0
  envelope := envelope_416_i0
  height := height_416_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_416_i0
def height_416 : ℕ := 5
def childrenH_416 : Fin 2 → ℕ := ![height_5, height_416_i0]
theorem height_exact_416 : height_416 = 1 + Finset.univ.sup childrenH_416 := by decide +kernel
theorem required_origin_416 : ∀ x ∈ required_416,
    (∃ j, x ∈ childrenC_416 j) ∨ ∀ j, x ∈ childrenD_416 j := by decide +kernel
theorem required_exact_416 : required_416 =
    ((Finset.univ.biUnion childrenC_416) ∪ commonEnvelope childrenD_416).erase (3, 3) := by
  exact required_eq_combination childrenC_416 childrenD_416 (3, 3) required_416
    (by decide +kernel) child_required_sub_416 common_sub_416 required_origin_416
theorem envelope_origin_416 : ∀ x ∈ envelope_416,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_416 j := by decide +kernel
theorem envelope_exact_416 : envelope_416 =
    insert (3, 3) (Finset.univ.biUnion childrenD_416) := by
  exact envelope_eq_combination childrenD_416 (3, 3) envelope_416
    pivot_mem_416 child_envelope_sub_416 envelope_origin_416
def checked_416 : CheckedCard where
  required := required_416
  envelope := envelope_416
  height := height_416
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_416
def height_425_i0 : ℕ := 4
def childrenH_425_i0 : Fin 2 → ℕ := ![height_2, height_44]
theorem height_exact_425_i0 : height_425_i0 = 1 + Finset.univ.sup childrenH_425_i0 := by decide +kernel
theorem required_origin_425_i0 : ∀ x ∈ required_425_i0,
    (∃ j, x ∈ childrenC_425_i0 j) ∨ ∀ j, x ∈ childrenD_425_i0 j := by decide +kernel
theorem required_exact_425_i0 : required_425_i0 =
    ((Finset.univ.biUnion childrenC_425_i0) ∪ commonEnvelope childrenD_425_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_425_i0 childrenD_425_i0 (3, 2) required_425_i0
    (by decide +kernel) child_required_sub_425_i0 common_sub_425_i0 required_origin_425_i0
theorem envelope_origin_425_i0 : ∀ x ∈ envelope_425_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_425_i0 j := by decide +kernel
theorem envelope_exact_425_i0 : envelope_425_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_425_i0) := by
  exact envelope_eq_combination childrenD_425_i0 (3, 2) envelope_425_i0
    pivot_mem_425_i0 child_envelope_sub_425_i0 envelope_origin_425_i0
def checked_425_i0 : CheckedCard where
  required := required_425_i0
  envelope := envelope_425_i0
  height := height_425_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_425_i0
def height_425 : ℕ := 5
def childrenH_425 : Fin 2 → ℕ := ![height_2, height_425_i0]
theorem height_exact_425 : height_425 = 1 + Finset.univ.sup childrenH_425 := by decide +kernel
theorem required_origin_425 : ∀ x ∈ required_425,
    (∃ j, x ∈ childrenC_425 j) ∨ ∀ j, x ∈ childrenD_425 j := by decide +kernel
theorem required_exact_425 : required_425 =
    ((Finset.univ.biUnion childrenC_425) ∪ commonEnvelope childrenD_425).erase (4, 3) := by
  exact required_eq_combination childrenC_425 childrenD_425 (4, 3) required_425
    (by decide +kernel) child_required_sub_425 common_sub_425 required_origin_425
theorem envelope_origin_425 : ∀ x ∈ envelope_425,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_425 j := by decide +kernel
theorem envelope_exact_425 : envelope_425 =
    insert (4, 3) (Finset.univ.biUnion childrenD_425) := by
  exact envelope_eq_combination childrenD_425 (4, 3) envelope_425
    pivot_mem_425 child_envelope_sub_425 envelope_origin_425
def checked_425 : CheckedCard where
  required := required_425
  envelope := envelope_425
  height := height_425
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_425
def height_426_i0 : ℕ := 4
def childrenH_426_i0 : Fin 2 → ℕ := ![height_0, height_221]
theorem height_exact_426_i0 : height_426_i0 = 1 + Finset.univ.sup childrenH_426_i0 := by decide +kernel
theorem required_origin_426_i0 : ∀ x ∈ required_426_i0,
    (∃ j, x ∈ childrenC_426_i0 j) ∨ ∀ j, x ∈ childrenD_426_i0 j := by decide +kernel
theorem required_exact_426_i0 : required_426_i0 =
    ((Finset.univ.biUnion childrenC_426_i0) ∪ commonEnvelope childrenD_426_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_426_i0 childrenD_426_i0 (3, 3) required_426_i0
    (by decide +kernel) child_required_sub_426_i0 common_sub_426_i0 required_origin_426_i0
theorem envelope_origin_426_i0 : ∀ x ∈ envelope_426_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_426_i0 j := by decide +kernel
theorem envelope_exact_426_i0 : envelope_426_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_426_i0) := by
  exact envelope_eq_combination childrenD_426_i0 (3, 3) envelope_426_i0
    pivot_mem_426_i0 child_envelope_sub_426_i0 envelope_origin_426_i0
def checked_426_i0 : CheckedCard where
  required := required_426_i0
  envelope := envelope_426_i0
  height := height_426_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_426_i0
def height_426 : ℕ := 5
def childrenH_426 : Fin 2 → ℕ := ![height_11, height_426_i0]
theorem height_exact_426 : height_426 = 1 + Finset.univ.sup childrenH_426 := by decide +kernel
theorem required_origin_426 : ∀ x ∈ required_426,
    (∃ j, x ∈ childrenC_426 j) ∨ ∀ j, x ∈ childrenD_426 j := by decide +kernel
theorem required_exact_426 : required_426 =
    ((Finset.univ.biUnion childrenC_426) ∪ commonEnvelope childrenD_426).erase (2, 4) := by
  exact required_eq_combination childrenC_426 childrenD_426 (2, 4) required_426
    (by decide +kernel) child_required_sub_426 common_sub_426 required_origin_426
theorem envelope_origin_426 : ∀ x ∈ envelope_426,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_426 j := by decide +kernel
theorem envelope_exact_426 : envelope_426 =
    insert (2, 4) (Finset.univ.biUnion childrenD_426) := by
  exact envelope_eq_combination childrenD_426 (2, 4) envelope_426
    pivot_mem_426 child_envelope_sub_426 envelope_origin_426
def checked_426 : CheckedCard where
  required := required_426
  envelope := envelope_426
  height := height_426
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_426
def height_433 : ℕ := 5
def childrenH_433 : Fin 2 → ℕ := ![height_86, height_432]
theorem height_exact_433 : height_433 = 1 + Finset.univ.sup childrenH_433 := by decide +kernel
theorem required_origin_433 : ∀ x ∈ required_433,
    (∃ j, x ∈ childrenC_433 j) ∨ ∀ j, x ∈ childrenD_433 j := by decide +kernel
theorem required_exact_433 : required_433 =
    ((Finset.univ.biUnion childrenC_433) ∪ commonEnvelope childrenD_433).erase (3, 4) := by
  exact required_eq_combination childrenC_433 childrenD_433 (3, 4) required_433
    (by decide +kernel) child_required_sub_433 common_sub_433 required_origin_433
theorem envelope_origin_433 : ∀ x ∈ envelope_433,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_433 j := by decide +kernel
theorem envelope_exact_433 : envelope_433 =
    insert (3, 4) (Finset.univ.biUnion childrenD_433) := by
  exact envelope_eq_combination childrenD_433 (3, 4) envelope_433
    pivot_mem_433 child_envelope_sub_433 envelope_origin_433
def checked_433 : CheckedCard where
  required := required_433
  envelope := envelope_433
  height := height_433
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_433
def height_445_i0 : ℕ := 4
def childrenH_445_i0 : Fin 3 → ℕ := ![height_20, height_29, height_221]
theorem height_exact_445_i0 : height_445_i0 = 1 + Finset.univ.sup childrenH_445_i0 := by decide +kernel
theorem required_origin_445_i0 : ∀ x ∈ required_445_i0,
    (∃ j, x ∈ childrenC_445_i0 j) ∨ ∀ j, x ∈ childrenD_445_i0 j := by decide +kernel
theorem required_exact_445_i0 : required_445_i0 =
    ((Finset.univ.biUnion childrenC_445_i0) ∪ commonEnvelope childrenD_445_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_445_i0 childrenD_445_i0 (3, 3) required_445_i0
    (by decide +kernel) child_required_sub_445_i0 common_sub_445_i0 required_origin_445_i0
theorem envelope_origin_445_i0 : ∀ x ∈ envelope_445_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_445_i0 j := by decide +kernel
theorem envelope_exact_445_i0 : envelope_445_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_445_i0) := by
  exact envelope_eq_combination childrenD_445_i0 (3, 3) envelope_445_i0
    pivot_mem_445_i0 child_envelope_sub_445_i0 envelope_origin_445_i0
def checked_445_i0 : CheckedCard where
  required := required_445_i0
  envelope := envelope_445_i0
  height := height_445_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_445_i0
def height_445 : ℕ := 5
def childrenH_445 : Fin 2 → ℕ := ![height_5, height_445_i0]
theorem height_exact_445 : height_445 = 1 + Finset.univ.sup childrenH_445 := by decide +kernel
theorem required_origin_445 : ∀ x ∈ required_445,
    (∃ j, x ∈ childrenC_445 j) ∨ ∀ j, x ∈ childrenD_445 j := by decide +kernel
theorem required_exact_445 : required_445 =
    ((Finset.univ.biUnion childrenC_445) ∪ commonEnvelope childrenD_445).erase (3, 0) := by
  exact required_eq_combination childrenC_445 childrenD_445 (3, 0) required_445
    (by decide +kernel) child_required_sub_445 common_sub_445 required_origin_445
theorem envelope_origin_445 : ∀ x ∈ envelope_445,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_445 j := by decide +kernel
theorem envelope_exact_445 : envelope_445 =
    insert (3, 0) (Finset.univ.biUnion childrenD_445) := by
  exact envelope_eq_combination childrenD_445 (3, 0) envelope_445
    pivot_mem_445 child_envelope_sub_445 envelope_origin_445
def checked_445 : CheckedCard where
  required := required_445
  envelope := envelope_445
  height := height_445
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_445
def height_451_i0 : ℕ := 4
def childrenH_451_i0 : Fin 2 → ℕ := ![height_0, height_402]
theorem height_exact_451_i0 : height_451_i0 = 1 + Finset.univ.sup childrenH_451_i0 := by decide +kernel
theorem required_origin_451_i0 : ∀ x ∈ required_451_i0,
    (∃ j, x ∈ childrenC_451_i0 j) ∨ ∀ j, x ∈ childrenD_451_i0 j := by decide +kernel
theorem required_exact_451_i0 : required_451_i0 =
    ((Finset.univ.biUnion childrenC_451_i0) ∪ commonEnvelope childrenD_451_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_451_i0 childrenD_451_i0 (2, 3) required_451_i0
    (by decide +kernel) child_required_sub_451_i0 common_sub_451_i0 required_origin_451_i0
theorem envelope_origin_451_i0 : ∀ x ∈ envelope_451_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_451_i0 j := by decide +kernel
theorem envelope_exact_451_i0 : envelope_451_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_451_i0) := by
  exact envelope_eq_combination childrenD_451_i0 (2, 3) envelope_451_i0
    pivot_mem_451_i0 child_envelope_sub_451_i0 envelope_origin_451_i0
def checked_451_i0 : CheckedCard where
  required := required_451_i0
  envelope := envelope_451_i0
  height := height_451_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_451_i0
def height_451 : ℕ := 5
def childrenH_451 : Fin 2 → ℕ := ![height_11, height_451_i0]
theorem height_exact_451 : height_451 = 1 + Finset.univ.sup childrenH_451 := by decide +kernel
theorem required_origin_451 : ∀ x ∈ required_451,
    (∃ j, x ∈ childrenC_451 j) ∨ ∀ j, x ∈ childrenD_451 j := by decide +kernel
theorem required_exact_451 : required_451 =
    ((Finset.univ.biUnion childrenC_451) ∪ commonEnvelope childrenD_451).erase (1, 4) := by
  exact required_eq_combination childrenC_451 childrenD_451 (1, 4) required_451
    (by decide +kernel) child_required_sub_451 common_sub_451 required_origin_451
theorem envelope_origin_451 : ∀ x ∈ envelope_451,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_451 j := by decide +kernel
theorem envelope_exact_451 : envelope_451 =
    insert (1, 4) (Finset.univ.biUnion childrenD_451) := by
  exact envelope_eq_combination childrenD_451 (1, 4) envelope_451
    pivot_mem_451 child_envelope_sub_451 envelope_origin_451
def checked_451 : CheckedCard where
  required := required_451
  envelope := envelope_451
  height := height_451
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_451
def height_464_i1 : ℕ := 3
def childrenH_464_i1 : Fin 2 → ℕ := ![height_0, height_11]
theorem height_exact_464_i1 : height_464_i1 = 1 + Finset.univ.sup childrenH_464_i1 := by decide +kernel
theorem required_origin_464_i1 : ∀ x ∈ required_464_i1,
    (∃ j, x ∈ childrenC_464_i1 j) ∨ ∀ j, x ∈ childrenD_464_i1 j := by decide +kernel
theorem required_exact_464_i1 : required_464_i1 =
    ((Finset.univ.biUnion childrenC_464_i1) ∪ commonEnvelope childrenD_464_i1).erase (1, 1) := by
  exact required_eq_combination childrenC_464_i1 childrenD_464_i1 (1, 1) required_464_i1
    (by decide +kernel) child_required_sub_464_i1 common_sub_464_i1 required_origin_464_i1
theorem envelope_origin_464_i1 : ∀ x ∈ envelope_464_i1,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_464_i1 j := by decide +kernel
theorem envelope_exact_464_i1 : envelope_464_i1 =
    insert (1, 1) (Finset.univ.biUnion childrenD_464_i1) := by
  exact envelope_eq_combination childrenD_464_i1 (1, 1) envelope_464_i1
    pivot_mem_464_i1 child_envelope_sub_464_i1 envelope_origin_464_i1
def checked_464_i1 : CheckedCard where
  required := required_464_i1
  envelope := envelope_464_i1
  height := height_464_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_464_i1
def height_464_i0 : ℕ := 4
def childrenH_464_i0 : Fin 2 → ℕ := ![height_0, height_464_i1]
theorem height_exact_464_i0 : height_464_i0 = 1 + Finset.univ.sup childrenH_464_i0 := by decide +kernel
theorem required_origin_464_i0 : ∀ x ∈ required_464_i0,
    (∃ j, x ∈ childrenC_464_i0 j) ∨ ∀ j, x ∈ childrenD_464_i0 j := by decide +kernel
theorem required_exact_464_i0 : required_464_i0 =
    ((Finset.univ.biUnion childrenC_464_i0) ∪ commonEnvelope childrenD_464_i0).erase (2, 2) := by
  exact required_eq_combination childrenC_464_i0 childrenD_464_i0 (2, 2) required_464_i0
    (by decide +kernel) child_required_sub_464_i0 common_sub_464_i0 required_origin_464_i0
theorem envelope_origin_464_i0 : ∀ x ∈ envelope_464_i0,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_464_i0 j := by decide +kernel
theorem envelope_exact_464_i0 : envelope_464_i0 =
    insert (2, 2) (Finset.univ.biUnion childrenD_464_i0) := by
  exact envelope_eq_combination childrenD_464_i0 (2, 2) envelope_464_i0
    pivot_mem_464_i0 child_envelope_sub_464_i0 envelope_origin_464_i0
def checked_464_i0 : CheckedCard where
  required := required_464_i0
  envelope := envelope_464_i0
  height := height_464_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_464_i0
def height_464_i2 : ℕ := 4
def childrenH_464_i2 : Fin 2 → ℕ := ![height_29, height_38]
theorem height_exact_464_i2 : height_464_i2 = 1 + Finset.univ.sup childrenH_464_i2 := by decide +kernel
theorem required_origin_464_i2 : ∀ x ∈ required_464_i2,
    (∃ j, x ∈ childrenC_464_i2 j) ∨ ∀ j, x ∈ childrenD_464_i2 j := by decide +kernel
theorem required_exact_464_i2 : required_464_i2 =
    ((Finset.univ.biUnion childrenC_464_i2) ∪ commonEnvelope childrenD_464_i2).erase (1, 5) := by
  exact required_eq_combination childrenC_464_i2 childrenD_464_i2 (1, 5) required_464_i2
    (by decide +kernel) child_required_sub_464_i2 common_sub_464_i2 required_origin_464_i2
theorem envelope_origin_464_i2 : ∀ x ∈ envelope_464_i2,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_464_i2 j := by decide +kernel
theorem envelope_exact_464_i2 : envelope_464_i2 =
    insert (1, 5) (Finset.univ.biUnion childrenD_464_i2) := by
  exact envelope_eq_combination childrenD_464_i2 (1, 5) envelope_464_i2
    pivot_mem_464_i2 child_envelope_sub_464_i2 envelope_origin_464_i2
def checked_464_i2 : CheckedCard where
  required := required_464_i2
  envelope := envelope_464_i2
  height := height_464_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_464_i2
def height_464 : ℕ := 5
def childrenH_464 : Fin 3 → ℕ := ![height_15, height_464_i0, height_464_i2]
theorem height_exact_464 : height_464 = 1 + Finset.univ.sup childrenH_464 := by decide +kernel
theorem required_origin_464 : ∀ x ∈ required_464,
    (∃ j, x ∈ childrenC_464 j) ∨ ∀ j, x ∈ childrenD_464 j := by decide +kernel
theorem required_exact_464 : required_464 =
    ((Finset.univ.biUnion childrenC_464) ∪ commonEnvelope childrenD_464).erase (1, 2) := by
  exact required_eq_combination childrenC_464 childrenD_464 (1, 2) required_464
    (by decide +kernel) child_required_sub_464 common_sub_464 required_origin_464
theorem envelope_origin_464 : ∀ x ∈ envelope_464,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_464 j := by decide +kernel
theorem envelope_exact_464 : envelope_464 =
    insert (1, 2) (Finset.univ.biUnion childrenD_464) := by
  exact envelope_eq_combination childrenD_464 (1, 2) envelope_464
    pivot_mem_464 child_envelope_sub_464 envelope_origin_464
def checked_464 : CheckedCard where
  required := required_464
  envelope := envelope_464
  height := height_464
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_464
def height_492_i1 : ℕ := 3
def childrenH_492_i1 : Fin 2 → ℕ := ![height_0, height_32]
theorem height_exact_492_i1 : height_492_i1 = 1 + Finset.univ.sup childrenH_492_i1 := by decide +kernel
theorem required_origin_492_i1 : ∀ x ∈ required_492_i1,
    (∃ j, x ∈ childrenC_492_i1 j) ∨ ∀ j, x ∈ childrenD_492_i1 j := by decide +kernel
theorem required_exact_492_i1 : required_492_i1 =
    ((Finset.univ.biUnion childrenC_492_i1) ∪ commonEnvelope childrenD_492_i1).erase (2, 3) := by
  exact required_eq_combination childrenC_492_i1 childrenD_492_i1 (2, 3) required_492_i1
    (by decide +kernel) child_required_sub_492_i1 common_sub_492_i1 required_origin_492_i1
theorem envelope_origin_492_i1 : ∀ x ∈ envelope_492_i1,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_492_i1 j := by decide +kernel
theorem envelope_exact_492_i1 : envelope_492_i1 =
    insert (2, 3) (Finset.univ.biUnion childrenD_492_i1) := by
  exact envelope_eq_combination childrenD_492_i1 (2, 3) envelope_492_i1
    pivot_mem_492_i1 child_envelope_sub_492_i1 envelope_origin_492_i1
def checked_492_i1 : CheckedCard where
  required := required_492_i1
  envelope := envelope_492_i1
  height := height_492_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_492_i1
def height_492_i0 : ℕ := 4
def childrenH_492_i0 : Fin 2 → ℕ := ![height_0, height_492_i1]
theorem height_exact_492_i0 : height_492_i0 = 1 + Finset.univ.sup childrenH_492_i0 := by decide +kernel
theorem required_origin_492_i0 : ∀ x ∈ required_492_i0,
    (∃ j, x ∈ childrenC_492_i0 j) ∨ ∀ j, x ∈ childrenD_492_i0 j := by decide +kernel
theorem required_exact_492_i0 : required_492_i0 =
    ((Finset.univ.biUnion childrenC_492_i0) ∪ commonEnvelope childrenD_492_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_492_i0 childrenD_492_i0 (1, 3) required_492_i0
    (by decide +kernel) child_required_sub_492_i0 common_sub_492_i0 required_origin_492_i0
theorem envelope_origin_492_i0 : ∀ x ∈ envelope_492_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_492_i0 j := by decide +kernel
theorem envelope_exact_492_i0 : envelope_492_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_492_i0) := by
  exact envelope_eq_combination childrenD_492_i0 (1, 3) envelope_492_i0
    pivot_mem_492_i0 child_envelope_sub_492_i0 envelope_origin_492_i0
def checked_492_i0 : CheckedCard where
  required := required_492_i0
  envelope := envelope_492_i0
  height := height_492_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_492_i0
def height_492 : ℕ := 5
def childrenH_492 : Fin 2 → ℕ := ![height_78, height_492_i0]
theorem height_exact_492 : height_492 = 1 + Finset.univ.sup childrenH_492 := by decide +kernel
theorem required_origin_492 : ∀ x ∈ required_492,
    (∃ j, x ∈ childrenC_492 j) ∨ ∀ j, x ∈ childrenD_492 j := by decide +kernel
theorem required_exact_492 : required_492 =
    ((Finset.univ.biUnion childrenC_492) ∪ commonEnvelope childrenD_492).erase (1, 2) := by
  exact required_eq_combination childrenC_492 childrenD_492 (1, 2) required_492
    (by decide +kernel) child_required_sub_492 common_sub_492 required_origin_492
theorem envelope_origin_492 : ∀ x ∈ envelope_492,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_492 j := by decide +kernel
theorem envelope_exact_492 : envelope_492 =
    insert (1, 2) (Finset.univ.biUnion childrenD_492) := by
  exact envelope_eq_combination childrenD_492 (1, 2) envelope_492
    pivot_mem_492 child_envelope_sub_492 envelope_origin_492
def checked_492 : CheckedCard where
  required := required_492
  envelope := envelope_492
  height := height_492
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_492
end SnakyPrototype.Certificate21

end OAI
