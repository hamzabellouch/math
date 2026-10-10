import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_512_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_512_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_512_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_69), (placed21 0 (1, 1) required_416)]
def childrenD_512_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_69), (placed21 0 (1, 1) envelope_416)]
theorem common_sub_512_i0 : commonEnvelope childrenD_512_i0 ⊆ insert (3, 3) required_512_i0 := by decide +kernel
theorem child_required_sub_512_i0 : ∀ j, childrenC_512_i0 j ⊆ insert (3, 3) required_512_i0 := by decide +kernel
theorem child_envelope_sub_512_i0 : ∀ j, childrenD_512_i0 j ⊆ envelope_512_i0 := by decide +kernel
theorem pivot_mem_512_i0 : (3, 3) ∈ envelope_512_i0 := by decide +kernel
theorem children_work_512_i0 : ∀ j, Template HasSnaky 5 (childrenC_512_i0 j) (childrenD_512_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_69 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_416 0 (1, 1)).mono (by decide +kernel)
theorem row_works_512_i0 : Template HasSnaky 6 required_512_i0 envelope_512_i0 := by
  refine compose HasSnaky 5 childrenC_512_i0 childrenD_512_i0 children_work_512_i0 (3, 3)
    required_512_i0 envelope_512_i0 pivot_mem_512_i0 child_required_sub_512_i0 child_envelope_sub_512_i0 ?_
  intro b hb
  exact common_sub_512_i0 (mem_commonEnvelope childrenD_512_i0 b hb)
def required_512_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_512_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (3, 4), (4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_512_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_0), (placed21 0 (1, 4) required_5)]
def childrenD_512_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_0), (placed21 0 (1, 4) envelope_5)]
theorem common_sub_512_i3 : commonEnvelope childrenD_512_i3 ⊆ insert (3, 4) required_512_i3 := by decide +kernel
theorem child_required_sub_512_i3 : ∀ j, childrenC_512_i3 j ⊆ insert (3, 4) required_512_i3 := by decide +kernel
theorem child_envelope_sub_512_i3 : ∀ j, childrenD_512_i3 j ⊆ envelope_512_i3 := by decide +kernel
theorem pivot_mem_512_i3 : (3, 4) ∈ envelope_512_i3 := by decide +kernel
theorem children_work_512_i3 : ∀ j, Template HasSnaky 1 (childrenC_512_i3 j) (childrenD_512_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 0 (1, 4)).mono (by decide +kernel)
theorem row_works_512_i3 : Template HasSnaky 2 required_512_i3 envelope_512_i3 := by
  refine compose HasSnaky 1 childrenC_512_i3 childrenD_512_i3 children_work_512_i3 (3, 4)
    required_512_i3 envelope_512_i3 pivot_mem_512_i3 child_required_sub_512_i3 child_envelope_sub_512_i3 ?_
  intro b hb
  exact common_sub_512_i3 (mem_commonEnvelope childrenD_512_i3 b hb)
def required_512_i4 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_512_i4 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_512_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) required_18), (placed21 0 (1, 2) required_382)]
def childrenD_512_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) envelope_18), (placed21 0 (1, 2) envelope_382)]
theorem common_sub_512_i4 : commonEnvelope childrenD_512_i4 ⊆ insert (3, 6) required_512_i4 := by decide +kernel
theorem child_required_sub_512_i4 : ∀ j, childrenC_512_i4 j ⊆ insert (3, 6) required_512_i4 := by decide +kernel
theorem child_envelope_sub_512_i4 : ∀ j, childrenD_512_i4 j ⊆ envelope_512_i4 := by decide +kernel
theorem pivot_mem_512_i4 : (3, 6) ∈ envelope_512_i4 := by decide +kernel
theorem children_work_512_i4 : ∀ j, Template HasSnaky 5 (childrenC_512_i4 j) (childrenD_512_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_382 0 (1, 2)).mono (by decide +kernel)
theorem row_works_512_i4 : Template HasSnaky 6 required_512_i4 envelope_512_i4 := by
  refine compose HasSnaky 5 childrenC_512_i4 childrenD_512_i4 children_work_512_i4 (3, 6)
    required_512_i4 envelope_512_i4 pivot_mem_512_i4 child_required_sub_512_i4 child_envelope_sub_512_i4 ?_
  intro b hb
  exact common_sub_512_i4 (mem_commonEnvelope childrenD_512_i4 b hb)
def required_512_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_512_i2 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_512_i2 : Fin 2 → Finset Cell := ![required_512_i3, required_512_i4]
def childrenD_512_i2 : Fin 2 → Finset Cell := ![envelope_512_i3, envelope_512_i4]
theorem common_sub_512_i2 : commonEnvelope childrenD_512_i2 ⊆ insert (4, 5) required_512_i2 := by decide +kernel
theorem child_required_sub_512_i2 : ∀ j, childrenC_512_i2 j ⊆ insert (4, 5) required_512_i2 := by decide +kernel
theorem child_envelope_sub_512_i2 : ∀ j, childrenD_512_i2 j ⊆ envelope_512_i2 := by decide +kernel
theorem pivot_mem_512_i2 : (4, 5) ∈ envelope_512_i2 := by decide +kernel
theorem children_work_512_i2 : ∀ j, Template HasSnaky 6 (childrenC_512_i2 j) (childrenD_512_i2 j) := by
  intro j
  fin_cases j
  · exact row_works_512_i3.mono (by decide +kernel)
  · exact row_works_512_i4.mono (by decide +kernel)
theorem row_works_512_i2 : Template HasSnaky 7 required_512_i2 envelope_512_i2 := by
  refine compose HasSnaky 6 childrenC_512_i2 childrenD_512_i2 children_work_512_i2 (4, 5)
    required_512_i2 envelope_512_i2 pivot_mem_512_i2 child_required_sub_512_i2 child_envelope_sub_512_i2 ?_
  intro b hb
  exact common_sub_512_i2 (mem_commonEnvelope childrenD_512_i2 b hb)
def required_512_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_512_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_512_i1 : Fin 4 → Finset Cell := ![(placed21 3 (1, 4) required_30), (placed21 4 (1, 7) required_59), (placed21 0 (1, 1) required_511), required_512_i2]
def childrenD_512_i1 : Fin 4 → Finset Cell := ![(placed21 3 (1, 4) envelope_30), (placed21 4 (1, 7) envelope_59), (placed21 0 (1, 1) envelope_511), envelope_512_i2]
theorem common_sub_512_i1 : commonEnvelope childrenD_512_i1 ⊆ insert (4, 4) required_512_i1 := by decide +kernel
theorem child_required_sub_512_i1 : ∀ j, childrenC_512_i1 j ⊆ insert (4, 4) required_512_i1 := by decide +kernel
theorem child_envelope_sub_512_i1 : ∀ j, childrenD_512_i1 j ⊆ envelope_512_i1 := by decide +kernel
theorem pivot_mem_512_i1 : (4, 4) ∈ envelope_512_i1 := by decide +kernel
theorem children_work_512_i1 : ∀ j, Template HasSnaky 7 (childrenC_512_i1 j) (childrenD_512_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_59 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_511 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_512_i2.mono (by decide +kernel)
theorem row_works_512_i1 : Template HasSnaky 8 required_512_i1 envelope_512_i1 := by
  refine compose HasSnaky 7 childrenC_512_i1 childrenD_512_i1 children_work_512_i1 (4, 4)
    required_512_i1 envelope_512_i1 pivot_mem_512_i1 child_required_sub_512_i1 child_envelope_sub_512_i1 ?_
  intro b hb
  exact common_sub_512_i1 (mem_commonEnvelope childrenD_512_i1 b hb)
def required_512 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_512 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_512 : Fin 4 → Finset Cell := ![(placed21 1 (1, 3) required_74), (placed21 0 (0, 1) required_108), required_512_i0, required_512_i1]
def childrenD_512 : Fin 4 → Finset Cell := ![(placed21 1 (1, 3) envelope_74), (placed21 0 (0, 1) envelope_108), envelope_512_i0, envelope_512_i1]
theorem common_sub_512 : commonEnvelope childrenD_512 ⊆ insert (4, 3) required_512 := by decide +kernel
theorem child_required_sub_512 : ∀ j, childrenC_512 j ⊆ insert (4, 3) required_512 := by decide +kernel
theorem child_envelope_sub_512 : ∀ j, childrenD_512 j ⊆ envelope_512 := by decide +kernel
theorem pivot_mem_512 : (4, 3) ∈ envelope_512 := by decide +kernel
theorem children_work_512 : ∀ j, Template HasSnaky 8 (childrenC_512 j) (childrenD_512 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_74 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_108 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_512_i0.mono (by decide +kernel)
  · exact row_works_512_i1.mono (by decide +kernel)
theorem row_works_512 : Template HasSnaky 9 required_512 envelope_512 := by
  refine compose HasSnaky 8 childrenC_512 childrenD_512 children_work_512 (4, 3)
    required_512 envelope_512 pivot_mem_512 child_required_sub_512 child_envelope_sub_512 ?_
  intro b hb
  exact common_sub_512 (mem_commonEnvelope childrenD_512 b hb)
def required_514 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_514 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_514 : Fin 3 → Finset Cell := ![(placed21 7 (5, 2) required_34), (placed21 5 (5, 1) required_149), required_513]
def childrenD_514 : Fin 3 → Finset Cell := ![(placed21 7 (5, 2) envelope_34), (placed21 5 (5, 1) envelope_149), envelope_513]
theorem common_sub_514 : commonEnvelope childrenD_514 ⊆ insert (3, 2) required_514 := by decide +kernel
theorem child_required_sub_514 : ∀ j, childrenC_514 j ⊆ insert (3, 2) required_514 := by decide +kernel
theorem child_envelope_sub_514 : ∀ j, childrenD_514 j ⊆ envelope_514 := by decide +kernel
theorem pivot_mem_514 : (3, 2) ∈ envelope_514 := by decide +kernel
theorem children_work_514 : ∀ j, Template HasSnaky 8 (childrenC_514 j) (childrenD_514 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 7 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_149 5 (5, 1)).mono (by decide +kernel)
  · exact row_works_513.mono (by decide +kernel)
theorem row_works_514 : Template HasSnaky 9 required_514 envelope_514 := by
  refine compose HasSnaky 8 childrenC_514 childrenD_514 children_work_514 (3, 2)
    required_514 envelope_514 pivot_mem_514 child_required_sub_514 child_envelope_sub_514 ?_
  intro b hb
  exact common_sub_514 (mem_commonEnvelope childrenD_514 b hb)
def required_519 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_519 : Finset Cell := ⟨(([(0, 6), (1, 3), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 5), (6, 2), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_519 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) required_10), (placed21 3 (1, 6) required_47), (placed21 6 (3, 6) required_52), (placed21 2 (6, 0) required_518)]
def childrenD_519 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) envelope_10), (placed21 3 (1, 6) envelope_47), (placed21 6 (3, 6) envelope_52), (placed21 2 (6, 0) envelope_518)]
theorem common_sub_519 : commonEnvelope childrenD_519 ⊆ insert (3, 5) required_519 := by decide +kernel
theorem child_required_sub_519 : ∀ j, childrenC_519 j ⊆ insert (3, 5) required_519 := by decide +kernel
theorem child_envelope_sub_519 : ∀ j, childrenD_519 j ⊆ envelope_519 := by decide +kernel
theorem pivot_mem_519 : (3, 5) ∈ envelope_519 := by decide +kernel
theorem children_work_519 : ∀ j, Template HasSnaky 8 (childrenC_519 j) (childrenD_519 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_518 2 (6, 0)).mono (by decide +kernel)
theorem row_works_519 : Template HasSnaky 9 required_519 envelope_519 := by
  refine compose HasSnaky 8 childrenC_519 childrenD_519 children_work_519 (3, 5)
    required_519 envelope_519 pivot_mem_519 child_required_sub_519 child_envelope_sub_519 ?_
  intro b hb
  exact common_sub_519 (mem_commonEnvelope childrenD_519 b hb)
def required_528_i0 : Finset Cell := ⟨(([(0, 7), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_528_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_528_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 3) required_4), (placed21 7 (2, 6) required_49)]
def childrenD_528_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 3) envelope_4), (placed21 7 (2, 6) envelope_49)]
theorem common_sub_528_i0 : commonEnvelope childrenD_528_i0 ⊆ insert (1, 3) required_528_i0 := by decide +kernel
theorem child_required_sub_528_i0 : ∀ j, childrenC_528_i0 j ⊆ insert (1, 3) required_528_i0 := by decide +kernel
theorem child_envelope_sub_528_i0 : ∀ j, childrenD_528_i0 j ⊆ envelope_528_i0 := by decide +kernel
theorem pivot_mem_528_i0 : (1, 3) ∈ envelope_528_i0 := by decide +kernel
theorem children_work_528_i0 : ∀ j, Template HasSnaky 4 (childrenC_528_i0 j) (childrenD_528_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 5 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 7 (2, 6)).mono (by decide +kernel)
theorem row_works_528_i0 : Template HasSnaky 5 required_528_i0 envelope_528_i0 := by
  refine compose HasSnaky 4 childrenC_528_i0 childrenD_528_i0 children_work_528_i0 (1, 3)
    required_528_i0 envelope_528_i0 pivot_mem_528_i0 child_required_sub_528_i0 child_envelope_sub_528_i0 ?_
  intro b hb
  exact common_sub_528_i0 (mem_commonEnvelope childrenD_528_i0 b hb)
def required_528_i1 : Finset Cell := ⟨(([(0, 4), (0, 7), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_528_i1 : Finset Cell := ⟨(([(0, 4), (0, 7), (0, 8), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_528_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 4) required_5), (placed21 0 (0, 1) required_446)]
def childrenD_528_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 4) envelope_5), (placed21 0 (0, 1) envelope_446)]
theorem common_sub_528_i1 : commonEnvelope childrenD_528_i1 ⊆ insert (1, 7) required_528_i1 := by decide +kernel
theorem child_required_sub_528_i1 : ∀ j, childrenC_528_i1 j ⊆ insert (1, 7) required_528_i1 := by decide +kernel
theorem child_envelope_sub_528_i1 : ∀ j, childrenD_528_i1 j ⊆ envelope_528_i1 := by decide +kernel
theorem pivot_mem_528_i1 : (1, 7) ∈ envelope_528_i1 := by decide +kernel
theorem children_work_528_i1 : ∀ j, Template HasSnaky 7 (childrenC_528_i1 j) (childrenD_528_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_446 0 (0, 1)).mono (by decide +kernel)
theorem row_works_528_i1 : Template HasSnaky 8 required_528_i1 envelope_528_i1 := by
  refine compose HasSnaky 7 childrenC_528_i1 childrenD_528_i1 children_work_528_i1 (1, 7)
    required_528_i1 envelope_528_i1 pivot_mem_528_i1 child_required_sub_528_i1 child_envelope_sub_528_i1 ?_
  intro b hb
  exact common_sub_528_i1 (mem_commonEnvelope childrenD_528_i1 b hb)
def required_528 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_528 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 6), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_528 : Fin 3 → Finset Cell := ![(placed21 2 (1, 3) required_61), required_528_i0, required_528_i1]
def childrenD_528 : Fin 3 → Finset Cell := ![(placed21 2 (1, 3) envelope_61), envelope_528_i0, envelope_528_i1]
theorem common_sub_528 : commonEnvelope childrenD_528 ⊆ insert (0, 7) required_528 := by decide +kernel
theorem child_required_sub_528 : ∀ j, childrenC_528 j ⊆ insert (0, 7) required_528 := by decide +kernel
theorem child_envelope_sub_528 : ∀ j, childrenD_528 j ⊆ envelope_528 := by decide +kernel
theorem pivot_mem_528 : (0, 7) ∈ envelope_528 := by decide +kernel
theorem children_work_528 : ∀ j, Template HasSnaky 8 (childrenC_528 j) (childrenD_528 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_61 2 (1, 3)).mono (by decide +kernel)
  · exact row_works_528_i0.mono (by decide +kernel)
  · exact row_works_528_i1.mono (by decide +kernel)
theorem row_works_528 : Template HasSnaky 9 required_528 envelope_528 := by
  refine compose HasSnaky 8 childrenC_528 childrenD_528 children_work_528 (0, 7)
    required_528 envelope_528 pivot_mem_528 child_required_sub_528 child_envelope_sub_528 ?_
  intro b hb
  exact common_sub_528 (mem_commonEnvelope childrenD_528 b hb)
def required_531 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_531 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_531 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), required_530]
def childrenD_531 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), envelope_530]
theorem common_sub_531 : commonEnvelope childrenD_531 ⊆ insert (1, 4) required_531 := by decide +kernel
theorem child_required_sub_531 : ∀ j, childrenC_531 j ⊆ insert (1, 4) required_531 := by decide +kernel
theorem child_envelope_sub_531 : ∀ j, childrenD_531 j ⊆ envelope_531 := by decide +kernel
theorem pivot_mem_531 : (1, 4) ∈ envelope_531 := by decide +kernel
theorem children_work_531 : ∀ j, Template HasSnaky 8 (childrenC_531 j) (childrenD_531 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact row_works_530.mono (by decide +kernel)
theorem row_works_531 : Template HasSnaky 9 required_531 envelope_531 := by
  refine compose HasSnaky 8 childrenC_531 childrenD_531 children_work_531 (1, 4)
    required_531 envelope_531 pivot_mem_531 child_required_sub_531 child_envelope_sub_531 ?_
  intro b hb
  exact common_sub_531 (mem_commonEnvelope childrenD_531 b hb)
def required_536 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_536 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_536 : Fin 4 → Finset Cell := ![(placed21 2 (4, 1) required_14), (placed21 7 (6, 6) required_88), (placed21 5 (6, 2) required_213), (placed21 3 (0, 6) required_534)]
def childrenD_536 : Fin 4 → Finset Cell := ![(placed21 2 (4, 1) envelope_14), (placed21 7 (6, 6) envelope_88), (placed21 5 (6, 2) envelope_213), (placed21 3 (0, 6) envelope_534)]
theorem common_sub_536 : commonEnvelope childrenD_536 ⊆ insert (3, 5) required_536 := by decide +kernel
theorem child_required_sub_536 : ∀ j, childrenC_536 j ⊆ insert (3, 5) required_536 := by decide +kernel
theorem child_envelope_sub_536 : ∀ j, childrenD_536 j ⊆ envelope_536 := by decide +kernel
theorem pivot_mem_536 : (3, 5) ∈ envelope_536 := by decide +kernel
theorem children_work_536 : ∀ j, Template HasSnaky 8 (childrenC_536 j) (childrenD_536 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_88 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_213 5 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_534 3 (0, 6)).mono (by decide +kernel)
theorem row_works_536 : Template HasSnaky 9 required_536 envelope_536 := by
  refine compose HasSnaky 8 childrenC_536 childrenD_536 children_work_536 (3, 5)
    required_536 envelope_536 pivot_mem_536 child_required_sub_536 child_envelope_sub_536 ?_
  intro b hb
  exact common_sub_536 (mem_commonEnvelope childrenD_536 b hb)
def required_537_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537_i0 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) required_45), (placed21 0 (1, 2) required_418)]
def childrenD_537_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) envelope_45), (placed21 0 (1, 2) envelope_418)]
theorem common_sub_537_i0 : commonEnvelope childrenD_537_i0 ⊆ insert (3, 3) required_537_i0 := by decide +kernel
theorem child_required_sub_537_i0 : ∀ j, childrenC_537_i0 j ⊆ insert (3, 3) required_537_i0 := by decide +kernel
theorem child_envelope_sub_537_i0 : ∀ j, childrenD_537_i0 j ⊆ envelope_537_i0 := by decide +kernel
theorem pivot_mem_537_i0 : (3, 3) ∈ envelope_537_i0 := by decide +kernel
theorem children_work_537_i0 : ∀ j, Template HasSnaky 7 (childrenC_537_i0 j) (childrenD_537_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_45 6 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_418 0 (1, 2)).mono (by decide +kernel)
theorem row_works_537_i0 : Template HasSnaky 8 required_537_i0 envelope_537_i0 := by
  refine compose HasSnaky 7 childrenC_537_i0 childrenD_537_i0 children_work_537_i0 (3, 3)
    required_537_i0 envelope_537_i0 pivot_mem_537_i0 child_required_sub_537_i0 child_envelope_sub_537_i0 ?_
  intro b hb
  exact common_sub_537_i0 (mem_commonEnvelope childrenD_537_i0 b hb)
def required_537_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537_i2 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537_i2 : Fin 2 → Finset Cell := ![(placed21 6 (2, 6) required_15), (placed21 0 (1, 2) required_425)]
def childrenD_537_i2 : Fin 2 → Finset Cell := ![(placed21 6 (2, 6) envelope_15), (placed21 0 (1, 2) envelope_425)]
theorem common_sub_537_i2 : commonEnvelope childrenD_537_i2 ⊆ insert (2, 5) required_537_i2 := by decide +kernel
theorem child_required_sub_537_i2 : ∀ j, childrenC_537_i2 j ⊆ insert (2, 5) required_537_i2 := by decide +kernel
theorem child_envelope_sub_537_i2 : ∀ j, childrenD_537_i2 j ⊆ envelope_537_i2 := by decide +kernel
theorem pivot_mem_537_i2 : (2, 5) ∈ envelope_537_i2 := by decide +kernel
theorem children_work_537_i2 : ∀ j, Template HasSnaky 5 (childrenC_537_i2 j) (childrenD_537_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_425 0 (1, 2)).mono (by decide +kernel)
theorem row_works_537_i2 : Template HasSnaky 6 required_537_i2 envelope_537_i2 := by
  refine compose HasSnaky 5 childrenC_537_i2 childrenD_537_i2 children_work_537_i2 (2, 5)
    required_537_i2 envelope_537_i2 pivot_mem_537_i2 child_required_sub_537_i2 child_envelope_sub_537_i2 ?_
  intro b hb
  exact common_sub_537_i2 (mem_commonEnvelope childrenD_537_i2 b hb)
def required_537_i6 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537_i6 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537_i6 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) required_0), (placed21 2 (2, 2) required_23)]
def childrenD_537_i6 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) envelope_0), (placed21 2 (2, 2) envelope_23)]
theorem common_sub_537_i6 : commonEnvelope childrenD_537_i6 ⊆ insert (2, 5) required_537_i6 := by decide +kernel
theorem child_required_sub_537_i6 : ∀ j, childrenC_537_i6 j ⊆ insert (2, 5) required_537_i6 := by decide +kernel
theorem child_envelope_sub_537_i6 : ∀ j, childrenD_537_i6 j ⊆ envelope_537_i6 := by decide +kernel
theorem pivot_mem_537_i6 : (2, 5) ∈ envelope_537_i6 := by decide +kernel
theorem children_work_537_i6 : ∀ j, Template HasSnaky 2 (childrenC_537_i6 j) (childrenD_537_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_23 2 (2, 2)).mono (by decide +kernel)
theorem row_works_537_i6 : Template HasSnaky 3 required_537_i6 envelope_537_i6 := by
  refine compose HasSnaky 2 childrenC_537_i6 childrenD_537_i6 children_work_537_i6 (2, 5)
    required_537_i6 envelope_537_i6 pivot_mem_537_i6 child_required_sub_537_i6 child_envelope_sub_537_i6 ?_
  intro b hb
  exact common_sub_537_i6 (mem_commonEnvelope childrenD_537_i6 b hb)
def required_537_i5 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (3, 6), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537_i5 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 2) required_0), required_537_i6]
def childrenD_537_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 2) envelope_0), envelope_537_i6]
theorem common_sub_537_i5 : commonEnvelope childrenD_537_i5 ⊆ insert (3, 5) required_537_i5 := by decide +kernel
theorem child_required_sub_537_i5 : ∀ j, childrenC_537_i5 j ⊆ insert (3, 5) required_537_i5 := by decide +kernel
theorem child_envelope_sub_537_i5 : ∀ j, childrenD_537_i5 j ⊆ envelope_537_i5 := by decide +kernel
theorem pivot_mem_537_i5 : (3, 5) ∈ envelope_537_i5 := by decide +kernel
theorem children_work_537_i5 : ∀ j, Template HasSnaky 3 (childrenC_537_i5 j) (childrenD_537_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 5 (4, 2)).mono (by decide +kernel)
  · exact row_works_537_i6.mono (by decide +kernel)
theorem row_works_537_i5 : Template HasSnaky 4 required_537_i5 envelope_537_i5 := by
  refine compose HasSnaky 3 childrenC_537_i5 childrenD_537_i5 children_work_537_i5 (3, 5)
    required_537_i5 envelope_537_i5 pivot_mem_537_i5 child_required_sub_537_i5 child_envelope_sub_537_i5 ?_
  intro b hb
  exact common_sub_537_i5 (mem_commonEnvelope childrenD_537_i5 b hb)
def required_537_i4 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537_i4 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 6), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537_i4 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) required_139), (placed21 0 (1, 2) required_382), required_537_i5]
def childrenD_537_i4 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) envelope_139), (placed21 0 (1, 2) envelope_382), envelope_537_i5]
theorem common_sub_537_i4 : commonEnvelope childrenD_537_i4 ⊆ insert (3, 6) required_537_i4 := by decide +kernel
theorem child_required_sub_537_i4 : ∀ j, childrenC_537_i4 j ⊆ insert (3, 6) required_537_i4 := by decide +kernel
theorem child_envelope_sub_537_i4 : ∀ j, childrenD_537_i4 j ⊆ envelope_537_i4 := by decide +kernel
theorem pivot_mem_537_i4 : (3, 6) ∈ envelope_537_i4 := by decide +kernel
theorem children_work_537_i4 : ∀ j, Template HasSnaky 5 (childrenC_537_i4 j) (childrenD_537_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_139 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_382 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_537_i5.mono (by decide +kernel)
theorem row_works_537_i4 : Template HasSnaky 6 required_537_i4 envelope_537_i4 := by
  refine compose HasSnaky 5 childrenC_537_i4 childrenD_537_i4 children_work_537_i4 (3, 6)
    required_537_i4 envelope_537_i4 pivot_mem_537_i4 child_required_sub_537_i4 child_envelope_sub_537_i4 ?_
  intro b hb
  exact common_sub_537_i4 (mem_commonEnvelope childrenD_537_i4 b hb)
def required_537_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537_i3 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 6), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537_i3 : Fin 3 → Finset Cell := ![(placed21 2 (5, 1) required_13), (placed21 3 (1, 4) required_30), required_537_i4]
def childrenD_537_i3 : Fin 3 → Finset Cell := ![(placed21 2 (5, 1) envelope_13), (placed21 3 (1, 4) envelope_30), envelope_537_i4]
theorem common_sub_537_i3 : commonEnvelope childrenD_537_i3 ⊆ insert (4, 4) required_537_i3 := by decide +kernel
theorem child_required_sub_537_i3 : ∀ j, childrenC_537_i3 j ⊆ insert (4, 4) required_537_i3 := by decide +kernel
theorem child_envelope_sub_537_i3 : ∀ j, childrenD_537_i3 j ⊆ envelope_537_i3 := by decide +kernel
theorem pivot_mem_537_i3 : (4, 4) ∈ envelope_537_i3 := by decide +kernel
theorem children_work_537_i3 : ∀ j, Template HasSnaky 6 (childrenC_537_i3 j) (childrenD_537_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_30 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_537_i4.mono (by decide +kernel)
theorem row_works_537_i3 : Template HasSnaky 7 required_537_i3 envelope_537_i3 := by
  refine compose HasSnaky 6 childrenC_537_i3 childrenD_537_i3 children_work_537_i3 (4, 4)
    required_537_i3 envelope_537_i3 pivot_mem_537_i3 child_required_sub_537_i3 child_envelope_sub_537_i3 ?_
  intro b hb
  exact common_sub_537_i3 (mem_commonEnvelope childrenD_537_i3 b hb)
def required_537_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537_i1 : Finset Cell := ⟨(([(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537_i1 : Fin 4 → Finset Cell := ![(placed21 0 (1, 1) required_166), (placed21 4 (1, 7) required_464), required_537_i2, required_537_i3]
def childrenD_537_i1 : Fin 4 → Finset Cell := ![(placed21 0 (1, 1) envelope_166), (placed21 4 (1, 7) envelope_464), envelope_537_i2, envelope_537_i3]
theorem common_sub_537_i1 : commonEnvelope childrenD_537_i1 ⊆ insert (4, 5) required_537_i1 := by decide +kernel
theorem child_required_sub_537_i1 : ∀ j, childrenC_537_i1 j ⊆ insert (4, 5) required_537_i1 := by decide +kernel
theorem child_envelope_sub_537_i1 : ∀ j, childrenD_537_i1 j ⊆ envelope_537_i1 := by decide +kernel
theorem pivot_mem_537_i1 : (4, 5) ∈ envelope_537_i1 := by decide +kernel
theorem children_work_537_i1 : ∀ j, Template HasSnaky 7 (childrenC_537_i1 j) (childrenD_537_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_166 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_464 4 (1, 7)).mono (by decide +kernel)
  · exact row_works_537_i2.mono (by decide +kernel)
  · exact row_works_537_i3.mono (by decide +kernel)
theorem row_works_537_i1 : Template HasSnaky 8 required_537_i1 envelope_537_i1 := by
  refine compose HasSnaky 7 childrenC_537_i1 childrenD_537_i1 children_work_537_i1 (4, 5)
    required_537_i1 envelope_537_i1 pivot_mem_537_i1 child_required_sub_537_i1 child_envelope_sub_537_i1 ?_
  intro b hb
  exact common_sub_537_i1 (mem_commonEnvelope childrenD_537_i1 b hb)
def required_537 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_537 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_537 : Fin 4 → Finset Cell := ![(placed21 1 (1, 3) required_74), (placed21 0 (0, 1) required_108), required_537_i0, required_537_i1]
def childrenD_537 : Fin 4 → Finset Cell := ![(placed21 1 (1, 3) envelope_74), (placed21 0 (0, 1) envelope_108), envelope_537_i0, envelope_537_i1]
theorem common_sub_537 : commonEnvelope childrenD_537 ⊆ insert (4, 3) required_537 := by decide +kernel
theorem child_required_sub_537 : ∀ j, childrenC_537 j ⊆ insert (4, 3) required_537 := by decide +kernel
theorem child_envelope_sub_537 : ∀ j, childrenD_537 j ⊆ envelope_537 := by decide +kernel
theorem pivot_mem_537 : (4, 3) ∈ envelope_537 := by decide +kernel
theorem children_work_537 : ∀ j, Template HasSnaky 8 (childrenC_537 j) (childrenD_537 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_74 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_108 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_537_i0.mono (by decide +kernel)
  · exact row_works_537_i1.mono (by decide +kernel)
theorem row_works_537 : Template HasSnaky 9 required_537 envelope_537 := by
  refine compose HasSnaky 8 childrenC_537 childrenD_537 children_work_537 (4, 3)
    required_537 envelope_537 pivot_mem_537 child_required_sub_537 child_envelope_sub_537 ?_
  intro b hb
  exact common_sub_537 (mem_commonEnvelope childrenD_537 b hb)
def height_512_i0 : ℕ := 6
def childrenH_512_i0 : Fin 2 → ℕ := ![height_69, height_416]
theorem height_exact_512_i0 : height_512_i0 = 1 + Finset.univ.sup childrenH_512_i0 := by decide +kernel
theorem required_origin_512_i0 : ∀ x ∈ required_512_i0,
    (∃ j, x ∈ childrenC_512_i0 j) ∨ ∀ j, x ∈ childrenD_512_i0 j := by decide +kernel
theorem required_exact_512_i0 : required_512_i0 =
    ((Finset.univ.biUnion childrenC_512_i0) ∪ commonEnvelope childrenD_512_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_512_i0 childrenD_512_i0 (3, 3) required_512_i0
    (by decide +kernel) child_required_sub_512_i0 common_sub_512_i0 required_origin_512_i0
theorem envelope_origin_512_i0 : ∀ x ∈ envelope_512_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_512_i0 j := by decide +kernel
theorem envelope_exact_512_i0 : envelope_512_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_512_i0) := by
  exact envelope_eq_combination childrenD_512_i0 (3, 3) envelope_512_i0
    pivot_mem_512_i0 child_envelope_sub_512_i0 envelope_origin_512_i0
def checked_512_i0 : CheckedCard where
  required := required_512_i0
  envelope := envelope_512_i0
  height := height_512_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_512_i0
def height_512_i3 : ℕ := 2
def childrenH_512_i3 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_512_i3 : height_512_i3 = 1 + Finset.univ.sup childrenH_512_i3 := by decide +kernel
theorem required_origin_512_i3 : ∀ x ∈ required_512_i3,
    (∃ j, x ∈ childrenC_512_i3 j) ∨ ∀ j, x ∈ childrenD_512_i3 j := by decide +kernel
theorem required_exact_512_i3 : required_512_i3 =
    ((Finset.univ.biUnion childrenC_512_i3) ∪ commonEnvelope childrenD_512_i3).erase (3, 4) := by
  exact required_eq_combination childrenC_512_i3 childrenD_512_i3 (3, 4) required_512_i3
    (by decide +kernel) child_required_sub_512_i3 common_sub_512_i3 required_origin_512_i3
theorem envelope_origin_512_i3 : ∀ x ∈ envelope_512_i3,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_512_i3 j := by decide +kernel
theorem envelope_exact_512_i3 : envelope_512_i3 =
    insert (3, 4) (Finset.univ.biUnion childrenD_512_i3) := by
  exact envelope_eq_combination childrenD_512_i3 (3, 4) envelope_512_i3
    pivot_mem_512_i3 child_envelope_sub_512_i3 envelope_origin_512_i3
def checked_512_i3 : CheckedCard where
  required := required_512_i3
  envelope := envelope_512_i3
  height := height_512_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_512_i3
def height_512_i4 : ℕ := 6
def childrenH_512_i4 : Fin 2 → ℕ := ![height_18, height_382]
theorem height_exact_512_i4 : height_512_i4 = 1 + Finset.univ.sup childrenH_512_i4 := by decide +kernel
theorem required_origin_512_i4 : ∀ x ∈ required_512_i4,
    (∃ j, x ∈ childrenC_512_i4 j) ∨ ∀ j, x ∈ childrenD_512_i4 j := by decide +kernel
theorem required_exact_512_i4 : required_512_i4 =
    ((Finset.univ.biUnion childrenC_512_i4) ∪ commonEnvelope childrenD_512_i4).erase (3, 6) := by
  exact required_eq_combination childrenC_512_i4 childrenD_512_i4 (3, 6) required_512_i4
    (by decide +kernel) child_required_sub_512_i4 common_sub_512_i4 required_origin_512_i4
theorem envelope_origin_512_i4 : ∀ x ∈ envelope_512_i4,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_512_i4 j := by decide +kernel
theorem envelope_exact_512_i4 : envelope_512_i4 =
    insert (3, 6) (Finset.univ.biUnion childrenD_512_i4) := by
  exact envelope_eq_combination childrenD_512_i4 (3, 6) envelope_512_i4
    pivot_mem_512_i4 child_envelope_sub_512_i4 envelope_origin_512_i4
def checked_512_i4 : CheckedCard where
  required := required_512_i4
  envelope := envelope_512_i4
  height := height_512_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_512_i4
def height_512_i2 : ℕ := 7
def childrenH_512_i2 : Fin 2 → ℕ := ![height_512_i3, height_512_i4]
theorem height_exact_512_i2 : height_512_i2 = 1 + Finset.univ.sup childrenH_512_i2 := by decide +kernel
theorem required_origin_512_i2 : ∀ x ∈ required_512_i2,
    (∃ j, x ∈ childrenC_512_i2 j) ∨ ∀ j, x ∈ childrenD_512_i2 j := by decide +kernel
theorem required_exact_512_i2 : required_512_i2 =
    ((Finset.univ.biUnion childrenC_512_i2) ∪ commonEnvelope childrenD_512_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_512_i2 childrenD_512_i2 (4, 5) required_512_i2
    (by decide +kernel) child_required_sub_512_i2 common_sub_512_i2 required_origin_512_i2
theorem envelope_origin_512_i2 : ∀ x ∈ envelope_512_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_512_i2 j := by decide +kernel
theorem envelope_exact_512_i2 : envelope_512_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_512_i2) := by
  exact envelope_eq_combination childrenD_512_i2 (4, 5) envelope_512_i2
    pivot_mem_512_i2 child_envelope_sub_512_i2 envelope_origin_512_i2
def checked_512_i2 : CheckedCard where
  required := required_512_i2
  envelope := envelope_512_i2
  height := height_512_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_512_i2
def height_512_i1 : ℕ := 8
def childrenH_512_i1 : Fin 4 → ℕ := ![height_30, height_59, height_511, height_512_i2]
theorem height_exact_512_i1 : height_512_i1 = 1 + Finset.univ.sup childrenH_512_i1 := by decide +kernel
theorem required_origin_512_i1 : ∀ x ∈ required_512_i1,
    (∃ j, x ∈ childrenC_512_i1 j) ∨ ∀ j, x ∈ childrenD_512_i1 j := by decide +kernel
theorem required_exact_512_i1 : required_512_i1 =
    ((Finset.univ.biUnion childrenC_512_i1) ∪ commonEnvelope childrenD_512_i1).erase (4, 4) := by
  exact required_eq_combination childrenC_512_i1 childrenD_512_i1 (4, 4) required_512_i1
    (by decide +kernel) child_required_sub_512_i1 common_sub_512_i1 required_origin_512_i1
theorem envelope_origin_512_i1 : ∀ x ∈ envelope_512_i1,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_512_i1 j := by decide +kernel
theorem envelope_exact_512_i1 : envelope_512_i1 =
    insert (4, 4) (Finset.univ.biUnion childrenD_512_i1) := by
  exact envelope_eq_combination childrenD_512_i1 (4, 4) envelope_512_i1
    pivot_mem_512_i1 child_envelope_sub_512_i1 envelope_origin_512_i1
def checked_512_i1 : CheckedCard where
  required := required_512_i1
  envelope := envelope_512_i1
  height := height_512_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_512_i1
def height_512 : ℕ := 9
def childrenH_512 : Fin 4 → ℕ := ![height_74, height_108, height_512_i0, height_512_i1]
theorem height_exact_512 : height_512 = 1 + Finset.univ.sup childrenH_512 := by decide +kernel
theorem required_origin_512 : ∀ x ∈ required_512,
    (∃ j, x ∈ childrenC_512 j) ∨ ∀ j, x ∈ childrenD_512 j := by decide +kernel
theorem required_exact_512 : required_512 =
    ((Finset.univ.biUnion childrenC_512) ∪ commonEnvelope childrenD_512).erase (4, 3) := by
  exact required_eq_combination childrenC_512 childrenD_512 (4, 3) required_512
    (by decide +kernel) child_required_sub_512 common_sub_512 required_origin_512
theorem envelope_origin_512 : ∀ x ∈ envelope_512,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_512 j := by decide +kernel
theorem envelope_exact_512 : envelope_512 =
    insert (4, 3) (Finset.univ.biUnion childrenD_512) := by
  exact envelope_eq_combination childrenD_512 (4, 3) envelope_512
    pivot_mem_512 child_envelope_sub_512 envelope_origin_512
def checked_512 : CheckedCard where
  required := required_512
  envelope := envelope_512
  height := height_512
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_512
def height_514 : ℕ := 9
def childrenH_514 : Fin 3 → ℕ := ![height_34, height_149, height_513]
theorem height_exact_514 : height_514 = 1 + Finset.univ.sup childrenH_514 := by decide +kernel
theorem required_origin_514 : ∀ x ∈ required_514,
    (∃ j, x ∈ childrenC_514 j) ∨ ∀ j, x ∈ childrenD_514 j := by decide +kernel
theorem required_exact_514 : required_514 =
    ((Finset.univ.biUnion childrenC_514) ∪ commonEnvelope childrenD_514).erase (3, 2) := by
  exact required_eq_combination childrenC_514 childrenD_514 (3, 2) required_514
    (by decide +kernel) child_required_sub_514 common_sub_514 required_origin_514
theorem envelope_origin_514 : ∀ x ∈ envelope_514,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_514 j := by decide +kernel
theorem envelope_exact_514 : envelope_514 =
    insert (3, 2) (Finset.univ.biUnion childrenD_514) := by
  exact envelope_eq_combination childrenD_514 (3, 2) envelope_514
    pivot_mem_514 child_envelope_sub_514 envelope_origin_514
def checked_514 : CheckedCard where
  required := required_514
  envelope := envelope_514
  height := height_514
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_514
def height_519 : ℕ := 9
def childrenH_519 : Fin 4 → ℕ := ![height_10, height_47, height_52, height_518]
theorem height_exact_519 : height_519 = 1 + Finset.univ.sup childrenH_519 := by decide +kernel
theorem required_origin_519 : ∀ x ∈ required_519,
    (∃ j, x ∈ childrenC_519 j) ∨ ∀ j, x ∈ childrenD_519 j := by decide +kernel
theorem required_exact_519 : required_519 =
    ((Finset.univ.biUnion childrenC_519) ∪ commonEnvelope childrenD_519).erase (3, 5) := by
  exact required_eq_combination childrenC_519 childrenD_519 (3, 5) required_519
    (by decide +kernel) child_required_sub_519 common_sub_519 required_origin_519
theorem envelope_origin_519 : ∀ x ∈ envelope_519,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_519 j := by decide +kernel
theorem envelope_exact_519 : envelope_519 =
    insert (3, 5) (Finset.univ.biUnion childrenD_519) := by
  exact envelope_eq_combination childrenD_519 (3, 5) envelope_519
    pivot_mem_519 child_envelope_sub_519 envelope_origin_519
def checked_519 : CheckedCard where
  required := required_519
  envelope := envelope_519
  height := height_519
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_519
def height_528_i0 : ℕ := 5
def childrenH_528_i0 : Fin 2 → ℕ := ![height_4, height_49]
theorem height_exact_528_i0 : height_528_i0 = 1 + Finset.univ.sup childrenH_528_i0 := by decide +kernel
theorem required_origin_528_i0 : ∀ x ∈ required_528_i0,
    (∃ j, x ∈ childrenC_528_i0 j) ∨ ∀ j, x ∈ childrenD_528_i0 j := by decide +kernel
theorem required_exact_528_i0 : required_528_i0 =
    ((Finset.univ.biUnion childrenC_528_i0) ∪ commonEnvelope childrenD_528_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_528_i0 childrenD_528_i0 (1, 3) required_528_i0
    (by decide +kernel) child_required_sub_528_i0 common_sub_528_i0 required_origin_528_i0
theorem envelope_origin_528_i0 : ∀ x ∈ envelope_528_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_528_i0 j := by decide +kernel
theorem envelope_exact_528_i0 : envelope_528_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_528_i0) := by
  exact envelope_eq_combination childrenD_528_i0 (1, 3) envelope_528_i0
    pivot_mem_528_i0 child_envelope_sub_528_i0 envelope_origin_528_i0
def checked_528_i0 : CheckedCard where
  required := required_528_i0
  envelope := envelope_528_i0
  height := height_528_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_528_i0
def height_528_i1 : ℕ := 8
def childrenH_528_i1 : Fin 2 → ℕ := ![height_5, height_446]
theorem height_exact_528_i1 : height_528_i1 = 1 + Finset.univ.sup childrenH_528_i1 := by decide +kernel
theorem required_origin_528_i1 : ∀ x ∈ required_528_i1,
    (∃ j, x ∈ childrenC_528_i1 j) ∨ ∀ j, x ∈ childrenD_528_i1 j := by decide +kernel
theorem required_exact_528_i1 : required_528_i1 =
    ((Finset.univ.biUnion childrenC_528_i1) ∪ commonEnvelope childrenD_528_i1).erase (1, 7) := by
  exact required_eq_combination childrenC_528_i1 childrenD_528_i1 (1, 7) required_528_i1
    (by decide +kernel) child_required_sub_528_i1 common_sub_528_i1 required_origin_528_i1
theorem envelope_origin_528_i1 : ∀ x ∈ envelope_528_i1,
    x = (1, 7) ∨ ∃ j, x ∈ childrenD_528_i1 j := by decide +kernel
theorem envelope_exact_528_i1 : envelope_528_i1 =
    insert (1, 7) (Finset.univ.biUnion childrenD_528_i1) := by
  exact envelope_eq_combination childrenD_528_i1 (1, 7) envelope_528_i1
    pivot_mem_528_i1 child_envelope_sub_528_i1 envelope_origin_528_i1
def checked_528_i1 : CheckedCard where
  required := required_528_i1
  envelope := envelope_528_i1
  height := height_528_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_528_i1
def height_528 : ℕ := 9
def childrenH_528 : Fin 3 → ℕ := ![height_61, height_528_i0, height_528_i1]
theorem height_exact_528 : height_528 = 1 + Finset.univ.sup childrenH_528 := by decide +kernel
theorem required_origin_528 : ∀ x ∈ required_528,
    (∃ j, x ∈ childrenC_528 j) ∨ ∀ j, x ∈ childrenD_528 j := by decide +kernel
theorem required_exact_528 : required_528 =
    ((Finset.univ.biUnion childrenC_528) ∪ commonEnvelope childrenD_528).erase (0, 7) := by
  exact required_eq_combination childrenC_528 childrenD_528 (0, 7) required_528
    (by decide +kernel) child_required_sub_528 common_sub_528 required_origin_528
theorem envelope_origin_528 : ∀ x ∈ envelope_528,
    x = (0, 7) ∨ ∃ j, x ∈ childrenD_528 j := by decide +kernel
theorem envelope_exact_528 : envelope_528 =
    insert (0, 7) (Finset.univ.biUnion childrenD_528) := by
  exact envelope_eq_combination childrenD_528 (0, 7) envelope_528
    pivot_mem_528 child_envelope_sub_528 envelope_origin_528
def checked_528 : CheckedCard where
  required := required_528
  envelope := envelope_528
  height := height_528
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_528
def height_531 : ℕ := 9
def childrenH_531 : Fin 2 → ℕ := ![height_0, height_530]
theorem height_exact_531 : height_531 = 1 + Finset.univ.sup childrenH_531 := by decide +kernel
theorem required_origin_531 : ∀ x ∈ required_531,
    (∃ j, x ∈ childrenC_531 j) ∨ ∀ j, x ∈ childrenD_531 j := by decide +kernel
theorem required_exact_531 : required_531 =
    ((Finset.univ.biUnion childrenC_531) ∪ commonEnvelope childrenD_531).erase (1, 4) := by
  exact required_eq_combination childrenC_531 childrenD_531 (1, 4) required_531
    (by decide +kernel) child_required_sub_531 common_sub_531 required_origin_531
theorem envelope_origin_531 : ∀ x ∈ envelope_531,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_531 j := by decide +kernel
theorem envelope_exact_531 : envelope_531 =
    insert (1, 4) (Finset.univ.biUnion childrenD_531) := by
  exact envelope_eq_combination childrenD_531 (1, 4) envelope_531
    pivot_mem_531 child_envelope_sub_531 envelope_origin_531
def checked_531 : CheckedCard where
  required := required_531
  envelope := envelope_531
  height := height_531
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_531
def height_536 : ℕ := 9
def childrenH_536 : Fin 4 → ℕ := ![height_14, height_88, height_213, height_534]
theorem height_exact_536 : height_536 = 1 + Finset.univ.sup childrenH_536 := by decide +kernel
theorem required_origin_536 : ∀ x ∈ required_536,
    (∃ j, x ∈ childrenC_536 j) ∨ ∀ j, x ∈ childrenD_536 j := by decide +kernel
theorem required_exact_536 : required_536 =
    ((Finset.univ.biUnion childrenC_536) ∪ commonEnvelope childrenD_536).erase (3, 5) := by
  exact required_eq_combination childrenC_536 childrenD_536 (3, 5) required_536
    (by decide +kernel) child_required_sub_536 common_sub_536 required_origin_536
theorem envelope_origin_536 : ∀ x ∈ envelope_536,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_536 j := by decide +kernel
theorem envelope_exact_536 : envelope_536 =
    insert (3, 5) (Finset.univ.biUnion childrenD_536) := by
  exact envelope_eq_combination childrenD_536 (3, 5) envelope_536
    pivot_mem_536 child_envelope_sub_536 envelope_origin_536
def checked_536 : CheckedCard where
  required := required_536
  envelope := envelope_536
  height := height_536
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_536
def height_537_i0 : ℕ := 8
def childrenH_537_i0 : Fin 2 → ℕ := ![height_45, height_418]
theorem height_exact_537_i0 : height_537_i0 = 1 + Finset.univ.sup childrenH_537_i0 := by decide +kernel
theorem required_origin_537_i0 : ∀ x ∈ required_537_i0,
    (∃ j, x ∈ childrenC_537_i0 j) ∨ ∀ j, x ∈ childrenD_537_i0 j := by decide +kernel
theorem required_exact_537_i0 : required_537_i0 =
    ((Finset.univ.biUnion childrenC_537_i0) ∪ commonEnvelope childrenD_537_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_537_i0 childrenD_537_i0 (3, 3) required_537_i0
    (by decide +kernel) child_required_sub_537_i0 common_sub_537_i0 required_origin_537_i0
theorem envelope_origin_537_i0 : ∀ x ∈ envelope_537_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_537_i0 j := by decide +kernel
theorem envelope_exact_537_i0 : envelope_537_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_537_i0) := by
  exact envelope_eq_combination childrenD_537_i0 (3, 3) envelope_537_i0
    pivot_mem_537_i0 child_envelope_sub_537_i0 envelope_origin_537_i0
def checked_537_i0 : CheckedCard where
  required := required_537_i0
  envelope := envelope_537_i0
  height := height_537_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537_i0
def height_537_i2 : ℕ := 6
def childrenH_537_i2 : Fin 2 → ℕ := ![height_15, height_425]
theorem height_exact_537_i2 : height_537_i2 = 1 + Finset.univ.sup childrenH_537_i2 := by decide +kernel
theorem required_origin_537_i2 : ∀ x ∈ required_537_i2,
    (∃ j, x ∈ childrenC_537_i2 j) ∨ ∀ j, x ∈ childrenD_537_i2 j := by decide +kernel
theorem required_exact_537_i2 : required_537_i2 =
    ((Finset.univ.biUnion childrenC_537_i2) ∪ commonEnvelope childrenD_537_i2).erase (2, 5) := by
  exact required_eq_combination childrenC_537_i2 childrenD_537_i2 (2, 5) required_537_i2
    (by decide +kernel) child_required_sub_537_i2 common_sub_537_i2 required_origin_537_i2
theorem envelope_origin_537_i2 : ∀ x ∈ envelope_537_i2,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_537_i2 j := by decide +kernel
theorem envelope_exact_537_i2 : envelope_537_i2 =
    insert (2, 5) (Finset.univ.biUnion childrenD_537_i2) := by
  exact envelope_eq_combination childrenD_537_i2 (2, 5) envelope_537_i2
    pivot_mem_537_i2 child_envelope_sub_537_i2 envelope_origin_537_i2
def checked_537_i2 : CheckedCard where
  required := required_537_i2
  envelope := envelope_537_i2
  height := height_537_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537_i2
def height_537_i6 : ℕ := 3
def childrenH_537_i6 : Fin 2 → ℕ := ![height_0, height_23]
theorem height_exact_537_i6 : height_537_i6 = 1 + Finset.univ.sup childrenH_537_i6 := by decide +kernel
theorem required_origin_537_i6 : ∀ x ∈ required_537_i6,
    (∃ j, x ∈ childrenC_537_i6 j) ∨ ∀ j, x ∈ childrenD_537_i6 j := by decide +kernel
theorem required_exact_537_i6 : required_537_i6 =
    ((Finset.univ.biUnion childrenC_537_i6) ∪ commonEnvelope childrenD_537_i6).erase (2, 5) := by
  exact required_eq_combination childrenC_537_i6 childrenD_537_i6 (2, 5) required_537_i6
    (by decide +kernel) child_required_sub_537_i6 common_sub_537_i6 required_origin_537_i6
theorem envelope_origin_537_i6 : ∀ x ∈ envelope_537_i6,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_537_i6 j := by decide +kernel
theorem envelope_exact_537_i6 : envelope_537_i6 =
    insert (2, 5) (Finset.univ.biUnion childrenD_537_i6) := by
  exact envelope_eq_combination childrenD_537_i6 (2, 5) envelope_537_i6
    pivot_mem_537_i6 child_envelope_sub_537_i6 envelope_origin_537_i6
def checked_537_i6 : CheckedCard where
  required := required_537_i6
  envelope := envelope_537_i6
  height := height_537_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537_i6
def height_537_i5 : ℕ := 4
def childrenH_537_i5 : Fin 2 → ℕ := ![height_0, height_537_i6]
theorem height_exact_537_i5 : height_537_i5 = 1 + Finset.univ.sup childrenH_537_i5 := by decide +kernel
theorem required_origin_537_i5 : ∀ x ∈ required_537_i5,
    (∃ j, x ∈ childrenC_537_i5 j) ∨ ∀ j, x ∈ childrenD_537_i5 j := by decide +kernel
theorem required_exact_537_i5 : required_537_i5 =
    ((Finset.univ.biUnion childrenC_537_i5) ∪ commonEnvelope childrenD_537_i5).erase (3, 5) := by
  exact required_eq_combination childrenC_537_i5 childrenD_537_i5 (3, 5) required_537_i5
    (by decide +kernel) child_required_sub_537_i5 common_sub_537_i5 required_origin_537_i5
theorem envelope_origin_537_i5 : ∀ x ∈ envelope_537_i5,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_537_i5 j := by decide +kernel
theorem envelope_exact_537_i5 : envelope_537_i5 =
    insert (3, 5) (Finset.univ.biUnion childrenD_537_i5) := by
  exact envelope_eq_combination childrenD_537_i5 (3, 5) envelope_537_i5
    pivot_mem_537_i5 child_envelope_sub_537_i5 envelope_origin_537_i5
def checked_537_i5 : CheckedCard where
  required := required_537_i5
  envelope := envelope_537_i5
  height := height_537_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537_i5
def height_537_i4 : ℕ := 6
def childrenH_537_i4 : Fin 3 → ℕ := ![height_139, height_382, height_537_i5]
theorem height_exact_537_i4 : height_537_i4 = 1 + Finset.univ.sup childrenH_537_i4 := by decide +kernel
theorem required_origin_537_i4 : ∀ x ∈ required_537_i4,
    (∃ j, x ∈ childrenC_537_i4 j) ∨ ∀ j, x ∈ childrenD_537_i4 j := by decide +kernel
theorem required_exact_537_i4 : required_537_i4 =
    ((Finset.univ.biUnion childrenC_537_i4) ∪ commonEnvelope childrenD_537_i4).erase (3, 6) := by
  exact required_eq_combination childrenC_537_i4 childrenD_537_i4 (3, 6) required_537_i4
    (by decide +kernel) child_required_sub_537_i4 common_sub_537_i4 required_origin_537_i4
theorem envelope_origin_537_i4 : ∀ x ∈ envelope_537_i4,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_537_i4 j := by decide +kernel
theorem envelope_exact_537_i4 : envelope_537_i4 =
    insert (3, 6) (Finset.univ.biUnion childrenD_537_i4) := by
  exact envelope_eq_combination childrenD_537_i4 (3, 6) envelope_537_i4
    pivot_mem_537_i4 child_envelope_sub_537_i4 envelope_origin_537_i4
def checked_537_i4 : CheckedCard where
  required := required_537_i4
  envelope := envelope_537_i4
  height := height_537_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537_i4
def height_537_i3 : ℕ := 7
def childrenH_537_i3 : Fin 3 → ℕ := ![height_13, height_30, height_537_i4]
theorem height_exact_537_i3 : height_537_i3 = 1 + Finset.univ.sup childrenH_537_i3 := by decide +kernel
theorem required_origin_537_i3 : ∀ x ∈ required_537_i3,
    (∃ j, x ∈ childrenC_537_i3 j) ∨ ∀ j, x ∈ childrenD_537_i3 j := by decide +kernel
theorem required_exact_537_i3 : required_537_i3 =
    ((Finset.univ.biUnion childrenC_537_i3) ∪ commonEnvelope childrenD_537_i3).erase (4, 4) := by
  exact required_eq_combination childrenC_537_i3 childrenD_537_i3 (4, 4) required_537_i3
    (by decide +kernel) child_required_sub_537_i3 common_sub_537_i3 required_origin_537_i3
theorem envelope_origin_537_i3 : ∀ x ∈ envelope_537_i3,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_537_i3 j := by decide +kernel
theorem envelope_exact_537_i3 : envelope_537_i3 =
    insert (4, 4) (Finset.univ.biUnion childrenD_537_i3) := by
  exact envelope_eq_combination childrenD_537_i3 (4, 4) envelope_537_i3
    pivot_mem_537_i3 child_envelope_sub_537_i3 envelope_origin_537_i3
def checked_537_i3 : CheckedCard where
  required := required_537_i3
  envelope := envelope_537_i3
  height := height_537_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537_i3
def height_537_i1 : ℕ := 8
def childrenH_537_i1 : Fin 4 → ℕ := ![height_166, height_464, height_537_i2, height_537_i3]
theorem height_exact_537_i1 : height_537_i1 = 1 + Finset.univ.sup childrenH_537_i1 := by decide +kernel
theorem required_origin_537_i1 : ∀ x ∈ required_537_i1,
    (∃ j, x ∈ childrenC_537_i1 j) ∨ ∀ j, x ∈ childrenD_537_i1 j := by decide +kernel
theorem required_exact_537_i1 : required_537_i1 =
    ((Finset.univ.biUnion childrenC_537_i1) ∪ commonEnvelope childrenD_537_i1).erase (4, 5) := by
  exact required_eq_combination childrenC_537_i1 childrenD_537_i1 (4, 5) required_537_i1
    (by decide +kernel) child_required_sub_537_i1 common_sub_537_i1 required_origin_537_i1
theorem envelope_origin_537_i1 : ∀ x ∈ envelope_537_i1,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_537_i1 j := by decide +kernel
theorem envelope_exact_537_i1 : envelope_537_i1 =
    insert (4, 5) (Finset.univ.biUnion childrenD_537_i1) := by
  exact envelope_eq_combination childrenD_537_i1 (4, 5) envelope_537_i1
    pivot_mem_537_i1 child_envelope_sub_537_i1 envelope_origin_537_i1
def checked_537_i1 : CheckedCard where
  required := required_537_i1
  envelope := envelope_537_i1
  height := height_537_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537_i1
def height_537 : ℕ := 9
def childrenH_537 : Fin 4 → ℕ := ![height_74, height_108, height_537_i0, height_537_i1]
theorem height_exact_537 : height_537 = 1 + Finset.univ.sup childrenH_537 := by decide +kernel
theorem required_origin_537 : ∀ x ∈ required_537,
    (∃ j, x ∈ childrenC_537 j) ∨ ∀ j, x ∈ childrenD_537 j := by decide +kernel
theorem required_exact_537 : required_537 =
    ((Finset.univ.biUnion childrenC_537) ∪ commonEnvelope childrenD_537).erase (4, 3) := by
  exact required_eq_combination childrenC_537 childrenD_537 (4, 3) required_537
    (by decide +kernel) child_required_sub_537 common_sub_537 required_origin_537
theorem envelope_origin_537 : ∀ x ∈ envelope_537,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_537 j := by decide +kernel
theorem envelope_exact_537 : envelope_537 =
    insert (4, 3) (Finset.univ.biUnion childrenD_537) := by
  exact envelope_eq_combination childrenD_537 (4, 3) envelope_537
    pivot_mem_537 child_envelope_sub_537 envelope_origin_537
def checked_537 : CheckedCard where
  required := required_537
  envelope := envelope_537
  height := height_537
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_537
end SnakyPrototype.Certificate21

end OAI
