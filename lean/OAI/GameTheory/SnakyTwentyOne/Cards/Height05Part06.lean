import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_495_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 5), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_495_i0 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_495_i0 : Fin 2 → Finset Cell := ![(placed21 5 (2, 2) required_5), (placed21 4 (0, 5) required_221)]
def childrenD_495_i0 : Fin 2 → Finset Cell := ![(placed21 5 (2, 2) envelope_5), (placed21 4 (0, 5) envelope_221)]
theorem common_sub_495_i0 : commonEnvelope childrenD_495_i0 ⊆ insert (2, 2) required_495_i0 := by decide +kernel
theorem child_required_sub_495_i0 : ∀ j, childrenC_495_i0 j ⊆ insert (2, 2) required_495_i0 := by decide +kernel
theorem child_envelope_sub_495_i0 : ∀ j, childrenD_495_i0 j ⊆ envelope_495_i0 := by decide +kernel
theorem pivot_mem_495_i0 : (2, 2) ∈ envelope_495_i0 := by decide +kernel
theorem children_work_495_i0 : ∀ j, Template HasSnaky 3 (childrenC_495_i0 j) (childrenD_495_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_221 4 (0, 5)).mono (by decide +kernel)
theorem row_works_495_i0 : Template HasSnaky 4 required_495_i0 envelope_495_i0 := by
  refine compose HasSnaky 3 childrenC_495_i0 childrenD_495_i0 children_work_495_i0 (2, 2)
    required_495_i0 envelope_495_i0 pivot_mem_495_i0 child_required_sub_495_i0 child_envelope_sub_495_i0 ?_
  intro b hb
  exact common_sub_495_i0 (mem_commonEnvelope childrenD_495_i0 b hb)
def required_495 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 5), (2, 3), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_495 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 6), (3, 7), (3, 8), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_495 : Fin 4 → Finset Cell := ![(placed21 0 (1, 2) required_10), (placed21 2 (2, 2) required_52), (placed21 6 (2, 6) required_52), required_495_i0]
def childrenD_495 : Fin 4 → Finset Cell := ![(placed21 0 (1, 2) envelope_10), (placed21 2 (2, 2) envelope_52), (placed21 6 (2, 6) envelope_52), envelope_495_i0]
theorem common_sub_495 : commonEnvelope childrenD_495 ⊆ insert (2, 4) required_495 := by decide +kernel
theorem child_required_sub_495 : ∀ j, childrenC_495 j ⊆ insert (2, 4) required_495 := by decide +kernel
theorem child_envelope_sub_495 : ∀ j, childrenD_495 j ⊆ envelope_495 := by decide +kernel
theorem pivot_mem_495 : (2, 4) ∈ envelope_495 := by decide +kernel
theorem children_work_495 : ∀ j, Template HasSnaky 4 (childrenC_495 j) (childrenD_495 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (2, 6)).mono (by decide +kernel)
  · exact row_works_495_i0.mono (by decide +kernel)
theorem row_works_495 : Template HasSnaky 5 required_495 envelope_495 := by
  refine compose HasSnaky 4 childrenC_495 childrenD_495 children_work_495 (2, 4)
    required_495 envelope_495 pivot_mem_495 child_required_sub_495 child_envelope_sub_495 ?_
  intro b hb
  exact common_sub_495 (mem_commonEnvelope childrenD_495 b hb)
def required_497 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_497 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_497 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_5), required_496]
def childrenD_497 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_5), envelope_496]
theorem common_sub_497 : commonEnvelope childrenD_497 ⊆ insert (0, 3) required_497 := by decide +kernel
theorem child_required_sub_497 : ∀ j, childrenC_497 j ⊆ insert (0, 3) required_497 := by decide +kernel
theorem child_envelope_sub_497 : ∀ j, childrenD_497 j ⊆ envelope_497 := by decide +kernel
theorem pivot_mem_497 : (0, 3) ∈ envelope_497 := by decide +kernel
theorem children_work_497 : ∀ j, Template HasSnaky 4 (childrenC_497 j) (childrenD_497 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_496.mono (by decide +kernel)
theorem row_works_497 : Template HasSnaky 5 required_497 envelope_497 := by
  refine compose HasSnaky 4 childrenC_497 childrenD_497 children_work_497 (0, 3)
    required_497 envelope_497 pivot_mem_497 child_required_sub_497 child_envelope_sub_497 ?_
  intro b hb
  exact common_sub_497 (mem_commonEnvelope childrenD_497 b hb)
def required_501 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 4), (3, 1), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_501 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_501 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_2), required_500]
def childrenD_501 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_2), envelope_500]
theorem common_sub_501 : commonEnvelope childrenD_501 ⊆ insert (1, 3) required_501 := by decide +kernel
theorem child_required_sub_501 : ∀ j, childrenC_501 j ⊆ insert (1, 3) required_501 := by decide +kernel
theorem child_envelope_sub_501 : ∀ j, childrenD_501 j ⊆ envelope_501 := by decide +kernel
theorem pivot_mem_501 : (1, 3) ∈ envelope_501 := by decide +kernel
theorem children_work_501 : ∀ j, Template HasSnaky 4 (childrenC_501 j) (childrenD_501 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 2 (4, 3)).mono (by decide +kernel)
  · exact row_works_500.mono (by decide +kernel)
theorem row_works_501 : Template HasSnaky 5 required_501 envelope_501 := by
  refine compose HasSnaky 4 childrenC_501 childrenD_501 children_work_501 (1, 3)
    required_501 envelope_501 pivot_mem_501 child_required_sub_501 child_envelope_sub_501 ?_
  intro b hb
  exact common_sub_501 (mem_commonEnvelope childrenD_501 b hb)
def required_502_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_502_i0 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_502_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) required_11), (placed21 4 (2, 6) required_53)]
def childrenD_502_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) envelope_11), (placed21 4 (2, 6) envelope_53)]
theorem common_sub_502_i0 : commonEnvelope childrenD_502_i0 ⊆ insert (2, 4) required_502_i0 := by decide +kernel
theorem child_required_sub_502_i0 : ∀ j, childrenC_502_i0 j ⊆ insert (2, 4) required_502_i0 := by decide +kernel
theorem child_envelope_sub_502_i0 : ∀ j, childrenD_502_i0 j ⊆ envelope_502_i0 := by decide +kernel
theorem pivot_mem_502_i0 : (2, 4) ∈ envelope_502_i0 := by decide +kernel
theorem children_work_502_i0 : ∀ j, Template HasSnaky 3 (childrenC_502_i0 j) (childrenD_502_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 4 (2, 6)).mono (by decide +kernel)
theorem row_works_502_i0 : Template HasSnaky 4 required_502_i0 envelope_502_i0 := by
  refine compose HasSnaky 3 childrenC_502_i0 childrenD_502_i0 children_work_502_i0 (2, 4)
    required_502_i0 envelope_502_i0 pivot_mem_502_i0 child_required_sub_502_i0 child_envelope_sub_502_i0 ?_
  intro b hb
  exact common_sub_502_i0 (mem_commonEnvelope childrenD_502_i0 b hb)
def required_502 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_502 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_502 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) required_7), (placed21 4 (1, 5) required_69), required_502_i0]
def childrenD_502 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) envelope_7), (placed21 4 (1, 5) envelope_69), envelope_502_i0]
theorem common_sub_502 : commonEnvelope childrenD_502 ⊆ insert (4, 3) required_502 := by decide +kernel
theorem child_required_sub_502 : ∀ j, childrenC_502 j ⊆ insert (4, 3) required_502 := by decide +kernel
theorem child_envelope_sub_502 : ∀ j, childrenD_502 j ⊆ envelope_502 := by decide +kernel
theorem pivot_mem_502 : (4, 3) ∈ envelope_502 := by decide +kernel
theorem children_work_502 : ∀ j, Template HasSnaky 4 (childrenC_502 j) (childrenD_502 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_69 4 (1, 5)).mono (by decide +kernel)
  · exact row_works_502_i0.mono (by decide +kernel)
theorem row_works_502 : Template HasSnaky 5 required_502 envelope_502 := by
  refine compose HasSnaky 4 childrenC_502 childrenD_502 children_work_502 (4, 3)
    required_502 envelope_502 pivot_mem_502 child_required_sub_502 child_envelope_sub_502 ?_
  intro b hb
  exact common_sub_502 (mem_commonEnvelope childrenD_502 b hb)
def required_505_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (4, 1), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_505_i0 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_505_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) required_5), (placed21 0 (1, 0) required_350)]
def childrenD_505_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) envelope_5), (placed21 0 (1, 0) envelope_350)]
theorem common_sub_505_i0 : commonEnvelope childrenD_505_i0 ⊆ insert (4, 2) required_505_i0 := by decide +kernel
theorem child_required_sub_505_i0 : ∀ j, childrenC_505_i0 j ⊆ insert (4, 2) required_505_i0 := by decide +kernel
theorem child_envelope_sub_505_i0 : ∀ j, childrenD_505_i0 j ⊆ envelope_505_i0 := by decide +kernel
theorem pivot_mem_505_i0 : (4, 2) ∈ envelope_505_i0 := by decide +kernel
theorem children_work_505_i0 : ∀ j, Template HasSnaky 3 (childrenC_505_i0 j) (childrenD_505_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_350 0 (1, 0)).mono (by decide +kernel)
theorem row_works_505_i0 : Template HasSnaky 4 required_505_i0 envelope_505_i0 := by
  refine compose HasSnaky 3 childrenC_505_i0 childrenD_505_i0 children_work_505_i0 (4, 2)
    required_505_i0 envelope_505_i0 pivot_mem_505_i0 child_required_sub_505_i0 child_envelope_sub_505_i0 ?_
  intro b hb
  exact common_sub_505_i0 (mem_commonEnvelope childrenD_505_i0 b hb)
def required_505_i2 : Finset Cell := ⟨(([(3, 1), (4, 1), (4, 2), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_505_i2 : Finset Cell := ⟨(([(3, 0), (3, 1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_505_i2 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) required_5), (placed21 0 (4, 1) required_6)]
def childrenD_505_i2 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) envelope_5), (placed21 0 (4, 1) envelope_6)]
theorem common_sub_505_i2 : commonEnvelope childrenD_505_i2 ⊆ insert (4, 3) required_505_i2 := by decide +kernel
theorem child_required_sub_505_i2 : ∀ j, childrenC_505_i2 j ⊆ insert (4, 3) required_505_i2 := by decide +kernel
theorem child_envelope_sub_505_i2 : ∀ j, childrenD_505_i2 j ⊆ envelope_505_i2 := by decide +kernel
theorem pivot_mem_505_i2 : (4, 3) ∈ envelope_505_i2 := by decide +kernel
theorem children_work_505_i2 : ∀ j, Template HasSnaky 2 (childrenC_505_i2 j) (childrenD_505_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 0 (4, 1)).mono (by decide +kernel)
theorem row_works_505_i2 : Template HasSnaky 3 required_505_i2 envelope_505_i2 := by
  refine compose HasSnaky 2 childrenC_505_i2 childrenD_505_i2 children_work_505_i2 (4, 3)
    required_505_i2 envelope_505_i2 pivot_mem_505_i2 child_required_sub_505_i2 child_envelope_sub_505_i2 ?_
  intro b hb
  exact common_sub_505_i2 (mem_commonEnvelope childrenD_505_i2 b hb)
def required_505_i1 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (4, 1), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_505_i1 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 0), (3, 1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_505_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) required_5), required_505_i2]
def childrenD_505_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) envelope_5), envelope_505_i2]
theorem common_sub_505_i1 : commonEnvelope childrenD_505_i1 ⊆ insert (4, 2) required_505_i1 := by decide +kernel
theorem child_required_sub_505_i1 : ∀ j, childrenC_505_i1 j ⊆ insert (4, 2) required_505_i1 := by decide +kernel
theorem child_envelope_sub_505_i1 : ∀ j, childrenD_505_i1 j ⊆ envelope_505_i1 := by decide +kernel
theorem pivot_mem_505_i1 : (4, 2) ∈ envelope_505_i1 := by decide +kernel
theorem children_work_505_i1 : ∀ j, Template HasSnaky 3 (childrenC_505_i1 j) (childrenD_505_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_505_i2.mono (by decide +kernel)
theorem row_works_505_i1 : Template HasSnaky 4 required_505_i1 envelope_505_i1 := by
  refine compose HasSnaky 3 childrenC_505_i1 childrenD_505_i1 children_work_505_i1 (4, 2)
    required_505_i1 envelope_505_i1 pivot_mem_505_i1 child_required_sub_505_i1 child_envelope_sub_505_i1 ?_
  intro b hb
  exact common_sub_505_i1 (mem_commonEnvelope childrenD_505_i1 b hb)
def required_505 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_505 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_505 : Fin 3 → Finset Cell := ![(placed21 3 (0, 1) required_6), required_505_i0, required_505_i1]
def childrenD_505 : Fin 3 → Finset Cell := ![(placed21 3 (0, 1) envelope_6), envelope_505_i0, envelope_505_i1]
theorem common_sub_505 : commonEnvelope childrenD_505 ⊆ insert (4, 1) required_505 := by decide +kernel
theorem child_required_sub_505 : ∀ j, childrenC_505 j ⊆ insert (4, 1) required_505 := by decide +kernel
theorem child_envelope_sub_505 : ∀ j, childrenD_505 j ⊆ envelope_505 := by decide +kernel
theorem pivot_mem_505 : (4, 1) ∈ envelope_505 := by decide +kernel
theorem children_work_505 : ∀ j, Template HasSnaky 4 (childrenC_505 j) (childrenD_505 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact row_works_505_i0.mono (by decide +kernel)
  · exact row_works_505_i1.mono (by decide +kernel)
theorem row_works_505 : Template HasSnaky 5 required_505 envelope_505 := by
  refine compose HasSnaky 4 childrenC_505 childrenD_505 children_work_505 (4, 1)
    required_505 envelope_505 pivot_mem_505 child_required_sub_505 child_envelope_sub_505 ?_
  intro b hb
  exact common_sub_505 (mem_commonEnvelope childrenD_505 b hb)
def required_506_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_506_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_506_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_7), (placed21 3 (0, 5) required_32)]
def childrenD_506_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_7), (placed21 3 (0, 5) envelope_32)]
theorem common_sub_506_i0 : commonEnvelope childrenD_506_i0 ⊆ insert (1, 2) required_506_i0 := by decide +kernel
theorem child_required_sub_506_i0 : ∀ j, childrenC_506_i0 j ⊆ insert (1, 2) required_506_i0 := by decide +kernel
theorem child_envelope_sub_506_i0 : ∀ j, childrenD_506_i0 j ⊆ envelope_506_i0 := by decide +kernel
theorem pivot_mem_506_i0 : (1, 2) ∈ envelope_506_i0 := by decide +kernel
theorem children_work_506_i0 : ∀ j, Template HasSnaky 3 (childrenC_506_i0 j) (childrenD_506_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 3 (0, 5)).mono (by decide +kernel)
theorem row_works_506_i0 : Template HasSnaky 4 required_506_i0 envelope_506_i0 := by
  refine compose HasSnaky 3 childrenC_506_i0 childrenD_506_i0 children_work_506_i0 (1, 2)
    required_506_i0 envelope_506_i0 pivot_mem_506_i0 child_required_sub_506_i0 child_envelope_sub_506_i0 ?_
  intro b hb
  exact common_sub_506_i0 (mem_commonEnvelope childrenD_506_i0 b hb)
def required_506 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_506 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_506 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) required_44), (placed21 0 (0, 1) required_67), required_506_i0]
def childrenD_506 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) envelope_44), (placed21 0 (0, 1) envelope_67), envelope_506_i0]
theorem common_sub_506 : commonEnvelope childrenD_506 ⊆ insert (1, 5) required_506 := by decide +kernel
theorem child_required_sub_506 : ∀ j, childrenC_506 j ⊆ insert (1, 5) required_506 := by decide +kernel
theorem child_envelope_sub_506 : ∀ j, childrenD_506 j ⊆ envelope_506 := by decide +kernel
theorem pivot_mem_506 : (1, 5) ∈ envelope_506 := by decide +kernel
theorem children_work_506 : ∀ j, Template HasSnaky 4 (childrenC_506 j) (childrenD_506 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_67 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_506_i0.mono (by decide +kernel)
theorem row_works_506 : Template HasSnaky 5 required_506 envelope_506 := by
  refine compose HasSnaky 4 childrenC_506 childrenD_506 children_work_506 (1, 5)
    required_506 envelope_506 pivot_mem_506 child_required_sub_506 child_envelope_sub_506 ?_
  intro b hb
  exact common_sub_506 (mem_commonEnvelope childrenD_506 b hb)
def required_515_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_515_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_515_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 1) required_0), required_78]
def childrenD_515_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 1) envelope_0), envelope_78]
theorem common_sub_515_i0 : commonEnvelope childrenD_515_i0 ⊆ insert (3, 1) required_515_i0 := by decide +kernel
theorem child_required_sub_515_i0 : ∀ j, childrenC_515_i0 j ⊆ insert (3, 1) required_515_i0 := by decide +kernel
theorem child_envelope_sub_515_i0 : ∀ j, childrenD_515_i0 j ⊆ envelope_515_i0 := by decide +kernel
theorem pivot_mem_515_i0 : (3, 1) ∈ envelope_515_i0 := by decide +kernel
theorem children_work_515_i0 : ∀ j, Template HasSnaky 3 (childrenC_515_i0 j) (childrenD_515_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 1)).mono (by decide +kernel)
  · exact row_works_78.mono (by decide +kernel)
theorem row_works_515_i0 : Template HasSnaky 4 required_515_i0 envelope_515_i0 := by
  refine compose HasSnaky 3 childrenC_515_i0 childrenD_515_i0 children_work_515_i0 (3, 1)
    required_515_i0 envelope_515_i0 pivot_mem_515_i0 child_required_sub_515_i0 child_envelope_sub_515_i0 ?_
  intro b hb
  exact common_sub_515_i0 (mem_commonEnvelope childrenD_515_i0 b hb)
def required_515 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_515 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_515 : Fin 2 → Finset Cell := ![(placed21 7 (2, 4) required_2), required_515_i0]
def childrenD_515 : Fin 2 → Finset Cell := ![(placed21 7 (2, 4) envelope_2), envelope_515_i0]
theorem common_sub_515 : commonEnvelope childrenD_515 ⊆ insert (2, 1) required_515 := by decide +kernel
theorem child_required_sub_515 : ∀ j, childrenC_515 j ⊆ insert (2, 1) required_515 := by decide +kernel
theorem child_envelope_sub_515 : ∀ j, childrenD_515 j ⊆ envelope_515 := by decide +kernel
theorem pivot_mem_515 : (2, 1) ∈ envelope_515 := by decide +kernel
theorem children_work_515 : ∀ j, Template HasSnaky 4 (childrenC_515 j) (childrenD_515 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 7 (2, 4)).mono (by decide +kernel)
  · exact row_works_515_i0.mono (by decide +kernel)
theorem row_works_515 : Template HasSnaky 5 required_515 envelope_515 := by
  refine compose HasSnaky 4 childrenC_515 childrenD_515 children_work_515 (2, 1)
    required_515 envelope_515 pivot_mem_515 child_required_sub_515 child_envelope_sub_515 ?_
  intro b hb
  exact common_sub_515 (mem_commonEnvelope childrenD_515 b hb)
def required_592_i0 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_592_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_592_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_1), (placed21 4 (1, 6) required_158)]
def childrenD_592_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_1), (placed21 4 (1, 6) envelope_158)]
theorem common_sub_592_i0 : commonEnvelope childrenD_592_i0 ⊆ insert (1, 5) required_592_i0 := by decide +kernel
theorem child_required_sub_592_i0 : ∀ j, childrenC_592_i0 j ⊆ insert (1, 5) required_592_i0 := by decide +kernel
theorem child_envelope_sub_592_i0 : ∀ j, childrenD_592_i0 j ⊆ envelope_592_i0 := by decide +kernel
theorem pivot_mem_592_i0 : (1, 5) ∈ envelope_592_i0 := by decide +kernel
theorem children_work_592_i0 : ∀ j, Template HasSnaky 3 (childrenC_592_i0 j) (childrenD_592_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_158 4 (1, 6)).mono (by decide +kernel)
theorem row_works_592_i0 : Template HasSnaky 4 required_592_i0 envelope_592_i0 := by
  refine compose HasSnaky 3 childrenC_592_i0 childrenD_592_i0 children_work_592_i0 (1, 5)
    required_592_i0 envelope_592_i0 pivot_mem_592_i0 child_required_sub_592_i0 child_envelope_sub_592_i0 ?_
  intro b hb
  exact common_sub_592_i0 (mem_commonEnvelope childrenD_592_i0 b hb)
def required_592 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (1, 1), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_592 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_592 : Fin 4 → Finset Cell := ![(placed21 4 (0, 5) required_22), (placed21 6 (1, 4) required_36), required_150, required_592_i0]
def childrenD_592 : Fin 4 → Finset Cell := ![(placed21 4 (0, 5) envelope_22), (placed21 6 (1, 4) envelope_36), envelope_150, envelope_592_i0]
theorem common_sub_592 : commonEnvelope childrenD_592 ⊆ insert (1, 4) required_592 := by decide +kernel
theorem child_required_sub_592 : ∀ j, childrenC_592 j ⊆ insert (1, 4) required_592 := by decide +kernel
theorem child_envelope_sub_592 : ∀ j, childrenD_592 j ⊆ envelope_592 := by decide +kernel
theorem pivot_mem_592 : (1, 4) ∈ envelope_592 := by decide +kernel
theorem children_work_592 : ∀ j, Template HasSnaky 4 (childrenC_592 j) (childrenD_592 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_36 6 (1, 4)).mono (by decide +kernel)
  · exact row_works_150.mono (by decide +kernel)
  · exact row_works_592_i0.mono (by decide +kernel)
theorem row_works_592 : Template HasSnaky 5 required_592 envelope_592 := by
  refine compose HasSnaky 4 childrenC_592 childrenD_592 children_work_592 (1, 4)
    required_592 envelope_592 pivot_mem_592 child_required_sub_592 child_envelope_sub_592 ?_
  intro b hb
  exact common_sub_592 (mem_commonEnvelope childrenD_592 b hb)
def required_612_i1 : Finset Cell := ⟨(([(1, 1), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_612_i1 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_612_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) required_6), (placed21 2 (1, 1) required_6)]
def childrenD_612_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) envelope_6), (placed21 2 (1, 1) envelope_6)]
theorem common_sub_612_i1 : commonEnvelope childrenD_612_i1 ⊆ insert (1, 2) required_612_i1 := by decide +kernel
theorem child_required_sub_612_i1 : ∀ j, childrenC_612_i1 j ⊆ insert (1, 2) required_612_i1 := by decide +kernel
theorem child_envelope_sub_612_i1 : ∀ j, childrenD_612_i1 j ⊆ envelope_612_i1 := by decide +kernel
theorem pivot_mem_612_i1 : (1, 2) ∈ envelope_612_i1 := by decide +kernel
theorem children_work_612_i1 : ∀ j, Template HasSnaky 2 (childrenC_612_i1 j) (childrenD_612_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 2 (1, 1)).mono (by decide +kernel)
theorem row_works_612_i1 : Template HasSnaky 3 required_612_i1 envelope_612_i1 := by
  refine compose HasSnaky 2 childrenC_612_i1 childrenD_612_i1 children_work_612_i1 (1, 2)
    required_612_i1 envelope_612_i1 pivot_mem_612_i1 child_required_sub_612_i1 child_envelope_sub_612_i1 ?_
  intro b hb
  exact common_sub_612_i1 (mem_commonEnvelope childrenD_612_i1 b hb)
def required_612_i2 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_612_i2 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_612_i2 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) required_0), (placed21 1 (0, 1) required_3)]
def childrenD_612_i2 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) envelope_0), (placed21 1 (0, 1) envelope_3)]
theorem common_sub_612_i2 : commonEnvelope childrenD_612_i2 ⊆ insert (0, 2) required_612_i2 := by decide +kernel
theorem child_required_sub_612_i2 : ∀ j, childrenC_612_i2 j ⊆ insert (0, 2) required_612_i2 := by decide +kernel
theorem child_envelope_sub_612_i2 : ∀ j, childrenD_612_i2 j ⊆ envelope_612_i2 := by decide +kernel
theorem pivot_mem_612_i2 : (0, 2) ∈ envelope_612_i2 := by decide +kernel
theorem children_work_612_i2 : ∀ j, Template HasSnaky 1 (childrenC_612_i2 j) (childrenD_612_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 1 (0, 1)).mono (by decide +kernel)
theorem row_works_612_i2 : Template HasSnaky 2 required_612_i2 envelope_612_i2 := by
  refine compose HasSnaky 1 childrenC_612_i2 childrenD_612_i2 children_work_612_i2 (0, 2)
    required_612_i2 envelope_612_i2 pivot_mem_612_i2 child_required_sub_612_i2 child_envelope_sub_612_i2 ?_
  intro b hb
  exact common_sub_612_i2 (mem_commonEnvelope childrenD_612_i2 b hb)
def required_612_i3 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_612_i3 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_612_i3 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_4), (placed21 0 (1, 1) required_6)]
def childrenD_612_i3 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_4), (placed21 0 (1, 1) envelope_6)]
theorem common_sub_612_i3 : commonEnvelope childrenD_612_i3 ⊆ insert (1, 2) required_612_i3 := by decide +kernel
theorem child_required_sub_612_i3 : ∀ j, childrenC_612_i3 j ⊆ insert (1, 2) required_612_i3 := by decide +kernel
theorem child_envelope_sub_612_i3 : ∀ j, childrenD_612_i3 j ⊆ envelope_612_i3 := by decide +kernel
theorem pivot_mem_612_i3 : (1, 2) ∈ envelope_612_i3 := by decide +kernel
theorem children_work_612_i3 : ∀ j, Template HasSnaky 2 (childrenC_612_i3 j) (childrenD_612_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 0 (1, 1)).mono (by decide +kernel)
theorem row_works_612_i3 : Template HasSnaky 3 required_612_i3 envelope_612_i3 := by
  refine compose HasSnaky 2 childrenC_612_i3 childrenD_612_i3 children_work_612_i3 (1, 2)
    required_612_i3 envelope_612_i3 pivot_mem_612_i3 child_required_sub_612_i3 child_envelope_sub_612_i3 ?_
  intro b hb
  exact common_sub_612_i3 (mem_commonEnvelope childrenD_612_i3 b hb)
def required_612_i0 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_612_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_612_i0 : Fin 3 → Finset Cell := ![required_612_i1, required_612_i2, required_612_i3]
def childrenD_612_i0 : Fin 3 → Finset Cell := ![envelope_612_i1, envelope_612_i2, envelope_612_i3]
theorem common_sub_612_i0 : commonEnvelope childrenD_612_i0 ⊆ insert (1, 5) required_612_i0 := by decide +kernel
theorem child_required_sub_612_i0 : ∀ j, childrenC_612_i0 j ⊆ insert (1, 5) required_612_i0 := by decide +kernel
theorem child_envelope_sub_612_i0 : ∀ j, childrenD_612_i0 j ⊆ envelope_612_i0 := by decide +kernel
theorem pivot_mem_612_i0 : (1, 5) ∈ envelope_612_i0 := by decide +kernel
theorem children_work_612_i0 : ∀ j, Template HasSnaky 3 (childrenC_612_i0 j) (childrenD_612_i0 j) := by
  intro j
  fin_cases j
  · exact row_works_612_i1.mono (by decide +kernel)
  · exact row_works_612_i2.mono (by decide +kernel)
  · exact row_works_612_i3.mono (by decide +kernel)
theorem row_works_612_i0 : Template HasSnaky 4 required_612_i0 envelope_612_i0 := by
  refine compose HasSnaky 3 childrenC_612_i0 childrenD_612_i0 children_work_612_i0 (1, 5)
    required_612_i0 envelope_612_i0 pivot_mem_612_i0 child_required_sub_612_i0 child_envelope_sub_612_i0 ?_
  intro b hb
  exact common_sub_612_i0 (mem_commonEnvelope childrenD_612_i0 b hb)
def required_612 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_612 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_612 : Fin 4 → Finset Cell := ![(placed21 6 (1, 4) required_36), required_50, required_54, required_612_i0]
def childrenD_612 : Fin 4 → Finset Cell := ![(placed21 6 (1, 4) envelope_36), envelope_50, envelope_54, envelope_612_i0]
theorem common_sub_612 : commonEnvelope childrenD_612 ⊆ insert (1, 4) required_612 := by decide +kernel
theorem child_required_sub_612 : ∀ j, childrenC_612 j ⊆ insert (1, 4) required_612 := by decide +kernel
theorem child_envelope_sub_612 : ∀ j, childrenD_612 j ⊆ envelope_612 := by decide +kernel
theorem pivot_mem_612 : (1, 4) ∈ envelope_612 := by decide +kernel
theorem children_work_612 : ∀ j, Template HasSnaky 4 (childrenC_612 j) (childrenD_612 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_36 6 (1, 4)).mono (by decide +kernel)
  · exact row_works_50.mono (by decide +kernel)
  · exact row_works_54.mono (by decide +kernel)
  · exact row_works_612_i0.mono (by decide +kernel)
theorem row_works_612 : Template HasSnaky 5 required_612 envelope_612 := by
  refine compose HasSnaky 4 childrenC_612 childrenD_612 children_work_612 (1, 4)
    required_612 envelope_612 pivot_mem_612 child_required_sub_612 child_envelope_sub_612 ?_
  intro b hb
  exact common_sub_612 (mem_commonEnvelope childrenD_612 b hb)
def required_672_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (2, 2), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_672_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_672_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_22), (placed21 1 (0, 1) required_22)]
def childrenD_672_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_22), (placed21 1 (0, 1) envelope_22)]
theorem common_sub_672_i0 : commonEnvelope childrenD_672_i0 ⊆ insert (2, 1) required_672_i0 := by decide +kernel
theorem child_required_sub_672_i0 : ∀ j, childrenC_672_i0 j ⊆ insert (2, 1) required_672_i0 := by decide +kernel
theorem child_envelope_sub_672_i0 : ∀ j, childrenD_672_i0 j ⊆ envelope_672_i0 := by decide +kernel
theorem pivot_mem_672_i0 : (2, 1) ∈ envelope_672_i0 := by decide +kernel
theorem children_work_672_i0 : ∀ j, Template HasSnaky 2 (childrenC_672_i0 j) (childrenD_672_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_22 1 (0, 1)).mono (by decide +kernel)
theorem row_works_672_i0 : Template HasSnaky 3 required_672_i0 envelope_672_i0 := by
  refine compose HasSnaky 2 childrenC_672_i0 childrenD_672_i0 children_work_672_i0 (2, 1)
    required_672_i0 envelope_672_i0 pivot_mem_672_i0 child_required_sub_672_i0 child_envelope_sub_672_i0 ?_
  intro b hb
  exact common_sub_672_i0 (mem_commonEnvelope childrenD_672_i0 b hb)
def required_672 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_672 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_672 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) required_34), (placed21 1 (0, 1) required_305), required_672_i0]
def childrenD_672 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) envelope_34), (placed21 1 (0, 1) envelope_305), envelope_672_i0]
theorem common_sub_672 : commonEnvelope childrenD_672 ⊆ insert (2, 2) required_672 := by decide +kernel
theorem child_required_sub_672 : ∀ j, childrenC_672 j ⊆ insert (2, 2) required_672 := by decide +kernel
theorem child_envelope_sub_672 : ∀ j, childrenD_672 j ⊆ envelope_672 := by decide +kernel
theorem pivot_mem_672 : (2, 2) ∈ envelope_672 := by decide +kernel
theorem children_work_672 : ∀ j, Template HasSnaky 4 (childrenC_672 j) (childrenD_672 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 3 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_305 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_672_i0.mono (by decide +kernel)
theorem row_works_672 : Template HasSnaky 5 required_672 envelope_672 := by
  refine compose HasSnaky 4 childrenC_672 childrenD_672 children_work_672 (2, 2)
    required_672 envelope_672 pivot_mem_672 child_required_sub_672 child_envelope_sub_672 ?_
  intro b hb
  exact common_sub_672 (mem_commonEnvelope childrenD_672 b hb)
def height_495_i0 : ℕ := 4
def childrenH_495_i0 : Fin 2 → ℕ := ![height_5, height_221]
theorem height_exact_495_i0 : height_495_i0 = 1 + Finset.univ.sup childrenH_495_i0 := by decide +kernel
theorem required_origin_495_i0 : ∀ x ∈ required_495_i0,
    (∃ j, x ∈ childrenC_495_i0 j) ∨ ∀ j, x ∈ childrenD_495_i0 j := by decide +kernel
theorem required_exact_495_i0 : required_495_i0 =
    ((Finset.univ.biUnion childrenC_495_i0) ∪ commonEnvelope childrenD_495_i0).erase (2, 2) := by
  exact required_eq_combination childrenC_495_i0 childrenD_495_i0 (2, 2) required_495_i0
    (by decide +kernel) child_required_sub_495_i0 common_sub_495_i0 required_origin_495_i0
theorem envelope_origin_495_i0 : ∀ x ∈ envelope_495_i0,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_495_i0 j := by decide +kernel
theorem envelope_exact_495_i0 : envelope_495_i0 =
    insert (2, 2) (Finset.univ.biUnion childrenD_495_i0) := by
  exact envelope_eq_combination childrenD_495_i0 (2, 2) envelope_495_i0
    pivot_mem_495_i0 child_envelope_sub_495_i0 envelope_origin_495_i0
def checked_495_i0 : CheckedCard where
  required := required_495_i0
  envelope := envelope_495_i0
  height := height_495_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_495_i0
def height_495 : ℕ := 5
def childrenH_495 : Fin 4 → ℕ := ![height_10, height_52, height_52, height_495_i0]
theorem height_exact_495 : height_495 = 1 + Finset.univ.sup childrenH_495 := by decide +kernel
theorem required_origin_495 : ∀ x ∈ required_495,
    (∃ j, x ∈ childrenC_495 j) ∨ ∀ j, x ∈ childrenD_495 j := by decide +kernel
theorem required_exact_495 : required_495 =
    ((Finset.univ.biUnion childrenC_495) ∪ commonEnvelope childrenD_495).erase (2, 4) := by
  exact required_eq_combination childrenC_495 childrenD_495 (2, 4) required_495
    (by decide +kernel) child_required_sub_495 common_sub_495 required_origin_495
theorem envelope_origin_495 : ∀ x ∈ envelope_495,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_495 j := by decide +kernel
theorem envelope_exact_495 : envelope_495 =
    insert (2, 4) (Finset.univ.biUnion childrenD_495) := by
  exact envelope_eq_combination childrenD_495 (2, 4) envelope_495
    pivot_mem_495 child_envelope_sub_495 envelope_origin_495
def checked_495 : CheckedCard where
  required := required_495
  envelope := envelope_495
  height := height_495
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_495
def height_497 : ℕ := 5
def childrenH_497 : Fin 2 → ℕ := ![height_5, height_496]
theorem height_exact_497 : height_497 = 1 + Finset.univ.sup childrenH_497 := by decide +kernel
theorem required_origin_497 : ∀ x ∈ required_497,
    (∃ j, x ∈ childrenC_497 j) ∨ ∀ j, x ∈ childrenD_497 j := by decide +kernel
theorem required_exact_497 : required_497 =
    ((Finset.univ.biUnion childrenC_497) ∪ commonEnvelope childrenD_497).erase (0, 3) := by
  exact required_eq_combination childrenC_497 childrenD_497 (0, 3) required_497
    (by decide +kernel) child_required_sub_497 common_sub_497 required_origin_497
theorem envelope_origin_497 : ∀ x ∈ envelope_497,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_497 j := by decide +kernel
theorem envelope_exact_497 : envelope_497 =
    insert (0, 3) (Finset.univ.biUnion childrenD_497) := by
  exact envelope_eq_combination childrenD_497 (0, 3) envelope_497
    pivot_mem_497 child_envelope_sub_497 envelope_origin_497
def checked_497 : CheckedCard where
  required := required_497
  envelope := envelope_497
  height := height_497
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_497
def height_501 : ℕ := 5
def childrenH_501 : Fin 2 → ℕ := ![height_2, height_500]
theorem height_exact_501 : height_501 = 1 + Finset.univ.sup childrenH_501 := by decide +kernel
theorem required_origin_501 : ∀ x ∈ required_501,
    (∃ j, x ∈ childrenC_501 j) ∨ ∀ j, x ∈ childrenD_501 j := by decide +kernel
theorem required_exact_501 : required_501 =
    ((Finset.univ.biUnion childrenC_501) ∪ commonEnvelope childrenD_501).erase (1, 3) := by
  exact required_eq_combination childrenC_501 childrenD_501 (1, 3) required_501
    (by decide +kernel) child_required_sub_501 common_sub_501 required_origin_501
theorem envelope_origin_501 : ∀ x ∈ envelope_501,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_501 j := by decide +kernel
theorem envelope_exact_501 : envelope_501 =
    insert (1, 3) (Finset.univ.biUnion childrenD_501) := by
  exact envelope_eq_combination childrenD_501 (1, 3) envelope_501
    pivot_mem_501 child_envelope_sub_501 envelope_origin_501
def checked_501 : CheckedCard where
  required := required_501
  envelope := envelope_501
  height := height_501
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_501
def height_502_i0 : ℕ := 4
def childrenH_502_i0 : Fin 2 → ℕ := ![height_11, height_53]
theorem height_exact_502_i0 : height_502_i0 = 1 + Finset.univ.sup childrenH_502_i0 := by decide +kernel
theorem required_origin_502_i0 : ∀ x ∈ required_502_i0,
    (∃ j, x ∈ childrenC_502_i0 j) ∨ ∀ j, x ∈ childrenD_502_i0 j := by decide +kernel
theorem required_exact_502_i0 : required_502_i0 =
    ((Finset.univ.biUnion childrenC_502_i0) ∪ commonEnvelope childrenD_502_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_502_i0 childrenD_502_i0 (2, 4) required_502_i0
    (by decide +kernel) child_required_sub_502_i0 common_sub_502_i0 required_origin_502_i0
theorem envelope_origin_502_i0 : ∀ x ∈ envelope_502_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_502_i0 j := by decide +kernel
theorem envelope_exact_502_i0 : envelope_502_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_502_i0) := by
  exact envelope_eq_combination childrenD_502_i0 (2, 4) envelope_502_i0
    pivot_mem_502_i0 child_envelope_sub_502_i0 envelope_origin_502_i0
def checked_502_i0 : CheckedCard where
  required := required_502_i0
  envelope := envelope_502_i0
  height := height_502_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_502_i0
def height_502 : ℕ := 5
def childrenH_502 : Fin 3 → ℕ := ![height_7, height_69, height_502_i0]
theorem height_exact_502 : height_502 = 1 + Finset.univ.sup childrenH_502 := by decide +kernel
theorem required_origin_502 : ∀ x ∈ required_502,
    (∃ j, x ∈ childrenC_502 j) ∨ ∀ j, x ∈ childrenD_502 j := by decide +kernel
theorem required_exact_502 : required_502 =
    ((Finset.univ.biUnion childrenC_502) ∪ commonEnvelope childrenD_502).erase (4, 3) := by
  exact required_eq_combination childrenC_502 childrenD_502 (4, 3) required_502
    (by decide +kernel) child_required_sub_502 common_sub_502 required_origin_502
theorem envelope_origin_502 : ∀ x ∈ envelope_502,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_502 j := by decide +kernel
theorem envelope_exact_502 : envelope_502 =
    insert (4, 3) (Finset.univ.biUnion childrenD_502) := by
  exact envelope_eq_combination childrenD_502 (4, 3) envelope_502
    pivot_mem_502 child_envelope_sub_502 envelope_origin_502
def checked_502 : CheckedCard where
  required := required_502
  envelope := envelope_502
  height := height_502
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_502
def height_505_i0 : ℕ := 4
def childrenH_505_i0 : Fin 2 → ℕ := ![height_5, height_350]
theorem height_exact_505_i0 : height_505_i0 = 1 + Finset.univ.sup childrenH_505_i0 := by decide +kernel
theorem required_origin_505_i0 : ∀ x ∈ required_505_i0,
    (∃ j, x ∈ childrenC_505_i0 j) ∨ ∀ j, x ∈ childrenD_505_i0 j := by decide +kernel
theorem required_exact_505_i0 : required_505_i0 =
    ((Finset.univ.biUnion childrenC_505_i0) ∪ commonEnvelope childrenD_505_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_505_i0 childrenD_505_i0 (4, 2) required_505_i0
    (by decide +kernel) child_required_sub_505_i0 common_sub_505_i0 required_origin_505_i0
theorem envelope_origin_505_i0 : ∀ x ∈ envelope_505_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_505_i0 j := by decide +kernel
theorem envelope_exact_505_i0 : envelope_505_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_505_i0) := by
  exact envelope_eq_combination childrenD_505_i0 (4, 2) envelope_505_i0
    pivot_mem_505_i0 child_envelope_sub_505_i0 envelope_origin_505_i0
def checked_505_i0 : CheckedCard where
  required := required_505_i0
  envelope := envelope_505_i0
  height := height_505_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_505_i0
def height_505_i2 : ℕ := 3
def childrenH_505_i2 : Fin 2 → ℕ := ![height_5, height_6]
theorem height_exact_505_i2 : height_505_i2 = 1 + Finset.univ.sup childrenH_505_i2 := by decide +kernel
theorem required_origin_505_i2 : ∀ x ∈ required_505_i2,
    (∃ j, x ∈ childrenC_505_i2 j) ∨ ∀ j, x ∈ childrenD_505_i2 j := by decide +kernel
theorem required_exact_505_i2 : required_505_i2 =
    ((Finset.univ.biUnion childrenC_505_i2) ∪ commonEnvelope childrenD_505_i2).erase (4, 3) := by
  exact required_eq_combination childrenC_505_i2 childrenD_505_i2 (4, 3) required_505_i2
    (by decide +kernel) child_required_sub_505_i2 common_sub_505_i2 required_origin_505_i2
theorem envelope_origin_505_i2 : ∀ x ∈ envelope_505_i2,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_505_i2 j := by decide +kernel
theorem envelope_exact_505_i2 : envelope_505_i2 =
    insert (4, 3) (Finset.univ.biUnion childrenD_505_i2) := by
  exact envelope_eq_combination childrenD_505_i2 (4, 3) envelope_505_i2
    pivot_mem_505_i2 child_envelope_sub_505_i2 envelope_origin_505_i2
def checked_505_i2 : CheckedCard where
  required := required_505_i2
  envelope := envelope_505_i2
  height := height_505_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_505_i2
def height_505_i1 : ℕ := 4
def childrenH_505_i1 : Fin 2 → ℕ := ![height_5, height_505_i2]
theorem height_exact_505_i1 : height_505_i1 = 1 + Finset.univ.sup childrenH_505_i1 := by decide +kernel
theorem required_origin_505_i1 : ∀ x ∈ required_505_i1,
    (∃ j, x ∈ childrenC_505_i1 j) ∨ ∀ j, x ∈ childrenD_505_i1 j := by decide +kernel
theorem required_exact_505_i1 : required_505_i1 =
    ((Finset.univ.biUnion childrenC_505_i1) ∪ commonEnvelope childrenD_505_i1).erase (4, 2) := by
  exact required_eq_combination childrenC_505_i1 childrenD_505_i1 (4, 2) required_505_i1
    (by decide +kernel) child_required_sub_505_i1 common_sub_505_i1 required_origin_505_i1
theorem envelope_origin_505_i1 : ∀ x ∈ envelope_505_i1,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_505_i1 j := by decide +kernel
theorem envelope_exact_505_i1 : envelope_505_i1 =
    insert (4, 2) (Finset.univ.biUnion childrenD_505_i1) := by
  exact envelope_eq_combination childrenD_505_i1 (4, 2) envelope_505_i1
    pivot_mem_505_i1 child_envelope_sub_505_i1 envelope_origin_505_i1
def checked_505_i1 : CheckedCard where
  required := required_505_i1
  envelope := envelope_505_i1
  height := height_505_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_505_i1
def height_505 : ℕ := 5
def childrenH_505 : Fin 3 → ℕ := ![height_6, height_505_i0, height_505_i1]
theorem height_exact_505 : height_505 = 1 + Finset.univ.sup childrenH_505 := by decide +kernel
theorem required_origin_505 : ∀ x ∈ required_505,
    (∃ j, x ∈ childrenC_505 j) ∨ ∀ j, x ∈ childrenD_505 j := by decide +kernel
theorem required_exact_505 : required_505 =
    ((Finset.univ.biUnion childrenC_505) ∪ commonEnvelope childrenD_505).erase (4, 1) := by
  exact required_eq_combination childrenC_505 childrenD_505 (4, 1) required_505
    (by decide +kernel) child_required_sub_505 common_sub_505 required_origin_505
theorem envelope_origin_505 : ∀ x ∈ envelope_505,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_505 j := by decide +kernel
theorem envelope_exact_505 : envelope_505 =
    insert (4, 1) (Finset.univ.biUnion childrenD_505) := by
  exact envelope_eq_combination childrenD_505 (4, 1) envelope_505
    pivot_mem_505 child_envelope_sub_505 envelope_origin_505
def checked_505 : CheckedCard where
  required := required_505
  envelope := envelope_505
  height := height_505
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_505
def height_506_i0 : ℕ := 4
def childrenH_506_i0 : Fin 2 → ℕ := ![height_7, height_32]
theorem height_exact_506_i0 : height_506_i0 = 1 + Finset.univ.sup childrenH_506_i0 := by decide +kernel
theorem required_origin_506_i0 : ∀ x ∈ required_506_i0,
    (∃ j, x ∈ childrenC_506_i0 j) ∨ ∀ j, x ∈ childrenD_506_i0 j := by decide +kernel
theorem required_exact_506_i0 : required_506_i0 =
    ((Finset.univ.biUnion childrenC_506_i0) ∪ commonEnvelope childrenD_506_i0).erase (1, 2) := by
  exact required_eq_combination childrenC_506_i0 childrenD_506_i0 (1, 2) required_506_i0
    (by decide +kernel) child_required_sub_506_i0 common_sub_506_i0 required_origin_506_i0
theorem envelope_origin_506_i0 : ∀ x ∈ envelope_506_i0,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_506_i0 j := by decide +kernel
theorem envelope_exact_506_i0 : envelope_506_i0 =
    insert (1, 2) (Finset.univ.biUnion childrenD_506_i0) := by
  exact envelope_eq_combination childrenD_506_i0 (1, 2) envelope_506_i0
    pivot_mem_506_i0 child_envelope_sub_506_i0 envelope_origin_506_i0
def checked_506_i0 : CheckedCard where
  required := required_506_i0
  envelope := envelope_506_i0
  height := height_506_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_506_i0
def height_506 : ℕ := 5
def childrenH_506 : Fin 3 → ℕ := ![height_44, height_67, height_506_i0]
theorem height_exact_506 : height_506 = 1 + Finset.univ.sup childrenH_506 := by decide +kernel
theorem required_origin_506 : ∀ x ∈ required_506,
    (∃ j, x ∈ childrenC_506 j) ∨ ∀ j, x ∈ childrenD_506 j := by decide +kernel
theorem required_exact_506 : required_506 =
    ((Finset.univ.biUnion childrenC_506) ∪ commonEnvelope childrenD_506).erase (1, 5) := by
  exact required_eq_combination childrenC_506 childrenD_506 (1, 5) required_506
    (by decide +kernel) child_required_sub_506 common_sub_506 required_origin_506
theorem envelope_origin_506 : ∀ x ∈ envelope_506,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_506 j := by decide +kernel
theorem envelope_exact_506 : envelope_506 =
    insert (1, 5) (Finset.univ.biUnion childrenD_506) := by
  exact envelope_eq_combination childrenD_506 (1, 5) envelope_506
    pivot_mem_506 child_envelope_sub_506 envelope_origin_506
def checked_506 : CheckedCard where
  required := required_506
  envelope := envelope_506
  height := height_506
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_506
def height_515_i0 : ℕ := 4
def childrenH_515_i0 : Fin 2 → ℕ := ![height_0, height_78]
theorem height_exact_515_i0 : height_515_i0 = 1 + Finset.univ.sup childrenH_515_i0 := by decide +kernel
theorem required_origin_515_i0 : ∀ x ∈ required_515_i0,
    (∃ j, x ∈ childrenC_515_i0 j) ∨ ∀ j, x ∈ childrenD_515_i0 j := by decide +kernel
theorem required_exact_515_i0 : required_515_i0 =
    ((Finset.univ.biUnion childrenC_515_i0) ∪ commonEnvelope childrenD_515_i0).erase (3, 1) := by
  exact required_eq_combination childrenC_515_i0 childrenD_515_i0 (3, 1) required_515_i0
    (by decide +kernel) child_required_sub_515_i0 common_sub_515_i0 required_origin_515_i0
theorem envelope_origin_515_i0 : ∀ x ∈ envelope_515_i0,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_515_i0 j := by decide +kernel
theorem envelope_exact_515_i0 : envelope_515_i0 =
    insert (3, 1) (Finset.univ.biUnion childrenD_515_i0) := by
  exact envelope_eq_combination childrenD_515_i0 (3, 1) envelope_515_i0
    pivot_mem_515_i0 child_envelope_sub_515_i0 envelope_origin_515_i0
def checked_515_i0 : CheckedCard where
  required := required_515_i0
  envelope := envelope_515_i0
  height := height_515_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_515_i0
def height_515 : ℕ := 5
def childrenH_515 : Fin 2 → ℕ := ![height_2, height_515_i0]
theorem height_exact_515 : height_515 = 1 + Finset.univ.sup childrenH_515 := by decide +kernel
theorem required_origin_515 : ∀ x ∈ required_515,
    (∃ j, x ∈ childrenC_515 j) ∨ ∀ j, x ∈ childrenD_515 j := by decide +kernel
theorem required_exact_515 : required_515 =
    ((Finset.univ.biUnion childrenC_515) ∪ commonEnvelope childrenD_515).erase (2, 1) := by
  exact required_eq_combination childrenC_515 childrenD_515 (2, 1) required_515
    (by decide +kernel) child_required_sub_515 common_sub_515 required_origin_515
theorem envelope_origin_515 : ∀ x ∈ envelope_515,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_515 j := by decide +kernel
theorem envelope_exact_515 : envelope_515 =
    insert (2, 1) (Finset.univ.biUnion childrenD_515) := by
  exact envelope_eq_combination childrenD_515 (2, 1) envelope_515
    pivot_mem_515 child_envelope_sub_515 envelope_origin_515
def checked_515 : CheckedCard where
  required := required_515
  envelope := envelope_515
  height := height_515
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_515
def height_592_i0 : ℕ := 4
def childrenH_592_i0 : Fin 2 → ℕ := ![height_1, height_158]
theorem height_exact_592_i0 : height_592_i0 = 1 + Finset.univ.sup childrenH_592_i0 := by decide +kernel
theorem required_origin_592_i0 : ∀ x ∈ required_592_i0,
    (∃ j, x ∈ childrenC_592_i0 j) ∨ ∀ j, x ∈ childrenD_592_i0 j := by decide +kernel
theorem required_exact_592_i0 : required_592_i0 =
    ((Finset.univ.biUnion childrenC_592_i0) ∪ commonEnvelope childrenD_592_i0).erase (1, 5) := by
  exact required_eq_combination childrenC_592_i0 childrenD_592_i0 (1, 5) required_592_i0
    (by decide +kernel) child_required_sub_592_i0 common_sub_592_i0 required_origin_592_i0
theorem envelope_origin_592_i0 : ∀ x ∈ envelope_592_i0,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_592_i0 j := by decide +kernel
theorem envelope_exact_592_i0 : envelope_592_i0 =
    insert (1, 5) (Finset.univ.biUnion childrenD_592_i0) := by
  exact envelope_eq_combination childrenD_592_i0 (1, 5) envelope_592_i0
    pivot_mem_592_i0 child_envelope_sub_592_i0 envelope_origin_592_i0
def checked_592_i0 : CheckedCard where
  required := required_592_i0
  envelope := envelope_592_i0
  height := height_592_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_592_i0
def height_592 : ℕ := 5
def childrenH_592 : Fin 4 → ℕ := ![height_22, height_36, height_150, height_592_i0]
theorem height_exact_592 : height_592 = 1 + Finset.univ.sup childrenH_592 := by decide +kernel
theorem required_origin_592 : ∀ x ∈ required_592,
    (∃ j, x ∈ childrenC_592 j) ∨ ∀ j, x ∈ childrenD_592 j := by decide +kernel
theorem required_exact_592 : required_592 =
    ((Finset.univ.biUnion childrenC_592) ∪ commonEnvelope childrenD_592).erase (1, 4) := by
  exact required_eq_combination childrenC_592 childrenD_592 (1, 4) required_592
    (by decide +kernel) child_required_sub_592 common_sub_592 required_origin_592
theorem envelope_origin_592 : ∀ x ∈ envelope_592,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_592 j := by decide +kernel
theorem envelope_exact_592 : envelope_592 =
    insert (1, 4) (Finset.univ.biUnion childrenD_592) := by
  exact envelope_eq_combination childrenD_592 (1, 4) envelope_592
    pivot_mem_592 child_envelope_sub_592 envelope_origin_592
def checked_592 : CheckedCard where
  required := required_592
  envelope := envelope_592
  height := height_592
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_592
def height_612_i1 : ℕ := 3
def childrenH_612_i1 : Fin 2 → ℕ := ![height_6, height_6]
theorem height_exact_612_i1 : height_612_i1 = 1 + Finset.univ.sup childrenH_612_i1 := by decide +kernel
theorem required_origin_612_i1 : ∀ x ∈ required_612_i1,
    (∃ j, x ∈ childrenC_612_i1 j) ∨ ∀ j, x ∈ childrenD_612_i1 j := by decide +kernel
theorem required_exact_612_i1 : required_612_i1 =
    ((Finset.univ.biUnion childrenC_612_i1) ∪ commonEnvelope childrenD_612_i1).erase (1, 2) := by
  exact required_eq_combination childrenC_612_i1 childrenD_612_i1 (1, 2) required_612_i1
    (by decide +kernel) child_required_sub_612_i1 common_sub_612_i1 required_origin_612_i1
theorem envelope_origin_612_i1 : ∀ x ∈ envelope_612_i1,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_612_i1 j := by decide +kernel
theorem envelope_exact_612_i1 : envelope_612_i1 =
    insert (1, 2) (Finset.univ.biUnion childrenD_612_i1) := by
  exact envelope_eq_combination childrenD_612_i1 (1, 2) envelope_612_i1
    pivot_mem_612_i1 child_envelope_sub_612_i1 envelope_origin_612_i1
def checked_612_i1 : CheckedCard where
  required := required_612_i1
  envelope := envelope_612_i1
  height := height_612_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_612_i1
def height_612_i2 : ℕ := 2
def childrenH_612_i2 : Fin 2 → ℕ := ![height_0, height_3]
theorem height_exact_612_i2 : height_612_i2 = 1 + Finset.univ.sup childrenH_612_i2 := by decide +kernel
theorem required_origin_612_i2 : ∀ x ∈ required_612_i2,
    (∃ j, x ∈ childrenC_612_i2 j) ∨ ∀ j, x ∈ childrenD_612_i2 j := by decide +kernel
theorem required_exact_612_i2 : required_612_i2 =
    ((Finset.univ.biUnion childrenC_612_i2) ∪ commonEnvelope childrenD_612_i2).erase (0, 2) := by
  exact required_eq_combination childrenC_612_i2 childrenD_612_i2 (0, 2) required_612_i2
    (by decide +kernel) child_required_sub_612_i2 common_sub_612_i2 required_origin_612_i2
theorem envelope_origin_612_i2 : ∀ x ∈ envelope_612_i2,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_612_i2 j := by decide +kernel
theorem envelope_exact_612_i2 : envelope_612_i2 =
    insert (0, 2) (Finset.univ.biUnion childrenD_612_i2) := by
  exact envelope_eq_combination childrenD_612_i2 (0, 2) envelope_612_i2
    pivot_mem_612_i2 child_envelope_sub_612_i2 envelope_origin_612_i2
def checked_612_i2 : CheckedCard where
  required := required_612_i2
  envelope := envelope_612_i2
  height := height_612_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_612_i2
def height_612_i3 : ℕ := 3
def childrenH_612_i3 : Fin 2 → ℕ := ![height_4, height_6]
theorem height_exact_612_i3 : height_612_i3 = 1 + Finset.univ.sup childrenH_612_i3 := by decide +kernel
theorem required_origin_612_i3 : ∀ x ∈ required_612_i3,
    (∃ j, x ∈ childrenC_612_i3 j) ∨ ∀ j, x ∈ childrenD_612_i3 j := by decide +kernel
theorem required_exact_612_i3 : required_612_i3 =
    ((Finset.univ.biUnion childrenC_612_i3) ∪ commonEnvelope childrenD_612_i3).erase (1, 2) := by
  exact required_eq_combination childrenC_612_i3 childrenD_612_i3 (1, 2) required_612_i3
    (by decide +kernel) child_required_sub_612_i3 common_sub_612_i3 required_origin_612_i3
theorem envelope_origin_612_i3 : ∀ x ∈ envelope_612_i3,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_612_i3 j := by decide +kernel
theorem envelope_exact_612_i3 : envelope_612_i3 =
    insert (1, 2) (Finset.univ.biUnion childrenD_612_i3) := by
  exact envelope_eq_combination childrenD_612_i3 (1, 2) envelope_612_i3
    pivot_mem_612_i3 child_envelope_sub_612_i3 envelope_origin_612_i3
def checked_612_i3 : CheckedCard where
  required := required_612_i3
  envelope := envelope_612_i3
  height := height_612_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_612_i3
def height_612_i0 : ℕ := 4
def childrenH_612_i0 : Fin 3 → ℕ := ![height_612_i1, height_612_i2, height_612_i3]
theorem height_exact_612_i0 : height_612_i0 = 1 + Finset.univ.sup childrenH_612_i0 := by decide +kernel
theorem required_origin_612_i0 : ∀ x ∈ required_612_i0,
    (∃ j, x ∈ childrenC_612_i0 j) ∨ ∀ j, x ∈ childrenD_612_i0 j := by decide +kernel
theorem required_exact_612_i0 : required_612_i0 =
    ((Finset.univ.biUnion childrenC_612_i0) ∪ commonEnvelope childrenD_612_i0).erase (1, 5) := by
  exact required_eq_combination childrenC_612_i0 childrenD_612_i0 (1, 5) required_612_i0
    (by decide +kernel) child_required_sub_612_i0 common_sub_612_i0 required_origin_612_i0
theorem envelope_origin_612_i0 : ∀ x ∈ envelope_612_i0,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_612_i0 j := by decide +kernel
theorem envelope_exact_612_i0 : envelope_612_i0 =
    insert (1, 5) (Finset.univ.biUnion childrenD_612_i0) := by
  exact envelope_eq_combination childrenD_612_i0 (1, 5) envelope_612_i0
    pivot_mem_612_i0 child_envelope_sub_612_i0 envelope_origin_612_i0
def checked_612_i0 : CheckedCard where
  required := required_612_i0
  envelope := envelope_612_i0
  height := height_612_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_612_i0
def height_612 : ℕ := 5
def childrenH_612 : Fin 4 → ℕ := ![height_36, height_50, height_54, height_612_i0]
theorem height_exact_612 : height_612 = 1 + Finset.univ.sup childrenH_612 := by decide +kernel
theorem required_origin_612 : ∀ x ∈ required_612,
    (∃ j, x ∈ childrenC_612 j) ∨ ∀ j, x ∈ childrenD_612 j := by decide +kernel
theorem required_exact_612 : required_612 =
    ((Finset.univ.biUnion childrenC_612) ∪ commonEnvelope childrenD_612).erase (1, 4) := by
  exact required_eq_combination childrenC_612 childrenD_612 (1, 4) required_612
    (by decide +kernel) child_required_sub_612 common_sub_612 required_origin_612
theorem envelope_origin_612 : ∀ x ∈ envelope_612,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_612 j := by decide +kernel
theorem envelope_exact_612 : envelope_612 =
    insert (1, 4) (Finset.univ.biUnion childrenD_612) := by
  exact envelope_eq_combination childrenD_612 (1, 4) envelope_612
    pivot_mem_612 child_envelope_sub_612 envelope_origin_612
def checked_612 : CheckedCard where
  required := required_612
  envelope := envelope_612
  height := height_612
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_612
def height_672_i0 : ℕ := 3
def childrenH_672_i0 : Fin 2 → ℕ := ![height_22, height_22]
theorem height_exact_672_i0 : height_672_i0 = 1 + Finset.univ.sup childrenH_672_i0 := by decide +kernel
theorem required_origin_672_i0 : ∀ x ∈ required_672_i0,
    (∃ j, x ∈ childrenC_672_i0 j) ∨ ∀ j, x ∈ childrenD_672_i0 j := by decide +kernel
theorem required_exact_672_i0 : required_672_i0 =
    ((Finset.univ.biUnion childrenC_672_i0) ∪ commonEnvelope childrenD_672_i0).erase (2, 1) := by
  exact required_eq_combination childrenC_672_i0 childrenD_672_i0 (2, 1) required_672_i0
    (by decide +kernel) child_required_sub_672_i0 common_sub_672_i0 required_origin_672_i0
theorem envelope_origin_672_i0 : ∀ x ∈ envelope_672_i0,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_672_i0 j := by decide +kernel
theorem envelope_exact_672_i0 : envelope_672_i0 =
    insert (2, 1) (Finset.univ.biUnion childrenD_672_i0) := by
  exact envelope_eq_combination childrenD_672_i0 (2, 1) envelope_672_i0
    pivot_mem_672_i0 child_envelope_sub_672_i0 envelope_origin_672_i0
def checked_672_i0 : CheckedCard where
  required := required_672_i0
  envelope := envelope_672_i0
  height := height_672_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_672_i0
def height_672 : ℕ := 5
def childrenH_672 : Fin 3 → ℕ := ![height_34, height_305, height_672_i0]
theorem height_exact_672 : height_672 = 1 + Finset.univ.sup childrenH_672 := by decide +kernel
theorem required_origin_672 : ∀ x ∈ required_672,
    (∃ j, x ∈ childrenC_672 j) ∨ ∀ j, x ∈ childrenD_672 j := by decide +kernel
theorem required_exact_672 : required_672 =
    ((Finset.univ.biUnion childrenC_672) ∪ commonEnvelope childrenD_672).erase (2, 2) := by
  exact required_eq_combination childrenC_672 childrenD_672 (2, 2) required_672
    (by decide +kernel) child_required_sub_672 common_sub_672 required_origin_672
theorem envelope_origin_672 : ∀ x ∈ envelope_672,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_672 j := by decide +kernel
theorem envelope_exact_672 : envelope_672 =
    insert (2, 2) (Finset.univ.biUnion childrenD_672) := by
  exact envelope_eq_combination childrenD_672 (2, 2) envelope_672
    pivot_mem_672 child_envelope_sub_672 envelope_origin_672
def checked_672 : CheckedCard where
  required := required_672
  envelope := envelope_672
  height := height_672
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_672
end SnakyPrototype.Certificate21

end OAI
