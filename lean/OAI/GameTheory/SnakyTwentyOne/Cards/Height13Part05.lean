import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_675_i0 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i0 : Finset Cell := ⟨(([(3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 3), (8, 4), (8, 5), (8, 7), (8, 8), (8, 9), (8, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i0 : Fin 5 → Finset Cell := ![(placed21 2 (8, 3) required_12), (placed21 0 (4, 3) required_356), (placed21 0 (4, 3) required_364), (placed21 2 (8, 3) required_367), (placed21 6 (8, 9) required_671)]
def childrenD_675_i0 : Fin 5 → Finset Cell := ![(placed21 2 (8, 3) envelope_12), (placed21 0 (4, 3) envelope_356), (placed21 0 (4, 3) envelope_364), (placed21 2 (8, 3) envelope_367), (placed21 6 (8, 9) envelope_671)]
theorem common_sub_675_i0 : commonEnvelope childrenD_675_i0 ⊆ insert (7, 7) required_675_i0 := by decide +kernel
theorem child_required_sub_675_i0 : ∀ j, childrenC_675_i0 j ⊆ insert (7, 7) required_675_i0 := by decide +kernel
theorem child_envelope_sub_675_i0 : ∀ j, childrenD_675_i0 j ⊆ envelope_675_i0 := by decide +kernel
theorem pivot_mem_675_i0 : (7, 7) ∈ envelope_675_i0 := by decide +kernel
theorem children_work_675_i0 : ∀ j, Template HasSnaky 7 (childrenC_675_i0 j) (childrenD_675_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_356 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_364 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 2 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_671 6 (8, 9)).mono (by decide +kernel)
theorem row_works_675_i0 : Template HasSnaky 8 required_675_i0 envelope_675_i0 := by
  refine compose HasSnaky 7 childrenC_675_i0 childrenD_675_i0 children_work_675_i0 (7, 7)
    required_675_i0 envelope_675_i0 pivot_mem_675_i0 child_required_sub_675_i0 child_envelope_sub_675_i0 ?_
  intro b hb
  exact common_sub_675_i0 (mem_commonEnvelope childrenD_675_i0 b hb)
def required_675_i1 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i1 : Finset Cell := ⟨(([(3, 2), (3, 4), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 5), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 4), (9, 6), (9, 7), (9, 8), (10, 6), (10, 7), (10, 8), (11, 6), (11, 7), (11, 8), (12, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i1 : Fin 6 → Finset Cell := ![(placed21 0 (5, 2) required_188), (placed21 6 (9, 8) required_190), (placed21 2 (8, 2) required_441), (placed21 2 (8, 2) required_442), (placed21 6 (8, 7) required_514), (placed21 0 (4, 3) required_667)]
def childrenD_675_i1 : Fin 6 → Finset Cell := ![(placed21 0 (5, 2) envelope_188), (placed21 6 (9, 8) envelope_190), (placed21 2 (8, 2) envelope_441), (placed21 2 (8, 2) envelope_442), (placed21 6 (8, 7) envelope_514), (placed21 0 (4, 3) envelope_667)]
theorem common_sub_675_i1 : commonEnvelope childrenD_675_i1 ⊆ insert (7, 4) required_675_i1 := by decide +kernel
theorem child_required_sub_675_i1 : ∀ j, childrenC_675_i1 j ⊆ insert (7, 4) required_675_i1 := by decide +kernel
theorem child_envelope_sub_675_i1 : ∀ j, childrenD_675_i1 j ⊆ envelope_675_i1 := by decide +kernel
theorem pivot_mem_675_i1 : (7, 4) ∈ envelope_675_i1 := by decide +kernel
theorem children_work_675_i1 : ∀ j, Template HasSnaky 9 (childrenC_675_i1 j) (childrenD_675_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 0 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_190 6 (9, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_441 2 (8, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_442 2 (8, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_514 6 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_667 0 (4, 3)).mono (by decide +kernel)
theorem row_works_675_i1 : Template HasSnaky 10 required_675_i1 envelope_675_i1 := by
  refine compose HasSnaky 9 childrenC_675_i1 childrenD_675_i1 children_work_675_i1 (7, 4)
    required_675_i1 envelope_675_i1 pivot_mem_675_i1 child_required_sub_675_i1 child_envelope_sub_675_i1 ?_
  intro b hb
  exact common_sub_675_i1 (mem_commonEnvelope childrenD_675_i1 b hb)
def required_675_i3 : Finset Cell := ⟨(([(7, 3), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i3 : Finset Cell := ⟨(([(5, 3), (6, 1), (6, 2), (6, 3), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 4), (10, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i3 : Fin 5 → Finset Cell := ![(placed21 3 (6, 6) required_8), (placed21 7 (8, 6) required_26), (placed21 1 (5, 2) required_133), (placed21 0 (6, 1) required_186), (placed21 4 (7, 8) required_187)]
def childrenD_675_i3 : Fin 5 → Finset Cell := ![(placed21 3 (6, 6) envelope_8), (placed21 7 (8, 6) envelope_26), (placed21 1 (5, 2) envelope_133), (placed21 0 (6, 1) envelope_186), (placed21 4 (7, 8) envelope_187)]
theorem common_sub_675_i3 : commonEnvelope childrenD_675_i3 ⊆ insert (7, 4) required_675_i3 := by decide +kernel
theorem child_required_sub_675_i3 : ∀ j, childrenC_675_i3 j ⊆ insert (7, 4) required_675_i3 := by decide +kernel
theorem child_envelope_sub_675_i3 : ∀ j, childrenD_675_i3 j ⊆ envelope_675_i3 := by decide +kernel
theorem pivot_mem_675_i3 : (7, 4) ∈ envelope_675_i3 := by decide +kernel
theorem children_work_675_i3 : ∀ j, Template HasSnaky 5 (childrenC_675_i3 j) (childrenD_675_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 3 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 1 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_186 0 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_187 4 (7, 8)).mono (by decide +kernel)
theorem row_works_675_i3 : Template HasSnaky 6 required_675_i3 envelope_675_i3 := by
  refine compose HasSnaky 5 childrenC_675_i3 childrenD_675_i3 children_work_675_i3 (7, 4)
    required_675_i3 envelope_675_i3 pivot_mem_675_i3 child_required_sub_675_i3 child_envelope_sub_675_i3 ?_
  intro b hb
  exact common_sub_675_i3 (mem_commonEnvelope childrenD_675_i3 b hb)
def required_675_i5 : Finset Cell := ⟨(([(6, 6), (7, 3), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i5 : Finset Cell := ⟨(([(4, 3), (5, 3), (6, 2), (6, 3), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (9, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i5 : Fin 2 → Finset Cell := ![(placed21 5 (7, 3) required_5), (placed21 5 (9, 2) required_179)]
def childrenD_675_i5 : Fin 2 → Finset Cell := ![(placed21 5 (7, 3) envelope_5), (placed21 5 (9, 2) envelope_179)]
theorem common_sub_675_i5 : commonEnvelope childrenD_675_i5 ⊆ insert (7, 4) required_675_i5 := by decide +kernel
theorem child_required_sub_675_i5 : ∀ j, childrenC_675_i5 j ⊆ insert (7, 4) required_675_i5 := by decide +kernel
theorem child_envelope_sub_675_i5 : ∀ j, childrenD_675_i5 j ⊆ envelope_675_i5 := by decide +kernel
theorem pivot_mem_675_i5 : (7, 4) ∈ envelope_675_i5 := by decide +kernel
theorem children_work_675_i5 : ∀ j, Template HasSnaky 5 (childrenC_675_i5 j) (childrenD_675_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 5 (9, 2)).mono (by decide +kernel)
theorem row_works_675_i5 : Template HasSnaky 6 required_675_i5 envelope_675_i5 := by
  refine compose HasSnaky 5 childrenC_675_i5 childrenD_675_i5 children_work_675_i5 (7, 4)
    required_675_i5 envelope_675_i5 pivot_mem_675_i5 child_required_sub_675_i5 child_envelope_sub_675_i5 ?_
  intro b hb
  exact common_sub_675_i5 (mem_commonEnvelope childrenD_675_i5 b hb)
def required_675_i6 : Finset Cell := ⟨(([(4, 5), (4, 6), (6, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i6 : Finset Cell := ⟨(([(3, 4), (3, 6), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (6, 5), (6, 6), (7, 5), (7, 6), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i6 : Fin 3 → Finset Cell := ![(placed21 7 (8, 6) required_22), (placed21 5 (8, 5) required_34), (placed21 7 (8, 6) required_305)]
def childrenD_675_i6 : Fin 3 → Finset Cell := ![(placed21 7 (8, 6) envelope_22), (placed21 5 (8, 5) envelope_34), (placed21 7 (8, 6) envelope_305)]
theorem common_sub_675_i6 : commonEnvelope childrenD_675_i6 ⊆ insert (6, 5) required_675_i6 := by decide +kernel
theorem child_required_sub_675_i6 : ∀ j, childrenC_675_i6 j ⊆ insert (6, 5) required_675_i6 := by decide +kernel
theorem child_envelope_sub_675_i6 : ∀ j, childrenD_675_i6 j ⊆ envelope_675_i6 := by decide +kernel
theorem pivot_mem_675_i6 : (6, 5) ∈ envelope_675_i6 := by decide +kernel
theorem children_work_675_i6 : ∀ j, Template HasSnaky 4 (childrenC_675_i6 j) (childrenD_675_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_34 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_305 7 (8, 6)).mono (by decide +kernel)
theorem row_works_675_i6 : Template HasSnaky 5 required_675_i6 envelope_675_i6 := by
  refine compose HasSnaky 4 childrenC_675_i6 childrenD_675_i6 children_work_675_i6 (6, 5)
    required_675_i6 envelope_675_i6 pivot_mem_675_i6 child_required_sub_675_i6 child_envelope_sub_675_i6 ?_
  intro b hb
  exact common_sub_675_i6 (mem_commonEnvelope childrenD_675_i6 b hb)
def required_675_i4 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 3), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i4 : Finset Cell := ⟨(([(3, 4), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i4 : Fin 2 → Finset Cell := ![required_675_i5, required_675_i6]
def childrenD_675_i4 : Fin 2 → Finset Cell := ![envelope_675_i5, envelope_675_i6]
theorem common_sub_675_i4 : commonEnvelope childrenD_675_i4 ⊆ insert (6, 6) required_675_i4 := by decide +kernel
theorem child_required_sub_675_i4 : ∀ j, childrenC_675_i4 j ⊆ insert (6, 6) required_675_i4 := by decide +kernel
theorem child_envelope_sub_675_i4 : ∀ j, childrenD_675_i4 j ⊆ envelope_675_i4 := by decide +kernel
theorem pivot_mem_675_i4 : (6, 6) ∈ envelope_675_i4 := by decide +kernel
theorem children_work_675_i4 : ∀ j, Template HasSnaky 6 (childrenC_675_i4 j) (childrenD_675_i4 j) := by
  intro j
  fin_cases j
  · exact row_works_675_i5.mono (by decide +kernel)
  · exact row_works_675_i6.mono (by decide +kernel)
theorem row_works_675_i4 : Template HasSnaky 7 required_675_i4 envelope_675_i4 := by
  refine compose HasSnaky 6 childrenC_675_i4 childrenD_675_i4 children_work_675_i4 (6, 6)
    required_675_i4 envelope_675_i4 pivot_mem_675_i4 child_required_sub_675_i4 child_envelope_sub_675_i4 ?_
  intro b hb
  exact common_sub_675_i4 (mem_commonEnvelope childrenD_675_i4 b hb)
def required_675_i2 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i2 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 2), (9, 3), (9, 4), (10, 2), (10, 3), (10, 4), (11, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i2 : Fin 5 → Finset Cell := ![(placed21 4 (6, 8) required_304), (placed21 6 (8, 7) required_672), required_675_i3, (placed21 3 (1, 7) required_674), required_675_i4]
def childrenD_675_i2 : Fin 5 → Finset Cell := ![(placed21 4 (6, 8) envelope_304), (placed21 6 (8, 7) envelope_672), envelope_675_i3, (placed21 3 (1, 7) envelope_674), envelope_675_i4]
theorem common_sub_675_i2 : commonEnvelope childrenD_675_i2 ⊆ insert (7, 3) required_675_i2 := by decide +kernel
theorem child_required_sub_675_i2 : ∀ j, childrenC_675_i2 j ⊆ insert (7, 3) required_675_i2 := by decide +kernel
theorem child_envelope_sub_675_i2 : ∀ j, childrenD_675_i2 j ⊆ envelope_675_i2 := by decide +kernel
theorem pivot_mem_675_i2 : (7, 3) ∈ envelope_675_i2 := by decide +kernel
theorem children_work_675_i2 : ∀ j, Template HasSnaky 10 (childrenC_675_i2 j) (childrenD_675_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_304 4 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_672 6 (8, 7)).mono (by decide +kernel)
  · exact row_works_675_i3.mono (by decide +kernel)
  · exact (placed21_template row_works_674 3 (1, 7)).mono (by decide +kernel)
  · exact row_works_675_i4.mono (by decide +kernel)
theorem row_works_675_i2 : Template HasSnaky 11 required_675_i2 envelope_675_i2 := by
  refine compose HasSnaky 10 childrenC_675_i2 childrenD_675_i2 children_work_675_i2 (7, 3)
    required_675_i2 envelope_675_i2 pivot_mem_675_i2 child_required_sub_675_i2 child_envelope_sub_675_i2 ?_
  intro b hb
  exact common_sub_675_i2 (mem_commonEnvelope childrenD_675_i2 b hb)
def required_675_i7 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i7 : Finset Cell := ⟨(([(3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 7), (9, 8), (10, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i7 : Fin 4 → Finset Cell := ![(placed21 0 (5, 3) required_190), (placed21 2 (9, 3) required_190), (placed21 0 (4, 3) required_363), (placed21 6 (8, 9) required_671)]
def childrenD_675_i7 : Fin 4 → Finset Cell := ![(placed21 0 (5, 3) envelope_190), (placed21 2 (9, 3) envelope_190), (placed21 0 (4, 3) envelope_363), (placed21 6 (8, 9) envelope_671)]
theorem common_sub_675_i7 : commonEnvelope childrenD_675_i7 ⊆ insert (7, 7) required_675_i7 := by decide +kernel
theorem child_required_sub_675_i7 : ∀ j, childrenC_675_i7 j ⊆ insert (7, 7) required_675_i7 := by decide +kernel
theorem child_envelope_sub_675_i7 : ∀ j, childrenD_675_i7 j ⊆ envelope_675_i7 := by decide +kernel
theorem pivot_mem_675_i7 : (7, 7) ∈ envelope_675_i7 := by decide +kernel
theorem children_work_675_i7 : ∀ j, Template HasSnaky 7 (childrenC_675_i7 j) (childrenD_675_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_190 0 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_190 2 (9, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_363 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_671 6 (8, 9)).mono (by decide +kernel)
theorem row_works_675_i7 : Template HasSnaky 8 required_675_i7 envelope_675_i7 := by
  refine compose HasSnaky 7 childrenC_675_i7 childrenD_675_i7 children_work_675_i7 (7, 7)
    required_675_i7 envelope_675_i7 pivot_mem_675_i7 child_required_sub_675_i7 child_envelope_sub_675_i7 ?_
  intro b hb
  exact common_sub_675_i7 (mem_commonEnvelope childrenD_675_i7 b hb)
def required_675_i8 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i8 : Finset Cell := ⟨(([(3, 6), (4, 5), (4, 6), (5, 5), (5, 6), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (11, 4), (11, 5), (11, 6), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i8 : Fin 3 → Finset Cell := ![(placed21 5 (8, 5) required_34), (placed21 3 (3, 6) required_97), (placed21 4 (5, 10) required_535)]
def childrenD_675_i8 : Fin 3 → Finset Cell := ![(placed21 5 (8, 5) envelope_34), (placed21 3 (3, 6) envelope_97), (placed21 4 (5, 10) envelope_535)]
theorem common_sub_675_i8 : commonEnvelope childrenD_675_i8 ⊆ insert (6, 5) required_675_i8 := by decide +kernel
theorem child_required_sub_675_i8 : ∀ j, childrenC_675_i8 j ⊆ insert (6, 5) required_675_i8 := by decide +kernel
theorem child_envelope_sub_675_i8 : ∀ j, childrenD_675_i8 j ⊆ envelope_675_i8 := by decide +kernel
theorem pivot_mem_675_i8 : (6, 5) ∈ envelope_675_i8 := by decide +kernel
theorem children_work_675_i8 : ∀ j, Template HasSnaky 10 (childrenC_675_i8 j) (childrenD_675_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_97 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_535 4 (5, 10)).mono (by decide +kernel)
theorem row_works_675_i8 : Template HasSnaky 11 required_675_i8 envelope_675_i8 := by
  refine compose HasSnaky 10 childrenC_675_i8 childrenD_675_i8 children_work_675_i8 (6, 5)
    required_675_i8 envelope_675_i8 pivot_mem_675_i8 child_required_sub_675_i8 child_envelope_sub_675_i8 ?_
  intro b hb
  exact common_sub_675_i8 (mem_commonEnvelope childrenD_675_i8 b hb)
def required_675_i10 : Finset Cell := ⟨(([(4, 5), (7, 3), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i10 : Finset Cell := ⟨(([(3, 2), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (8, 2), (8, 3), (8, 4), (8, 6), (8, 7), (9, 2), (9, 3), (9, 4), (10, 2), (10, 3), (10, 4), (11, 2), (11, 3), (11, 4), (12, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i10 : Fin 2 → Finset Cell := ![(placed21 3 (3, 6) required_321), (placed21 5 (8, 3) required_354)]
def childrenD_675_i10 : Fin 2 → Finset Cell := ![(placed21 3 (3, 6) envelope_321), (placed21 5 (8, 3) envelope_354)]
theorem common_sub_675_i10 : commonEnvelope childrenD_675_i10 ⊆ insert (7, 4) required_675_i10 := by decide +kernel
theorem child_required_sub_675_i10 : ∀ j, childrenC_675_i10 j ⊆ insert (7, 4) required_675_i10 := by decide +kernel
theorem child_envelope_sub_675_i10 : ∀ j, childrenD_675_i10 j ⊆ envelope_675_i10 := by decide +kernel
theorem pivot_mem_675_i10 : (7, 4) ∈ envelope_675_i10 := by decide +kernel
theorem children_work_675_i10 : ∀ j, Template HasSnaky 8 (childrenC_675_i10 j) (childrenD_675_i10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_321 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_354 5 (8, 3)).mono (by decide +kernel)
theorem row_works_675_i10 : Template HasSnaky 9 required_675_i10 envelope_675_i10 := by
  refine compose HasSnaky 8 childrenC_675_i10 childrenD_675_i10 children_work_675_i10 (7, 4)
    required_675_i10 envelope_675_i10 pivot_mem_675_i10 child_required_sub_675_i10 child_envelope_sub_675_i10 ?_
  intro b hb
  exact common_sub_675_i10 (mem_commonEnvelope childrenD_675_i10 b hb)
def required_675_i9 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675_i9 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 2), (9, 3), (9, 4), (9, 5), (10, 2), (10, 3), (10, 4), (11, 2), (11, 3), (11, 4), (12, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675_i9 : Fin 6 → Finset Cell := ![(placed21 3 (3, 7) required_328), (placed21 3 (3, 7) required_330), (placed21 4 (4, 7) required_384), (placed21 6 (8, 7) required_672), (placed21 3 (1, 7) required_674), required_675_i10]
def childrenD_675_i9 : Fin 6 → Finset Cell := ![(placed21 3 (3, 7) envelope_328), (placed21 3 (3, 7) envelope_330), (placed21 4 (4, 7) envelope_384), (placed21 6 (8, 7) envelope_672), (placed21 3 (1, 7) envelope_674), envelope_675_i10]
theorem common_sub_675_i9 : commonEnvelope childrenD_675_i9 ⊆ insert (7, 3) required_675_i9 := by decide +kernel
theorem child_required_sub_675_i9 : ∀ j, childrenC_675_i9 j ⊆ insert (7, 3) required_675_i9 := by decide +kernel
theorem child_envelope_sub_675_i9 : ∀ j, childrenD_675_i9 j ⊆ envelope_675_i9 := by decide +kernel
theorem pivot_mem_675_i9 : (7, 3) ∈ envelope_675_i9 := by decide +kernel
theorem children_work_675_i9 : ∀ j, Template HasSnaky 10 (childrenC_675_i9 j) (childrenD_675_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_328 3 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_330 3 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_384 4 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_672 6 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_674 3 (1, 7)).mono (by decide +kernel)
  · exact row_works_675_i10.mono (by decide +kernel)
theorem row_works_675_i9 : Template HasSnaky 11 required_675_i9 envelope_675_i9 := by
  refine compose HasSnaky 10 childrenC_675_i9 childrenD_675_i9 children_work_675_i9 (7, 3)
    required_675_i9 envelope_675_i9 pivot_mem_675_i9 child_required_sub_675_i9 child_envelope_sub_675_i9 ?_
  intro b hb
  exact common_sub_675_i9 (mem_commonEnvelope childrenD_675_i9 b hb)
def required_675 : Finset Cell := ⟨(([(4, 5), (4, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_675 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 2), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 9), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (12, 4), (12, 6), (12, 7), (12, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_675 : Fin 9 → Finset Cell := ![(placed21 0 (6, 1) required_459), (placed21 0 (2, 2) required_618), (placed21 2 (10, 2) required_629), required_675_i0, required_675_i1, required_675_i2, required_675_i7, required_675_i8, required_675_i9]
def childrenD_675 : Fin 9 → Finset Cell := ![(placed21 0 (6, 1) envelope_459), (placed21 0 (2, 2) envelope_618), (placed21 2 (10, 2) envelope_629), envelope_675_i0, envelope_675_i1, envelope_675_i2, envelope_675_i7, envelope_675_i8, envelope_675_i9]
theorem common_sub_675 : commonEnvelope childrenD_675 ⊆ insert (7, 6) required_675 := by decide +kernel
theorem child_required_sub_675 : ∀ j, childrenC_675 j ⊆ insert (7, 6) required_675 := by decide +kernel
theorem child_envelope_sub_675 : ∀ j, childrenD_675 j ⊆ envelope_675 := by decide +kernel
theorem pivot_mem_675 : (7, 6) ∈ envelope_675 := by decide +kernel
theorem children_work_675 : ∀ j, Template HasSnaky 12 (childrenC_675 j) (childrenD_675 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 0 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_618 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_629 2 (10, 2)).mono (by decide +kernel)
  · exact row_works_675_i0.mono (by decide +kernel)
  · exact row_works_675_i1.mono (by decide +kernel)
  · exact row_works_675_i2.mono (by decide +kernel)
  · exact row_works_675_i7.mono (by decide +kernel)
  · exact row_works_675_i8.mono (by decide +kernel)
  · exact row_works_675_i9.mono (by decide +kernel)
theorem row_works_675 : Template HasSnaky 13 required_675 envelope_675 := by
  refine compose HasSnaky 12 childrenC_675 childrenD_675 children_work_675 (7, 6)
    required_675 envelope_675 pivot_mem_675 child_required_sub_675 child_envelope_sub_675 ?_
  intro b hb
  exact common_sub_675 (mem_commonEnvelope childrenD_675 b hb)
def required_690_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_690_i0 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_690_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 2) required_39), (placed21 0 (2, 2) required_80), (placed21 1 (0, 2) required_463)]
def childrenD_690_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 2) envelope_39), (placed21 0 (2, 2) envelope_80), (placed21 1 (0, 2) envelope_463)]
theorem common_sub_690_i0 : commonEnvelope childrenD_690_i0 ⊆ insert (3, 6) required_690_i0 := by decide +kernel
theorem child_required_sub_690_i0 : ∀ j, childrenC_690_i0 j ⊆ insert (3, 6) required_690_i0 := by decide +kernel
theorem child_envelope_sub_690_i0 : ∀ j, childrenD_690_i0 j ⊆ envelope_690_i0 := by decide +kernel
theorem pivot_mem_690_i0 : (3, 6) ∈ envelope_690_i0 := by decide +kernel
theorem children_work_690_i0 : ∀ j, Template HasSnaky 11 (childrenC_690_i0 j) (childrenD_690_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_39 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_80 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_463 1 (0, 2)).mono (by decide +kernel)
theorem row_works_690_i0 : Template HasSnaky 12 required_690_i0 envelope_690_i0 := by
  refine compose HasSnaky 11 childrenC_690_i0 childrenD_690_i0 children_work_690_i0 (3, 6)
    required_690_i0 envelope_690_i0 pivot_mem_690_i0 child_required_sub_690_i0 child_envelope_sub_690_i0 ?_
  intro b hb
  exact common_sub_690_i0 (mem_commonEnvelope childrenD_690_i0 b hb)
def required_690 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_690 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 2), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_690 : Fin 3 → Finset Cell := ![(placed21 1 (2, 3) required_21), (placed21 6 (5, 6) required_56), required_690_i0]
def childrenD_690 : Fin 3 → Finset Cell := ![(placed21 1 (2, 3) envelope_21), (placed21 6 (5, 6) envelope_56), envelope_690_i0]
theorem common_sub_690 : commonEnvelope childrenD_690 ⊆ insert (3, 4) required_690 := by decide +kernel
theorem child_required_sub_690 : ∀ j, childrenC_690 j ⊆ insert (3, 4) required_690 := by decide +kernel
theorem child_envelope_sub_690 : ∀ j, childrenD_690 j ⊆ envelope_690 := by decide +kernel
theorem pivot_mem_690 : (3, 4) ∈ envelope_690 := by decide +kernel
theorem children_work_690 : ∀ j, Template HasSnaky 12 (childrenC_690 j) (childrenD_690 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 6 (5, 6)).mono (by decide +kernel)
  · exact row_works_690_i0.mono (by decide +kernel)
theorem row_works_690 : Template HasSnaky 13 required_690 envelope_690 := by
  refine compose HasSnaky 12 childrenC_690 childrenD_690 children_work_690 (3, 4)
    required_690 envelope_690 pivot_mem_690 child_required_sub_690 child_envelope_sub_690 ?_
  intro b hb
  exact common_sub_690 (mem_commonEnvelope childrenD_690 b hb)
def required_692_i1 : Finset Cell := ⟨(([(3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_692_i1 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_692_i1 : Fin 7 → Finset Cell := ![(placed21 4 (2, 7) required_13), (placed21 4 (2, 7) required_14), (placed21 3 (0, 6) required_118), (placed21 2 (4, 1) required_192), (placed21 0 (2, 1) required_193), (placed21 0 (1, 0) required_396), (placed21 7 (6, 6) required_435)]
def childrenD_692_i1 : Fin 7 → Finset Cell := ![(placed21 4 (2, 7) envelope_13), (placed21 4 (2, 7) envelope_14), (placed21 3 (0, 6) envelope_118), (placed21 2 (4, 1) envelope_192), (placed21 0 (2, 1) envelope_193), (placed21 0 (1, 0) envelope_396), (placed21 7 (6, 6) envelope_435)]
theorem common_sub_692_i1 : commonEnvelope childrenD_692_i1 ⊆ insert (3, 3) required_692_i1 := by decide +kernel
theorem child_required_sub_692_i1 : ∀ j, childrenC_692_i1 j ⊆ insert (3, 3) required_692_i1 := by decide +kernel
theorem child_envelope_sub_692_i1 : ∀ j, childrenD_692_i1 j ⊆ envelope_692_i1 := by decide +kernel
theorem pivot_mem_692_i1 : (3, 3) ∈ envelope_692_i1 := by decide +kernel
theorem children_work_692_i1 : ∀ j, Template HasSnaky 9 (childrenC_692_i1 j) (childrenD_692_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_118 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_192 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_193 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_396 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 7 (6, 6)).mono (by decide +kernel)
theorem row_works_692_i1 : Template HasSnaky 10 required_692_i1 envelope_692_i1 := by
  refine compose HasSnaky 9 childrenC_692_i1 childrenD_692_i1 children_work_692_i1 (3, 3)
    required_692_i1 envelope_692_i1 pivot_mem_692_i1 child_required_sub_692_i1 child_envelope_sub_692_i1 ?_
  intro b hb
  exact common_sub_692_i1 (mem_commonEnvelope childrenD_692_i1 b hb)
def required_692_i2 : Finset Cell := ⟨(([(0, 5), (1, 5), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_692_i2 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_692_i2 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) required_2), (placed21 4 (1, 7) required_509)]
def childrenD_692_i2 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) envelope_2), (placed21 4 (1, 7) envelope_509)]
theorem common_sub_692_i2 : commonEnvelope childrenD_692_i2 ⊆ insert (4, 4) required_692_i2 := by decide +kernel
theorem child_required_sub_692_i2 : ∀ j, childrenC_692_i2 j ⊆ insert (4, 4) required_692_i2 := by decide +kernel
theorem child_envelope_sub_692_i2 : ∀ j, childrenD_692_i2 j ⊆ envelope_692_i2 := by decide +kernel
theorem pivot_mem_692_i2 : (4, 4) ∈ envelope_692_i2 := by decide +kernel
theorem children_work_692_i2 : ∀ j, Template HasSnaky 10 (childrenC_692_i2 j) (childrenD_692_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_509 4 (1, 7)).mono (by decide +kernel)
theorem row_works_692_i2 : Template HasSnaky 11 required_692_i2 envelope_692_i2 := by
  refine compose HasSnaky 10 childrenC_692_i2 childrenD_692_i2 children_work_692_i2 (4, 4)
    required_692_i2 envelope_692_i2 pivot_mem_692_i2 child_required_sub_692_i2 child_envelope_sub_692_i2 ?_
  intro b hb
  exact common_sub_692_i2 (mem_commonEnvelope childrenD_692_i2 b hb)
def required_692_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_692_i0 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 7), (1, 2), (1, 3), (1, 5), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_692_i0 : Fin 8 → Finset Cell := ![(placed21 0 (0, 2) required_110), (placed21 0 (0, 2) required_119), (placed21 4 (1, 8) required_399), (placed21 0 (0, 1) required_430), (placed21 0 (0, 3) required_461), (placed21 4 (1, 8) required_475), required_692_i1, required_692_i2]
def childrenD_692_i0 : Fin 8 → Finset Cell := ![(placed21 0 (0, 2) envelope_110), (placed21 0 (0, 2) envelope_119), (placed21 4 (1, 8) envelope_399), (placed21 0 (0, 1) envelope_430), (placed21 0 (0, 3) envelope_461), (placed21 4 (1, 8) envelope_475), envelope_692_i1, envelope_692_i2]
theorem common_sub_692_i0 : commonEnvelope childrenD_692_i0 ⊆ insert (3, 4) required_692_i0 := by decide +kernel
theorem child_required_sub_692_i0 : ∀ j, childrenC_692_i0 j ⊆ insert (3, 4) required_692_i0 := by decide +kernel
theorem child_envelope_sub_692_i0 : ∀ j, childrenD_692_i0 j ⊆ envelope_692_i0 := by decide +kernel
theorem pivot_mem_692_i0 : (3, 4) ∈ envelope_692_i0 := by decide +kernel
theorem children_work_692_i0 : ∀ j, Template HasSnaky 11 (childrenC_692_i0 j) (childrenD_692_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_110 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_119 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_399 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_430 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_461 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_475 4 (1, 8)).mono (by decide +kernel)
  · exact row_works_692_i1.mono (by decide +kernel)
  · exact row_works_692_i2.mono (by decide +kernel)
theorem row_works_692_i0 : Template HasSnaky 12 required_692_i0 envelope_692_i0 := by
  refine compose HasSnaky 11 childrenC_692_i0 childrenD_692_i0 children_work_692_i0 (3, 4)
    required_692_i0 envelope_692_i0 pivot_mem_692_i0 child_required_sub_692_i0 child_envelope_sub_692_i0 ?_
  intro b hb
  exact common_sub_692_i0 (mem_commonEnvelope childrenD_692_i0 b hb)
def required_692 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_692 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (0, 7), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_692 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) required_5), required_692_i0]
def childrenD_692 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) envelope_5), envelope_692_i0]
theorem common_sub_692 : commonEnvelope childrenD_692 ⊆ insert (1, 5) required_692 := by decide +kernel
theorem child_required_sub_692 : ∀ j, childrenC_692 j ⊆ insert (1, 5) required_692 := by decide +kernel
theorem child_envelope_sub_692 : ∀ j, childrenD_692 j ⊆ envelope_692 := by decide +kernel
theorem pivot_mem_692 : (1, 5) ∈ envelope_692 := by decide +kernel
theorem children_work_692 : ∀ j, Template HasSnaky 12 (childrenC_692 j) (childrenD_692 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_692_i0.mono (by decide +kernel)
theorem row_works_692 : Template HasSnaky 13 required_692 envelope_692 := by
  refine compose HasSnaky 12 childrenC_692 childrenD_692 children_work_692 (1, 5)
    required_692 envelope_692 pivot_mem_692 child_required_sub_692 child_envelope_sub_692 ?_
  intro b hb
  exact common_sub_692 (mem_commonEnvelope childrenD_692 b hb)
def height_675_i0 : ℕ := 8
def childrenH_675_i0 : Fin 5 → ℕ := ![height_12, height_356, height_364, height_367, height_671]
theorem height_exact_675_i0 : height_675_i0 = 1 + Finset.univ.sup childrenH_675_i0 := by decide +kernel
theorem required_origin_675_i0 : ∀ x ∈ required_675_i0,
    (∃ j, x ∈ childrenC_675_i0 j) ∨ ∀ j, x ∈ childrenD_675_i0 j := by decide +kernel
theorem required_exact_675_i0 : required_675_i0 =
    ((Finset.univ.biUnion childrenC_675_i0) ∪ commonEnvelope childrenD_675_i0).erase (7, 7) := by
  exact required_eq_combination childrenC_675_i0 childrenD_675_i0 (7, 7) required_675_i0
    (by decide +kernel) child_required_sub_675_i0 common_sub_675_i0 required_origin_675_i0
theorem envelope_origin_675_i0 : ∀ x ∈ envelope_675_i0,
    x = (7, 7) ∨ ∃ j, x ∈ childrenD_675_i0 j := by decide +kernel
theorem envelope_exact_675_i0 : envelope_675_i0 =
    insert (7, 7) (Finset.univ.biUnion childrenD_675_i0) := by
  exact envelope_eq_combination childrenD_675_i0 (7, 7) envelope_675_i0
    pivot_mem_675_i0 child_envelope_sub_675_i0 envelope_origin_675_i0
def checked_675_i0 : CheckedCard where
  required := required_675_i0
  envelope := envelope_675_i0
  height := height_675_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i0
def height_675_i1 : ℕ := 10
def childrenH_675_i1 : Fin 6 → ℕ := ![height_188, height_190, height_441, height_442, height_514, height_667]
theorem height_exact_675_i1 : height_675_i1 = 1 + Finset.univ.sup childrenH_675_i1 := by decide +kernel
theorem required_origin_675_i1 : ∀ x ∈ required_675_i1,
    (∃ j, x ∈ childrenC_675_i1 j) ∨ ∀ j, x ∈ childrenD_675_i1 j := by decide +kernel
theorem required_exact_675_i1 : required_675_i1 =
    ((Finset.univ.biUnion childrenC_675_i1) ∪ commonEnvelope childrenD_675_i1).erase (7, 4) := by
  exact required_eq_combination childrenC_675_i1 childrenD_675_i1 (7, 4) required_675_i1
    (by decide +kernel) child_required_sub_675_i1 common_sub_675_i1 required_origin_675_i1
theorem envelope_origin_675_i1 : ∀ x ∈ envelope_675_i1,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_675_i1 j := by decide +kernel
theorem envelope_exact_675_i1 : envelope_675_i1 =
    insert (7, 4) (Finset.univ.biUnion childrenD_675_i1) := by
  exact envelope_eq_combination childrenD_675_i1 (7, 4) envelope_675_i1
    pivot_mem_675_i1 child_envelope_sub_675_i1 envelope_origin_675_i1
def checked_675_i1 : CheckedCard where
  required := required_675_i1
  envelope := envelope_675_i1
  height := height_675_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i1
def height_675_i3 : ℕ := 6
def childrenH_675_i3 : Fin 5 → ℕ := ![height_8, height_26, height_133, height_186, height_187]
theorem height_exact_675_i3 : height_675_i3 = 1 + Finset.univ.sup childrenH_675_i3 := by decide +kernel
theorem required_origin_675_i3 : ∀ x ∈ required_675_i3,
    (∃ j, x ∈ childrenC_675_i3 j) ∨ ∀ j, x ∈ childrenD_675_i3 j := by decide +kernel
theorem required_exact_675_i3 : required_675_i3 =
    ((Finset.univ.biUnion childrenC_675_i3) ∪ commonEnvelope childrenD_675_i3).erase (7, 4) := by
  exact required_eq_combination childrenC_675_i3 childrenD_675_i3 (7, 4) required_675_i3
    (by decide +kernel) child_required_sub_675_i3 common_sub_675_i3 required_origin_675_i3
theorem envelope_origin_675_i3 : ∀ x ∈ envelope_675_i3,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_675_i3 j := by decide +kernel
theorem envelope_exact_675_i3 : envelope_675_i3 =
    insert (7, 4) (Finset.univ.biUnion childrenD_675_i3) := by
  exact envelope_eq_combination childrenD_675_i3 (7, 4) envelope_675_i3
    pivot_mem_675_i3 child_envelope_sub_675_i3 envelope_origin_675_i3
def checked_675_i3 : CheckedCard where
  required := required_675_i3
  envelope := envelope_675_i3
  height := height_675_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i3
def height_675_i5 : ℕ := 6
def childrenH_675_i5 : Fin 2 → ℕ := ![height_5, height_179]
theorem height_exact_675_i5 : height_675_i5 = 1 + Finset.univ.sup childrenH_675_i5 := by decide +kernel
theorem required_origin_675_i5 : ∀ x ∈ required_675_i5,
    (∃ j, x ∈ childrenC_675_i5 j) ∨ ∀ j, x ∈ childrenD_675_i5 j := by decide +kernel
theorem required_exact_675_i5 : required_675_i5 =
    ((Finset.univ.biUnion childrenC_675_i5) ∪ commonEnvelope childrenD_675_i5).erase (7, 4) := by
  exact required_eq_combination childrenC_675_i5 childrenD_675_i5 (7, 4) required_675_i5
    (by decide +kernel) child_required_sub_675_i5 common_sub_675_i5 required_origin_675_i5
theorem envelope_origin_675_i5 : ∀ x ∈ envelope_675_i5,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_675_i5 j := by decide +kernel
theorem envelope_exact_675_i5 : envelope_675_i5 =
    insert (7, 4) (Finset.univ.biUnion childrenD_675_i5) := by
  exact envelope_eq_combination childrenD_675_i5 (7, 4) envelope_675_i5
    pivot_mem_675_i5 child_envelope_sub_675_i5 envelope_origin_675_i5
def checked_675_i5 : CheckedCard where
  required := required_675_i5
  envelope := envelope_675_i5
  height := height_675_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i5
def height_675_i6 : ℕ := 5
def childrenH_675_i6 : Fin 3 → ℕ := ![height_22, height_34, height_305]
theorem height_exact_675_i6 : height_675_i6 = 1 + Finset.univ.sup childrenH_675_i6 := by decide +kernel
theorem required_origin_675_i6 : ∀ x ∈ required_675_i6,
    (∃ j, x ∈ childrenC_675_i6 j) ∨ ∀ j, x ∈ childrenD_675_i6 j := by decide +kernel
theorem required_exact_675_i6 : required_675_i6 =
    ((Finset.univ.biUnion childrenC_675_i6) ∪ commonEnvelope childrenD_675_i6).erase (6, 5) := by
  exact required_eq_combination childrenC_675_i6 childrenD_675_i6 (6, 5) required_675_i6
    (by decide +kernel) child_required_sub_675_i6 common_sub_675_i6 required_origin_675_i6
theorem envelope_origin_675_i6 : ∀ x ∈ envelope_675_i6,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_675_i6 j := by decide +kernel
theorem envelope_exact_675_i6 : envelope_675_i6 =
    insert (6, 5) (Finset.univ.biUnion childrenD_675_i6) := by
  exact envelope_eq_combination childrenD_675_i6 (6, 5) envelope_675_i6
    pivot_mem_675_i6 child_envelope_sub_675_i6 envelope_origin_675_i6
def checked_675_i6 : CheckedCard where
  required := required_675_i6
  envelope := envelope_675_i6
  height := height_675_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i6
def height_675_i4 : ℕ := 7
def childrenH_675_i4 : Fin 2 → ℕ := ![height_675_i5, height_675_i6]
theorem height_exact_675_i4 : height_675_i4 = 1 + Finset.univ.sup childrenH_675_i4 := by decide +kernel
theorem required_origin_675_i4 : ∀ x ∈ required_675_i4,
    (∃ j, x ∈ childrenC_675_i4 j) ∨ ∀ j, x ∈ childrenD_675_i4 j := by decide +kernel
theorem required_exact_675_i4 : required_675_i4 =
    ((Finset.univ.biUnion childrenC_675_i4) ∪ commonEnvelope childrenD_675_i4).erase (6, 6) := by
  exact required_eq_combination childrenC_675_i4 childrenD_675_i4 (6, 6) required_675_i4
    (by decide +kernel) child_required_sub_675_i4 common_sub_675_i4 required_origin_675_i4
theorem envelope_origin_675_i4 : ∀ x ∈ envelope_675_i4,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_675_i4 j := by decide +kernel
theorem envelope_exact_675_i4 : envelope_675_i4 =
    insert (6, 6) (Finset.univ.biUnion childrenD_675_i4) := by
  exact envelope_eq_combination childrenD_675_i4 (6, 6) envelope_675_i4
    pivot_mem_675_i4 child_envelope_sub_675_i4 envelope_origin_675_i4
def checked_675_i4 : CheckedCard where
  required := required_675_i4
  envelope := envelope_675_i4
  height := height_675_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i4
def height_675_i2 : ℕ := 11
def childrenH_675_i2 : Fin 5 → ℕ := ![height_304, height_672, height_675_i3, height_674, height_675_i4]
theorem height_exact_675_i2 : height_675_i2 = 1 + Finset.univ.sup childrenH_675_i2 := by decide +kernel
theorem required_origin_675_i2 : ∀ x ∈ required_675_i2,
    (∃ j, x ∈ childrenC_675_i2 j) ∨ ∀ j, x ∈ childrenD_675_i2 j := by decide +kernel
theorem required_exact_675_i2 : required_675_i2 =
    ((Finset.univ.biUnion childrenC_675_i2) ∪ commonEnvelope childrenD_675_i2).erase (7, 3) := by
  exact required_eq_combination childrenC_675_i2 childrenD_675_i2 (7, 3) required_675_i2
    (by decide +kernel) child_required_sub_675_i2 common_sub_675_i2 required_origin_675_i2
theorem envelope_origin_675_i2 : ∀ x ∈ envelope_675_i2,
    x = (7, 3) ∨ ∃ j, x ∈ childrenD_675_i2 j := by decide +kernel
theorem envelope_exact_675_i2 : envelope_675_i2 =
    insert (7, 3) (Finset.univ.biUnion childrenD_675_i2) := by
  exact envelope_eq_combination childrenD_675_i2 (7, 3) envelope_675_i2
    pivot_mem_675_i2 child_envelope_sub_675_i2 envelope_origin_675_i2
def checked_675_i2 : CheckedCard where
  required := required_675_i2
  envelope := envelope_675_i2
  height := height_675_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i2
def height_675_i7 : ℕ := 8
def childrenH_675_i7 : Fin 4 → ℕ := ![height_190, height_190, height_363, height_671]
theorem height_exact_675_i7 : height_675_i7 = 1 + Finset.univ.sup childrenH_675_i7 := by decide +kernel
theorem required_origin_675_i7 : ∀ x ∈ required_675_i7,
    (∃ j, x ∈ childrenC_675_i7 j) ∨ ∀ j, x ∈ childrenD_675_i7 j := by decide +kernel
theorem required_exact_675_i7 : required_675_i7 =
    ((Finset.univ.biUnion childrenC_675_i7) ∪ commonEnvelope childrenD_675_i7).erase (7, 7) := by
  exact required_eq_combination childrenC_675_i7 childrenD_675_i7 (7, 7) required_675_i7
    (by decide +kernel) child_required_sub_675_i7 common_sub_675_i7 required_origin_675_i7
theorem envelope_origin_675_i7 : ∀ x ∈ envelope_675_i7,
    x = (7, 7) ∨ ∃ j, x ∈ childrenD_675_i7 j := by decide +kernel
theorem envelope_exact_675_i7 : envelope_675_i7 =
    insert (7, 7) (Finset.univ.biUnion childrenD_675_i7) := by
  exact envelope_eq_combination childrenD_675_i7 (7, 7) envelope_675_i7
    pivot_mem_675_i7 child_envelope_sub_675_i7 envelope_origin_675_i7
def checked_675_i7 : CheckedCard where
  required := required_675_i7
  envelope := envelope_675_i7
  height := height_675_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i7
def height_675_i8 : ℕ := 11
def childrenH_675_i8 : Fin 3 → ℕ := ![height_34, height_97, height_535]
theorem height_exact_675_i8 : height_675_i8 = 1 + Finset.univ.sup childrenH_675_i8 := by decide +kernel
theorem required_origin_675_i8 : ∀ x ∈ required_675_i8,
    (∃ j, x ∈ childrenC_675_i8 j) ∨ ∀ j, x ∈ childrenD_675_i8 j := by decide +kernel
theorem required_exact_675_i8 : required_675_i8 =
    ((Finset.univ.biUnion childrenC_675_i8) ∪ commonEnvelope childrenD_675_i8).erase (6, 5) := by
  exact required_eq_combination childrenC_675_i8 childrenD_675_i8 (6, 5) required_675_i8
    (by decide +kernel) child_required_sub_675_i8 common_sub_675_i8 required_origin_675_i8
theorem envelope_origin_675_i8 : ∀ x ∈ envelope_675_i8,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_675_i8 j := by decide +kernel
theorem envelope_exact_675_i8 : envelope_675_i8 =
    insert (6, 5) (Finset.univ.biUnion childrenD_675_i8) := by
  exact envelope_eq_combination childrenD_675_i8 (6, 5) envelope_675_i8
    pivot_mem_675_i8 child_envelope_sub_675_i8 envelope_origin_675_i8
def checked_675_i8 : CheckedCard where
  required := required_675_i8
  envelope := envelope_675_i8
  height := height_675_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i8
def height_675_i10 : ℕ := 9
def childrenH_675_i10 : Fin 2 → ℕ := ![height_321, height_354]
theorem height_exact_675_i10 : height_675_i10 = 1 + Finset.univ.sup childrenH_675_i10 := by decide +kernel
theorem required_origin_675_i10 : ∀ x ∈ required_675_i10,
    (∃ j, x ∈ childrenC_675_i10 j) ∨ ∀ j, x ∈ childrenD_675_i10 j := by decide +kernel
theorem required_exact_675_i10 : required_675_i10 =
    ((Finset.univ.biUnion childrenC_675_i10) ∪ commonEnvelope childrenD_675_i10).erase (7, 4) := by
  exact required_eq_combination childrenC_675_i10 childrenD_675_i10 (7, 4) required_675_i10
    (by decide +kernel) child_required_sub_675_i10 common_sub_675_i10 required_origin_675_i10
theorem envelope_origin_675_i10 : ∀ x ∈ envelope_675_i10,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_675_i10 j := by decide +kernel
theorem envelope_exact_675_i10 : envelope_675_i10 =
    insert (7, 4) (Finset.univ.biUnion childrenD_675_i10) := by
  exact envelope_eq_combination childrenD_675_i10 (7, 4) envelope_675_i10
    pivot_mem_675_i10 child_envelope_sub_675_i10 envelope_origin_675_i10
def checked_675_i10 : CheckedCard where
  required := required_675_i10
  envelope := envelope_675_i10
  height := height_675_i10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i10
def height_675_i9 : ℕ := 11
def childrenH_675_i9 : Fin 6 → ℕ := ![height_328, height_330, height_384, height_672, height_674, height_675_i10]
theorem height_exact_675_i9 : height_675_i9 = 1 + Finset.univ.sup childrenH_675_i9 := by decide +kernel
theorem required_origin_675_i9 : ∀ x ∈ required_675_i9,
    (∃ j, x ∈ childrenC_675_i9 j) ∨ ∀ j, x ∈ childrenD_675_i9 j := by decide +kernel
theorem required_exact_675_i9 : required_675_i9 =
    ((Finset.univ.biUnion childrenC_675_i9) ∪ commonEnvelope childrenD_675_i9).erase (7, 3) := by
  exact required_eq_combination childrenC_675_i9 childrenD_675_i9 (7, 3) required_675_i9
    (by decide +kernel) child_required_sub_675_i9 common_sub_675_i9 required_origin_675_i9
theorem envelope_origin_675_i9 : ∀ x ∈ envelope_675_i9,
    x = (7, 3) ∨ ∃ j, x ∈ childrenD_675_i9 j := by decide +kernel
theorem envelope_exact_675_i9 : envelope_675_i9 =
    insert (7, 3) (Finset.univ.biUnion childrenD_675_i9) := by
  exact envelope_eq_combination childrenD_675_i9 (7, 3) envelope_675_i9
    pivot_mem_675_i9 child_envelope_sub_675_i9 envelope_origin_675_i9
def checked_675_i9 : CheckedCard where
  required := required_675_i9
  envelope := envelope_675_i9
  height := height_675_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675_i9
def height_675 : ℕ := 13
def childrenH_675 : Fin 9 → ℕ := ![height_459, height_618, height_629, height_675_i0, height_675_i1, height_675_i2, height_675_i7, height_675_i8, height_675_i9]
theorem height_exact_675 : height_675 = 1 + Finset.univ.sup childrenH_675 := by decide +kernel
theorem required_origin_675 : ∀ x ∈ required_675,
    (∃ j, x ∈ childrenC_675 j) ∨ ∀ j, x ∈ childrenD_675 j := by decide +kernel
theorem required_exact_675 : required_675 =
    ((Finset.univ.biUnion childrenC_675) ∪ commonEnvelope childrenD_675).erase (7, 6) := by
  exact required_eq_combination childrenC_675 childrenD_675 (7, 6) required_675
    (by decide +kernel) child_required_sub_675 common_sub_675 required_origin_675
theorem envelope_origin_675 : ∀ x ∈ envelope_675,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_675 j := by decide +kernel
theorem envelope_exact_675 : envelope_675 =
    insert (7, 6) (Finset.univ.biUnion childrenD_675) := by
  exact envelope_eq_combination childrenD_675 (7, 6) envelope_675
    pivot_mem_675 child_envelope_sub_675 envelope_origin_675
def checked_675 : CheckedCard where
  required := required_675
  envelope := envelope_675
  height := height_675
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_675
def height_690_i0 : ℕ := 12
def childrenH_690_i0 : Fin 3 → ℕ := ![height_39, height_80, height_463]
theorem height_exact_690_i0 : height_690_i0 = 1 + Finset.univ.sup childrenH_690_i0 := by decide +kernel
theorem required_origin_690_i0 : ∀ x ∈ required_690_i0,
    (∃ j, x ∈ childrenC_690_i0 j) ∨ ∀ j, x ∈ childrenD_690_i0 j := by decide +kernel
theorem required_exact_690_i0 : required_690_i0 =
    ((Finset.univ.biUnion childrenC_690_i0) ∪ commonEnvelope childrenD_690_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_690_i0 childrenD_690_i0 (3, 6) required_690_i0
    (by decide +kernel) child_required_sub_690_i0 common_sub_690_i0 required_origin_690_i0
theorem envelope_origin_690_i0 : ∀ x ∈ envelope_690_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_690_i0 j := by decide +kernel
theorem envelope_exact_690_i0 : envelope_690_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_690_i0) := by
  exact envelope_eq_combination childrenD_690_i0 (3, 6) envelope_690_i0
    pivot_mem_690_i0 child_envelope_sub_690_i0 envelope_origin_690_i0
def checked_690_i0 : CheckedCard where
  required := required_690_i0
  envelope := envelope_690_i0
  height := height_690_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_690_i0
def height_690 : ℕ := 13
def childrenH_690 : Fin 3 → ℕ := ![height_21, height_56, height_690_i0]
theorem height_exact_690 : height_690 = 1 + Finset.univ.sup childrenH_690 := by decide +kernel
theorem required_origin_690 : ∀ x ∈ required_690,
    (∃ j, x ∈ childrenC_690 j) ∨ ∀ j, x ∈ childrenD_690 j := by decide +kernel
theorem required_exact_690 : required_690 =
    ((Finset.univ.biUnion childrenC_690) ∪ commonEnvelope childrenD_690).erase (3, 4) := by
  exact required_eq_combination childrenC_690 childrenD_690 (3, 4) required_690
    (by decide +kernel) child_required_sub_690 common_sub_690 required_origin_690
theorem envelope_origin_690 : ∀ x ∈ envelope_690,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_690 j := by decide +kernel
theorem envelope_exact_690 : envelope_690 =
    insert (3, 4) (Finset.univ.biUnion childrenD_690) := by
  exact envelope_eq_combination childrenD_690 (3, 4) envelope_690
    pivot_mem_690 child_envelope_sub_690 envelope_origin_690
def checked_690 : CheckedCard where
  required := required_690
  envelope := envelope_690
  height := height_690
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_690
def height_692_i1 : ℕ := 10
def childrenH_692_i1 : Fin 7 → ℕ := ![height_13, height_14, height_118, height_192, height_193, height_396, height_435]
theorem height_exact_692_i1 : height_692_i1 = 1 + Finset.univ.sup childrenH_692_i1 := by decide +kernel
theorem required_origin_692_i1 : ∀ x ∈ required_692_i1,
    (∃ j, x ∈ childrenC_692_i1 j) ∨ ∀ j, x ∈ childrenD_692_i1 j := by decide +kernel
theorem required_exact_692_i1 : required_692_i1 =
    ((Finset.univ.biUnion childrenC_692_i1) ∪ commonEnvelope childrenD_692_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_692_i1 childrenD_692_i1 (3, 3) required_692_i1
    (by decide +kernel) child_required_sub_692_i1 common_sub_692_i1 required_origin_692_i1
theorem envelope_origin_692_i1 : ∀ x ∈ envelope_692_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_692_i1 j := by decide +kernel
theorem envelope_exact_692_i1 : envelope_692_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_692_i1) := by
  exact envelope_eq_combination childrenD_692_i1 (3, 3) envelope_692_i1
    pivot_mem_692_i1 child_envelope_sub_692_i1 envelope_origin_692_i1
def checked_692_i1 : CheckedCard where
  required := required_692_i1
  envelope := envelope_692_i1
  height := height_692_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_692_i1
def height_692_i2 : ℕ := 11
def childrenH_692_i2 : Fin 2 → ℕ := ![height_2, height_509]
theorem height_exact_692_i2 : height_692_i2 = 1 + Finset.univ.sup childrenH_692_i2 := by decide +kernel
theorem required_origin_692_i2 : ∀ x ∈ required_692_i2,
    (∃ j, x ∈ childrenC_692_i2 j) ∨ ∀ j, x ∈ childrenD_692_i2 j := by decide +kernel
theorem required_exact_692_i2 : required_692_i2 =
    ((Finset.univ.biUnion childrenC_692_i2) ∪ commonEnvelope childrenD_692_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_692_i2 childrenD_692_i2 (4, 4) required_692_i2
    (by decide +kernel) child_required_sub_692_i2 common_sub_692_i2 required_origin_692_i2
theorem envelope_origin_692_i2 : ∀ x ∈ envelope_692_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_692_i2 j := by decide +kernel
theorem envelope_exact_692_i2 : envelope_692_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_692_i2) := by
  exact envelope_eq_combination childrenD_692_i2 (4, 4) envelope_692_i2
    pivot_mem_692_i2 child_envelope_sub_692_i2 envelope_origin_692_i2
def checked_692_i2 : CheckedCard where
  required := required_692_i2
  envelope := envelope_692_i2
  height := height_692_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_692_i2
def height_692_i0 : ℕ := 12
def childrenH_692_i0 : Fin 8 → ℕ := ![height_110, height_119, height_399, height_430, height_461, height_475, height_692_i1, height_692_i2]
theorem height_exact_692_i0 : height_692_i0 = 1 + Finset.univ.sup childrenH_692_i0 := by decide +kernel
theorem required_origin_692_i0 : ∀ x ∈ required_692_i0,
    (∃ j, x ∈ childrenC_692_i0 j) ∨ ∀ j, x ∈ childrenD_692_i0 j := by decide +kernel
theorem required_exact_692_i0 : required_692_i0 =
    ((Finset.univ.biUnion childrenC_692_i0) ∪ commonEnvelope childrenD_692_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_692_i0 childrenD_692_i0 (3, 4) required_692_i0
    (by decide +kernel) child_required_sub_692_i0 common_sub_692_i0 required_origin_692_i0
theorem envelope_origin_692_i0 : ∀ x ∈ envelope_692_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_692_i0 j := by decide +kernel
theorem envelope_exact_692_i0 : envelope_692_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_692_i0) := by
  exact envelope_eq_combination childrenD_692_i0 (3, 4) envelope_692_i0
    pivot_mem_692_i0 child_envelope_sub_692_i0 envelope_origin_692_i0
def checked_692_i0 : CheckedCard where
  required := required_692_i0
  envelope := envelope_692_i0
  height := height_692_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_692_i0
def height_692 : ℕ := 13
def childrenH_692 : Fin 2 → ℕ := ![height_5, height_692_i0]
theorem height_exact_692 : height_692 = 1 + Finset.univ.sup childrenH_692 := by decide +kernel
theorem required_origin_692 : ∀ x ∈ required_692,
    (∃ j, x ∈ childrenC_692 j) ∨ ∀ j, x ∈ childrenD_692 j := by decide +kernel
theorem required_exact_692 : required_692 =
    ((Finset.univ.biUnion childrenC_692) ∪ commonEnvelope childrenD_692).erase (1, 5) := by
  exact required_eq_combination childrenC_692 childrenD_692 (1, 5) required_692
    (by decide +kernel) child_required_sub_692 common_sub_692 required_origin_692
theorem envelope_origin_692 : ∀ x ∈ envelope_692,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_692 j := by decide +kernel
theorem envelope_exact_692 : envelope_692 =
    insert (1, 5) (Finset.univ.biUnion childrenD_692) := by
  exact envelope_eq_combination childrenD_692 (1, 5) envelope_692
    pivot_mem_692 child_envelope_sub_692 envelope_origin_692
def checked_692 : CheckedCard where
  required := required_692
  envelope := envelope_692
  height := height_692
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_692
end SnakyPrototype.Certificate21

end OAI
