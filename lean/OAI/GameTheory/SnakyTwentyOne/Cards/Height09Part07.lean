import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_622_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_622_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_622_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_41), (placed21 7 (6, 6) required_56)]
def childrenD_622_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_41), (placed21 7 (6, 6) envelope_56)]
theorem common_sub_622_i0 : commonEnvelope childrenD_622_i0 ⊆ insert (3, 6) required_622_i0 := by decide +kernel
theorem child_required_sub_622_i0 : ∀ j, childrenC_622_i0 j ⊆ insert (3, 6) required_622_i0 := by decide +kernel
theorem child_envelope_sub_622_i0 : ∀ j, childrenD_622_i0 j ⊆ envelope_622_i0 := by decide +kernel
theorem pivot_mem_622_i0 : (3, 6) ∈ envelope_622_i0 := by decide +kernel
theorem children_work_622_i0 : ∀ j, Template HasSnaky 4 (childrenC_622_i0 j) (childrenD_622_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_41 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 7 (6, 6)).mono (by decide +kernel)
theorem row_works_622_i0 : Template HasSnaky 5 required_622_i0 envelope_622_i0 := by
  refine compose HasSnaky 4 childrenC_622_i0 childrenD_622_i0 children_work_622_i0 (3, 6)
    required_622_i0 envelope_622_i0 pivot_mem_622_i0 child_required_sub_622_i0 child_envelope_sub_622_i0 ?_
  intro b hb
  exact common_sub_622_i0 (mem_commonEnvelope childrenD_622_i0 b hb)
def required_622_i2 : Finset Cell := ⟨(([(2, 2), (3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_622_i2 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_622_i2 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) required_4), (placed21 2 (4, 3) required_41)]
def childrenD_622_i2 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) envelope_4), (placed21 2 (4, 3) envelope_41)]
theorem common_sub_622_i2 : commonEnvelope childrenD_622_i2 ⊆ insert (3, 6) required_622_i2 := by decide +kernel
theorem child_required_sub_622_i2 : ∀ j, childrenC_622_i2 j ⊆ insert (3, 6) required_622_i2 := by decide +kernel
theorem child_envelope_sub_622_i2 : ∀ j, childrenD_622_i2 j ⊆ envelope_622_i2 := by decide +kernel
theorem pivot_mem_622_i2 : (3, 6) ∈ envelope_622_i2 := by decide +kernel
theorem children_work_622_i2 : ∀ j, Template HasSnaky 4 (childrenC_622_i2 j) (childrenD_622_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_41 2 (4, 3)).mono (by decide +kernel)
theorem row_works_622_i2 : Template HasSnaky 5 required_622_i2 envelope_622_i2 := by
  refine compose HasSnaky 4 childrenC_622_i2 childrenD_622_i2 children_work_622_i2 (3, 6)
    required_622_i2 envelope_622_i2 pivot_mem_622_i2 child_required_sub_622_i2 child_envelope_sub_622_i2 ?_
  intro b hb
  exact common_sub_622_i2 (mem_commonEnvelope childrenD_622_i2 b hb)
def required_622_i3 : Finset Cell := ⟨(([(2, 2), (3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_622_i3 : Finset Cell := ⟨(([(2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_622_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 5) required_5), (placed21 4 (3, 6) required_11)]
def childrenD_622_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 5) envelope_5), (placed21 4 (3, 6) envelope_11)]
theorem common_sub_622_i3 : commonEnvelope childrenD_622_i3 ⊆ insert (3, 2) required_622_i3 := by decide +kernel
theorem child_required_sub_622_i3 : ∀ j, childrenC_622_i3 j ⊆ insert (3, 2) required_622_i3 := by decide +kernel
theorem child_envelope_sub_622_i3 : ∀ j, childrenD_622_i3 j ⊆ envelope_622_i3 := by decide +kernel
theorem pivot_mem_622_i3 : (3, 2) ∈ envelope_622_i3 := by decide +kernel
theorem children_work_622_i3 : ∀ j, Template HasSnaky 2 (childrenC_622_i3 j) (childrenD_622_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 4 (3, 6)).mono (by decide +kernel)
theorem row_works_622_i3 : Template HasSnaky 3 required_622_i3 envelope_622_i3 := by
  refine compose HasSnaky 2 childrenC_622_i3 childrenD_622_i3 children_work_622_i3 (3, 2)
    required_622_i3 envelope_622_i3 pivot_mem_622_i3 child_required_sub_622_i3 child_envelope_sub_622_i3 ?_
  intro b hb
  exact common_sub_622_i3 (mem_commonEnvelope childrenD_622_i3 b hb)
def required_622_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_622_i1 : Finset Cell := ⟨(([(2, 0), (2, 1), (2, 2), (2, 3), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_622_i1 : Fin 3 → Finset Cell := ![(placed21 6 (3, 6) required_61), required_622_i2, required_622_i3]
def childrenD_622_i1 : Fin 3 → Finset Cell := ![(placed21 6 (3, 6) envelope_61), envelope_622_i2, envelope_622_i3]
theorem common_sub_622_i1 : commonEnvelope childrenD_622_i1 ⊆ insert (2, 2) required_622_i1 := by decide +kernel
theorem child_required_sub_622_i1 : ∀ j, childrenC_622_i1 j ⊆ insert (2, 2) required_622_i1 := by decide +kernel
theorem child_envelope_sub_622_i1 : ∀ j, childrenD_622_i1 j ⊆ envelope_622_i1 := by decide +kernel
theorem pivot_mem_622_i1 : (2, 2) ∈ envelope_622_i1 := by decide +kernel
theorem children_work_622_i1 : ∀ j, Template HasSnaky 5 (childrenC_622_i1 j) (childrenD_622_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_61 6 (3, 6)).mono (by decide +kernel)
  · exact row_works_622_i2.mono (by decide +kernel)
  · exact row_works_622_i3.mono (by decide +kernel)
theorem row_works_622_i1 : Template HasSnaky 6 required_622_i1 envelope_622_i1 := by
  refine compose HasSnaky 5 childrenC_622_i1 childrenD_622_i1 children_work_622_i1 (2, 2)
    required_622_i1 envelope_622_i1 pivot_mem_622_i1 child_required_sub_622_i1 child_envelope_sub_622_i1 ?_
  intro b hb
  exact common_sub_622_i1 (mem_commonEnvelope childrenD_622_i1 b hb)
def required_622_i4 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_622_i4 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_622_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) required_23), (placed21 2 (7, 1) required_621)]
def childrenD_622_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) envelope_23), (placed21 2 (7, 1) envelope_621)]
theorem common_sub_622_i4 : commonEnvelope childrenD_622_i4 ⊆ insert (4, 5) required_622_i4 := by decide +kernel
theorem child_required_sub_622_i4 : ∀ j, childrenC_622_i4 j ⊆ insert (4, 5) required_622_i4 := by decide +kernel
theorem child_envelope_sub_622_i4 : ∀ j, childrenD_622_i4 j ⊆ envelope_622_i4 := by decide +kernel
theorem pivot_mem_622_i4 : (4, 5) ∈ envelope_622_i4 := by decide +kernel
theorem children_work_622_i4 : ∀ j, Template HasSnaky 7 (childrenC_622_i4 j) (childrenD_622_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_23 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_621 2 (7, 1)).mono (by decide +kernel)
theorem row_works_622_i4 : Template HasSnaky 8 required_622_i4 envelope_622_i4 := by
  refine compose HasSnaky 7 childrenC_622_i4 childrenD_622_i4 children_work_622_i4 (4, 5)
    required_622_i4 envelope_622_i4 pivot_mem_622_i4 child_required_sub_622_i4 child_envelope_sub_622_i4 ?_
  intro b hb
  exact common_sub_622_i4 (mem_commonEnvelope childrenD_622_i4 b hb)
def required_622 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_622 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_622 : Fin 4 → Finset Cell := ![(placed21 7 (6, 6) required_57), required_622_i0, required_622_i1, required_622_i4]
def childrenD_622 : Fin 4 → Finset Cell := ![(placed21 7 (6, 6) envelope_57), envelope_622_i0, envelope_622_i1, envelope_622_i4]
theorem common_sub_622 : commonEnvelope childrenD_622 ⊆ insert (4, 4) required_622 := by decide +kernel
theorem child_required_sub_622 : ∀ j, childrenC_622 j ⊆ insert (4, 4) required_622 := by decide +kernel
theorem child_envelope_sub_622 : ∀ j, childrenD_622 j ⊆ envelope_622 := by decide +kernel
theorem pivot_mem_622 : (4, 4) ∈ envelope_622 := by decide +kernel
theorem children_work_622 : ∀ j, Template HasSnaky 8 (childrenC_622 j) (childrenD_622 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_57 7 (6, 6)).mono (by decide +kernel)
  · exact row_works_622_i0.mono (by decide +kernel)
  · exact row_works_622_i1.mono (by decide +kernel)
  · exact row_works_622_i4.mono (by decide +kernel)
theorem row_works_622 : Template HasSnaky 9 required_622 envelope_622 := by
  refine compose HasSnaky 8 childrenC_622 childrenD_622 children_work_622 (4, 4)
    required_622 envelope_622 pivot_mem_622 child_required_sub_622 child_envelope_sub_622 ?_
  intro b hb
  exact common_sub_622 (mem_commonEnvelope childrenD_622 b hb)
def required_629 : Finset Cell := ⟨(([(3, 3), (3, 4), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_629 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (7, 4), (7, 5), (8, 3), (8, 4), (8, 5), (9, 3), (9, 4), (9, 5), (10, 3), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_629 : Fin 5 → Finset Cell := ![(placed21 2 (5, 1) required_190), (placed21 2 (7, 2) required_295), (placed21 2 (6, 1) required_364), required_518, (placed21 4 (2, 7) required_628)]
def childrenD_629 : Fin 5 → Finset Cell := ![(placed21 2 (5, 1) envelope_190), (placed21 2 (7, 2) envelope_295), (placed21 2 (6, 1) envelope_364), envelope_518, (placed21 4 (2, 7) envelope_628)]
theorem common_sub_629 : commonEnvelope childrenD_629 ⊆ insert (3, 5) required_629 := by decide +kernel
theorem child_required_sub_629 : ∀ j, childrenC_629 j ⊆ insert (3, 5) required_629 := by decide +kernel
theorem child_envelope_sub_629 : ∀ j, childrenD_629 j ⊆ envelope_629 := by decide +kernel
theorem pivot_mem_629 : (3, 5) ∈ envelope_629 := by decide +kernel
theorem children_work_629 : ∀ j, Template HasSnaky 8 (childrenC_629 j) (childrenD_629 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_190 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_295 2 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_364 2 (6, 1)).mono (by decide +kernel)
  · exact row_works_518.mono (by decide +kernel)
  · exact (placed21_template row_works_628 4 (2, 7)).mono (by decide +kernel)
theorem row_works_629 : Template HasSnaky 9 required_629 envelope_629 := by
  refine compose HasSnaky 8 childrenC_629 childrenD_629 children_work_629 (3, 5)
    required_629 envelope_629 pivot_mem_629 child_required_sub_629 child_envelope_sub_629 ?_
  intro b hb
  exact common_sub_629 (mem_commonEnvelope childrenD_629 b hb)
def required_638_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_638_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_638_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) required_15), (placed21 4 (1, 7) required_85)]
def childrenD_638_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) envelope_15), (placed21 4 (1, 7) envelope_85)]
theorem common_sub_638_i0 : commonEnvelope childrenD_638_i0 ⊆ insert (3, 4) required_638_i0 := by decide +kernel
theorem child_required_sub_638_i0 : ∀ j, childrenC_638_i0 j ⊆ insert (3, 4) required_638_i0 := by decide +kernel
theorem child_envelope_sub_638_i0 : ∀ j, childrenD_638_i0 j ⊆ envelope_638_i0 := by decide +kernel
theorem pivot_mem_638_i0 : (3, 4) ∈ envelope_638_i0 := by decide +kernel
theorem children_work_638_i0 : ∀ j, Template HasSnaky 6 (childrenC_638_i0 j) (childrenD_638_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_85 4 (1, 7)).mono (by decide +kernel)
theorem row_works_638_i0 : Template HasSnaky 7 required_638_i0 envelope_638_i0 := by
  refine compose HasSnaky 6 childrenC_638_i0 childrenD_638_i0 children_work_638_i0 (3, 4)
    required_638_i0 envelope_638_i0 pivot_mem_638_i0 child_required_sub_638_i0 child_envelope_sub_638_i0 ?_
  intro b hb
  exact common_sub_638_i0 (mem_commonEnvelope childrenD_638_i0 b hb)
def required_638 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_638 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_638 : Fin 6 → Finset Cell := ![(placed21 4 (0, 6) required_57), (placed21 3 (0, 5) required_136), (placed21 3 (0, 5) required_217), (placed21 0 (1, 0) required_530), required_638_i0, (placed21 0 (0, 1) required_637)]
def childrenD_638 : Fin 6 → Finset Cell := ![(placed21 4 (0, 6) envelope_57), (placed21 3 (0, 5) envelope_136), (placed21 3 (0, 5) envelope_217), (placed21 0 (1, 0) envelope_530), envelope_638_i0, (placed21 0 (0, 1) envelope_637)]
theorem common_sub_638 : commonEnvelope childrenD_638 ⊆ insert (3, 3) required_638 := by decide +kernel
theorem child_required_sub_638 : ∀ j, childrenC_638 j ⊆ insert (3, 3) required_638 := by decide +kernel
theorem child_envelope_sub_638 : ∀ j, childrenD_638 j ⊆ envelope_638 := by decide +kernel
theorem pivot_mem_638 : (3, 3) ∈ envelope_638 := by decide +kernel
theorem children_work_638 : ∀ j, Template HasSnaky 8 (childrenC_638 j) (childrenD_638 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_57 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_136 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_217 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_530 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_638_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_637 0 (0, 1)).mono (by decide +kernel)
theorem row_works_638 : Template HasSnaky 9 required_638 envelope_638 := by
  refine compose HasSnaky 8 childrenC_638 childrenD_638 children_work_638 (3, 3)
    required_638 envelope_638 pivot_mem_638 child_required_sub_638 child_envelope_sub_638 ?_
  intro b hb
  exact common_sub_638 (mem_commonEnvelope childrenD_638 b hb)
def required_640_i3 : Finset Cell := ⟨(([(2, 6), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_640_i3 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_640_i3 : Fin 2 → Finset Cell := ![(placed21 1 (4, 3) required_5), (placed21 0 (2, 5) required_90)]
def childrenD_640_i3 : Fin 2 → Finset Cell := ![(placed21 1 (4, 3) envelope_5), (placed21 0 (2, 5) envelope_90)]
theorem common_sub_640_i3 : commonEnvelope childrenD_640_i3 ⊆ insert (5, 6) required_640_i3 := by decide +kernel
theorem child_required_sub_640_i3 : ∀ j, childrenC_640_i3 j ⊆ insert (5, 6) required_640_i3 := by decide +kernel
theorem child_envelope_sub_640_i3 : ∀ j, childrenD_640_i3 j ⊆ envelope_640_i3 := by decide +kernel
theorem pivot_mem_640_i3 : (5, 6) ∈ envelope_640_i3 := by decide +kernel
theorem children_work_640_i3 : ∀ j, Template HasSnaky 4 (childrenC_640_i3 j) (childrenD_640_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_90 0 (2, 5)).mono (by decide +kernel)
theorem row_works_640_i3 : Template HasSnaky 5 required_640_i3 envelope_640_i3 := by
  refine compose HasSnaky 4 childrenC_640_i3 childrenD_640_i3 children_work_640_i3 (5, 6)
    required_640_i3 envelope_640_i3 pivot_mem_640_i3 child_required_sub_640_i3 child_envelope_sub_640_i3 ?_
  intro b hb
  exact common_sub_640_i3 (mem_commonEnvelope childrenD_640_i3 b hb)
def required_640_i2 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_640_i2 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_640_i2 : Fin 3 → Finset Cell := ![(placed21 3 (1, 6) required_44), (placed21 5 (5, 3) required_260), required_640_i3]
def childrenD_640_i2 : Fin 3 → Finset Cell := ![(placed21 3 (1, 6) envelope_44), (placed21 5 (5, 3) envelope_260), envelope_640_i3]
theorem common_sub_640_i2 : commonEnvelope childrenD_640_i2 ⊆ insert (2, 6) required_640_i2 := by decide +kernel
theorem child_required_sub_640_i2 : ∀ j, childrenC_640_i2 j ⊆ insert (2, 6) required_640_i2 := by decide +kernel
theorem child_envelope_sub_640_i2 : ∀ j, childrenD_640_i2 j ⊆ envelope_640_i2 := by decide +kernel
theorem pivot_mem_640_i2 : (2, 6) ∈ envelope_640_i2 := by decide +kernel
theorem children_work_640_i2 : ∀ j, Template HasSnaky 5 (childrenC_640_i2 j) (childrenD_640_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_260 5 (5, 3)).mono (by decide +kernel)
  · exact row_works_640_i3.mono (by decide +kernel)
theorem row_works_640_i2 : Template HasSnaky 6 required_640_i2 envelope_640_i2 := by
  refine compose HasSnaky 5 childrenC_640_i2 childrenD_640_i2 children_work_640_i2 (2, 6)
    required_640_i2 envelope_640_i2 pivot_mem_640_i2 child_required_sub_640_i2 child_envelope_sub_640_i2 ?_
  intro b hb
  exact common_sub_640_i2 (mem_commonEnvelope childrenD_640_i2 b hb)
def required_640_i1 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 6), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_640_i1 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_640_i1 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) required_5), required_640_i2]
def childrenD_640_i1 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) envelope_5), envelope_640_i2]
theorem common_sub_640_i1 : commonEnvelope childrenD_640_i1 ⊆ insert (4, 6) required_640_i1 := by decide +kernel
theorem child_required_sub_640_i1 : ∀ j, childrenC_640_i1 j ⊆ insert (4, 6) required_640_i1 := by decide +kernel
theorem child_envelope_sub_640_i1 : ∀ j, childrenD_640_i1 j ⊆ envelope_640_i1 := by decide +kernel
theorem pivot_mem_640_i1 : (4, 6) ∈ envelope_640_i1 := by decide +kernel
theorem children_work_640_i1 : ∀ j, Template HasSnaky 6 (childrenC_640_i1 j) (childrenD_640_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact row_works_640_i2.mono (by decide +kernel)
theorem row_works_640_i1 : Template HasSnaky 7 required_640_i1 envelope_640_i1 := by
  refine compose HasSnaky 6 childrenC_640_i1 childrenD_640_i1 children_work_640_i1 (4, 6)
    required_640_i1 envelope_640_i1 pivot_mem_640_i1 child_required_sub_640_i1 child_envelope_sub_640_i1 ?_
  intro b hb
  exact common_sub_640_i1 (mem_commonEnvelope childrenD_640_i1 b hb)
def required_640_i0 : Finset Cell := ⟨(([(2, 3), (2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_640_i0 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_640_i0 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) required_61), (placed21 4 (3, 6) required_89), (placed21 5 (6, 2) required_183), required_640_i1]
def childrenD_640_i0 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) envelope_61), (placed21 4 (3, 6) envelope_89), (placed21 5 (6, 2) envelope_183), envelope_640_i1]
theorem common_sub_640_i0 : commonEnvelope childrenD_640_i0 ⊆ insert (3, 6) required_640_i0 := by decide +kernel
theorem child_required_sub_640_i0 : ∀ j, childrenC_640_i0 j ⊆ insert (3, 6) required_640_i0 := by decide +kernel
theorem child_envelope_sub_640_i0 : ∀ j, childrenD_640_i0 j ⊆ envelope_640_i0 := by decide +kernel
theorem pivot_mem_640_i0 : (3, 6) ∈ envelope_640_i0 := by decide +kernel
theorem children_work_640_i0 : ∀ j, Template HasSnaky 7 (childrenC_640_i0 j) (childrenD_640_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_61 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_89 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_183 5 (6, 2)).mono (by decide +kernel)
  · exact row_works_640_i1.mono (by decide +kernel)
theorem row_works_640_i0 : Template HasSnaky 8 required_640_i0 envelope_640_i0 := by
  refine compose HasSnaky 7 childrenC_640_i0 childrenD_640_i0 children_work_640_i0 (3, 6)
    required_640_i0 envelope_640_i0 pivot_mem_640_i0 child_required_sub_640_i0 child_envelope_sub_640_i0 ?_
  intro b hb
  exact common_sub_640_i0 (mem_commonEnvelope childrenD_640_i0 b hb)
def required_640 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_640 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 5), (6, 6), (6, 7), (7, 2), (7, 5), (7, 6), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_640 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) required_10), (placed21 3 (2, 6) required_47), (placed21 6 (4, 6) required_52), required_640_i0]
def childrenD_640 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) envelope_10), (placed21 3 (2, 6) envelope_47), (placed21 6 (4, 6) envelope_52), envelope_640_i0]
theorem common_sub_640 : commonEnvelope childrenD_640 ⊆ insert (4, 5) required_640 := by decide +kernel
theorem child_required_sub_640 : ∀ j, childrenC_640 j ⊆ insert (4, 5) required_640 := by decide +kernel
theorem child_envelope_sub_640 : ∀ j, childrenD_640 j ⊆ envelope_640 := by decide +kernel
theorem pivot_mem_640 : (4, 5) ∈ envelope_640 := by decide +kernel
theorem children_work_640 : ∀ j, Template HasSnaky 8 (childrenC_640 j) (childrenD_640 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (4, 6)).mono (by decide +kernel)
  · exact row_works_640_i0.mono (by decide +kernel)
theorem row_works_640 : Template HasSnaky 9 required_640 envelope_640 := by
  refine compose HasSnaky 8 childrenC_640 childrenD_640 children_work_640 (4, 5)
    required_640 envelope_640 pivot_mem_640 child_required_sub_640 child_envelope_sub_640 ?_
  intro b hb
  exact common_sub_640 (mem_commonEnvelope childrenD_640 b hb)
def required_655_i0 : Finset Cell := ⟨(([(2, 5), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_655_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 7), (4, 8), (4, 9), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_655_i0 : Fin 3 → Finset Cell := ![(placed21 5 (5, 2) required_179), (placed21 1 (2, 3) required_314), (placed21 7 (5, 7) required_344)]
def childrenD_655_i0 : Fin 3 → Finset Cell := ![(placed21 5 (5, 2) envelope_179), (placed21 1 (2, 3) envelope_314), (placed21 7 (5, 7) envelope_344)]
theorem common_sub_655_i0 : commonEnvelope childrenD_655_i0 ⊆ insert (3, 6) required_655_i0 := by decide +kernel
theorem child_required_sub_655_i0 : ∀ j, childrenC_655_i0 j ⊆ insert (3, 6) required_655_i0 := by decide +kernel
theorem child_envelope_sub_655_i0 : ∀ j, childrenD_655_i0 j ⊆ envelope_655_i0 := by decide +kernel
theorem pivot_mem_655_i0 : (3, 6) ∈ envelope_655_i0 := by decide +kernel
theorem children_work_655_i0 : ∀ j, Template HasSnaky 7 (childrenC_655_i0 j) (childrenD_655_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_179 5 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_344 7 (5, 7)).mono (by decide +kernel)
theorem row_works_655_i0 : Template HasSnaky 8 required_655_i0 envelope_655_i0 := by
  refine compose HasSnaky 7 childrenC_655_i0 childrenD_655_i0 children_work_655_i0 (3, 6)
    required_655_i0 envelope_655_i0 pivot_mem_655_i0 child_required_sub_655_i0 child_envelope_sub_655_i0 ?_
  intro b hb
  exact common_sub_655_i0 (mem_commonEnvelope childrenD_655_i0 b hb)
def required_655 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_655 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 7), (4, 8), (4, 9), (5, 2), (5, 4), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_655 : Fin 4 → Finset Cell := ![(placed21 4 (2, 6) required_10), (placed21 2 (3, 2) required_52), (placed21 7 (6, 6) required_435), required_655_i0]
def childrenD_655 : Fin 4 → Finset Cell := ![(placed21 4 (2, 6) envelope_10), (placed21 2 (3, 2) envelope_52), (placed21 7 (6, 6) envelope_435), envelope_655_i0]
theorem common_sub_655 : commonEnvelope childrenD_655 ⊆ insert (3, 3) required_655 := by decide +kernel
theorem child_required_sub_655 : ∀ j, childrenC_655 j ⊆ insert (3, 3) required_655 := by decide +kernel
theorem child_envelope_sub_655 : ∀ j, childrenD_655 j ⊆ envelope_655 := by decide +kernel
theorem pivot_mem_655 : (3, 3) ∈ envelope_655 := by decide +kernel
theorem children_work_655 : ∀ j, Template HasSnaky 8 (childrenC_655 j) (childrenD_655 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 7 (6, 6)).mono (by decide +kernel)
  · exact row_works_655_i0.mono (by decide +kernel)
theorem row_works_655 : Template HasSnaky 9 required_655 envelope_655 := by
  refine compose HasSnaky 8 childrenC_655 childrenD_655 children_work_655 (3, 3)
    required_655 envelope_655 pivot_mem_655 child_required_sub_655 child_envelope_sub_655 ?_
  intro b hb
  exact common_sub_655 (mem_commonEnvelope childrenD_655 b hb)
def required_659 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_659 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_659 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) required_5), (placed21 0 (1, 0) required_658)]
def childrenD_659 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) envelope_5), (placed21 0 (1, 0) envelope_658)]
theorem common_sub_659 : commonEnvelope childrenD_659 ⊆ insert (3, 4) required_659 := by decide +kernel
theorem child_required_sub_659 : ∀ j, childrenC_659 j ⊆ insert (3, 4) required_659 := by decide +kernel
theorem child_envelope_sub_659 : ∀ j, childrenD_659 j ⊆ envelope_659 := by decide +kernel
theorem pivot_mem_659 : (3, 4) ∈ envelope_659 := by decide +kernel
theorem children_work_659 : ∀ j, Template HasSnaky 8 (childrenC_659 j) (childrenD_659 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_658 0 (1, 0)).mono (by decide +kernel)
theorem row_works_659 : Template HasSnaky 9 required_659 envelope_659 := by
  refine compose HasSnaky 8 childrenC_659 childrenD_659 children_work_659 (3, 4)
    required_659 envelope_659 pivot_mem_659 child_required_sub_659 child_envelope_sub_659 ?_
  intro b hb
  exact common_sub_659 (mem_commonEnvelope childrenD_659 b hb)
def required_662_i0 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_662_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 5), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_662_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) required_5), (placed21 2 (4, 2) required_141)]
def childrenD_662_i0 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) envelope_5), (placed21 2 (4, 2) envelope_141)]
theorem common_sub_662_i0 : commonEnvelope childrenD_662_i0 ⊆ insert (1, 5) required_662_i0 := by decide +kernel
theorem child_required_sub_662_i0 : ∀ j, childrenC_662_i0 j ⊆ insert (1, 5) required_662_i0 := by decide +kernel
theorem child_envelope_sub_662_i0 : ∀ j, childrenD_662_i0 j ⊆ envelope_662_i0 := by decide +kernel
theorem pivot_mem_662_i0 : (1, 5) ∈ envelope_662_i0 := by decide +kernel
theorem children_work_662_i0 : ∀ j, Template HasSnaky 4 (childrenC_662_i0 j) (childrenD_662_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_141 2 (4, 2)).mono (by decide +kernel)
theorem row_works_662_i0 : Template HasSnaky 5 required_662_i0 envelope_662_i0 := by
  refine compose HasSnaky 4 childrenC_662_i0 childrenD_662_i0 children_work_662_i0 (1, 5)
    required_662_i0 envelope_662_i0 pivot_mem_662_i0 child_required_sub_662_i0 child_envelope_sub_662_i0 ?_
  intro b hb
  exact common_sub_662_i0 (mem_commonEnvelope childrenD_662_i0 b hb)
def required_662 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_662 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_662 : Fin 3 → Finset Cell := ![(placed21 3 (1, 5) required_52), (placed21 0 (2, 0) required_658), required_662_i0]
def childrenD_662 : Fin 3 → Finset Cell := ![(placed21 3 (1, 5) envelope_52), (placed21 0 (2, 0) envelope_658), envelope_662_i0]
theorem common_sub_662 : commonEnvelope childrenD_662 ⊆ insert (4, 4) required_662 := by decide +kernel
theorem child_required_sub_662 : ∀ j, childrenC_662 j ⊆ insert (4, 4) required_662 := by decide +kernel
theorem child_envelope_sub_662 : ∀ j, childrenD_662 j ⊆ envelope_662 := by decide +kernel
theorem pivot_mem_662 : (4, 4) ∈ envelope_662 := by decide +kernel
theorem children_work_662 : ∀ j, Template HasSnaky 8 (childrenC_662 j) (childrenD_662 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_658 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_662_i0.mono (by decide +kernel)
theorem row_works_662 : Template HasSnaky 9 required_662 envelope_662 := by
  refine compose HasSnaky 8 childrenC_662 childrenD_662 children_work_662 (4, 4)
    required_662 envelope_662 pivot_mem_662 child_required_sub_662 child_envelope_sub_662 ?_
  intro b hb
  exact common_sub_662 (mem_commonEnvelope childrenD_662 b hb)
def required_667 : Finset Cell := ⟨(([(0, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_667 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_667 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) required_7), (placed21 2 (4, 0) required_9), (placed21 0 (0, 1) required_666)]
def childrenD_667 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) envelope_7), (placed21 2 (4, 0) envelope_9), (placed21 0 (0, 1) envelope_666)]
theorem common_sub_667 : commonEnvelope childrenD_667 ⊆ insert (3, 4) required_667 := by decide +kernel
theorem child_required_sub_667 : ∀ j, childrenC_667 j ⊆ insert (3, 4) required_667 := by decide +kernel
theorem child_envelope_sub_667 : ∀ j, childrenD_667 j ⊆ envelope_667 := by decide +kernel
theorem pivot_mem_667 : (3, 4) ∈ envelope_667 := by decide +kernel
theorem children_work_667 : ∀ j, Template HasSnaky 8 (childrenC_667 j) (childrenD_667 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_666 0 (0, 1)).mono (by decide +kernel)
theorem row_works_667 : Template HasSnaky 9 required_667 envelope_667 := by
  refine compose HasSnaky 8 childrenC_667 childrenD_667 children_work_667 (3, 4)
    required_667 envelope_667 pivot_mem_667 child_required_sub_667 child_envelope_sub_667 ?_
  intro b hb
  exact common_sub_667 (mem_commonEnvelope childrenD_667 b hb)
def required_668 : Finset Cell := ⟨(([(0, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_668 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_668 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) required_7), (placed21 0 (2, 0) required_9), (placed21 0 (0, 1) required_666)]
def childrenD_668 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) envelope_7), (placed21 0 (2, 0) envelope_9), (placed21 0 (0, 1) envelope_666)]
theorem common_sub_668 : commonEnvelope childrenD_668 ⊆ insert (3, 4) required_668 := by decide +kernel
theorem child_required_sub_668 : ∀ j, childrenC_668 j ⊆ insert (3, 4) required_668 := by decide +kernel
theorem child_envelope_sub_668 : ∀ j, childrenD_668 j ⊆ envelope_668 := by decide +kernel
theorem pivot_mem_668 : (3, 4) ∈ envelope_668 := by decide +kernel
theorem children_work_668 : ∀ j, Template HasSnaky 8 (childrenC_668 j) (childrenD_668 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_666 0 (0, 1)).mono (by decide +kernel)
theorem row_works_668 : Template HasSnaky 9 required_668 envelope_668 := by
  refine compose HasSnaky 8 childrenC_668 childrenD_668 children_work_668 (3, 4)
    required_668 envelope_668 pivot_mem_668 child_required_sub_668 child_envelope_sub_668 ?_
  intro b hb
  exact common_sub_668 (mem_commonEnvelope childrenD_668 b hb)
def height_622_i0 : ℕ := 5
def childrenH_622_i0 : Fin 2 → ℕ := ![height_41, height_56]
theorem height_exact_622_i0 : height_622_i0 = 1 + Finset.univ.sup childrenH_622_i0 := by decide +kernel
theorem required_origin_622_i0 : ∀ x ∈ required_622_i0,
    (∃ j, x ∈ childrenC_622_i0 j) ∨ ∀ j, x ∈ childrenD_622_i0 j := by decide +kernel
theorem required_exact_622_i0 : required_622_i0 =
    ((Finset.univ.biUnion childrenC_622_i0) ∪ commonEnvelope childrenD_622_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_622_i0 childrenD_622_i0 (3, 6) required_622_i0
    (by decide +kernel) child_required_sub_622_i0 common_sub_622_i0 required_origin_622_i0
theorem envelope_origin_622_i0 : ∀ x ∈ envelope_622_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_622_i0 j := by decide +kernel
theorem envelope_exact_622_i0 : envelope_622_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_622_i0) := by
  exact envelope_eq_combination childrenD_622_i0 (3, 6) envelope_622_i0
    pivot_mem_622_i0 child_envelope_sub_622_i0 envelope_origin_622_i0
def checked_622_i0 : CheckedCard where
  required := required_622_i0
  envelope := envelope_622_i0
  height := height_622_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_622_i0
def height_622_i2 : ℕ := 5
def childrenH_622_i2 : Fin 2 → ℕ := ![height_4, height_41]
theorem height_exact_622_i2 : height_622_i2 = 1 + Finset.univ.sup childrenH_622_i2 := by decide +kernel
theorem required_origin_622_i2 : ∀ x ∈ required_622_i2,
    (∃ j, x ∈ childrenC_622_i2 j) ∨ ∀ j, x ∈ childrenD_622_i2 j := by decide +kernel
theorem required_exact_622_i2 : required_622_i2 =
    ((Finset.univ.biUnion childrenC_622_i2) ∪ commonEnvelope childrenD_622_i2).erase (3, 6) := by
  exact required_eq_combination childrenC_622_i2 childrenD_622_i2 (3, 6) required_622_i2
    (by decide +kernel) child_required_sub_622_i2 common_sub_622_i2 required_origin_622_i2
theorem envelope_origin_622_i2 : ∀ x ∈ envelope_622_i2,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_622_i2 j := by decide +kernel
theorem envelope_exact_622_i2 : envelope_622_i2 =
    insert (3, 6) (Finset.univ.biUnion childrenD_622_i2) := by
  exact envelope_eq_combination childrenD_622_i2 (3, 6) envelope_622_i2
    pivot_mem_622_i2 child_envelope_sub_622_i2 envelope_origin_622_i2
def checked_622_i2 : CheckedCard where
  required := required_622_i2
  envelope := envelope_622_i2
  height := height_622_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_622_i2
def height_622_i3 : ℕ := 3
def childrenH_622_i3 : Fin 2 → ℕ := ![height_5, height_11]
theorem height_exact_622_i3 : height_622_i3 = 1 + Finset.univ.sup childrenH_622_i3 := by decide +kernel
theorem required_origin_622_i3 : ∀ x ∈ required_622_i3,
    (∃ j, x ∈ childrenC_622_i3 j) ∨ ∀ j, x ∈ childrenD_622_i3 j := by decide +kernel
theorem required_exact_622_i3 : required_622_i3 =
    ((Finset.univ.biUnion childrenC_622_i3) ∪ commonEnvelope childrenD_622_i3).erase (3, 2) := by
  exact required_eq_combination childrenC_622_i3 childrenD_622_i3 (3, 2) required_622_i3
    (by decide +kernel) child_required_sub_622_i3 common_sub_622_i3 required_origin_622_i3
theorem envelope_origin_622_i3 : ∀ x ∈ envelope_622_i3,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_622_i3 j := by decide +kernel
theorem envelope_exact_622_i3 : envelope_622_i3 =
    insert (3, 2) (Finset.univ.biUnion childrenD_622_i3) := by
  exact envelope_eq_combination childrenD_622_i3 (3, 2) envelope_622_i3
    pivot_mem_622_i3 child_envelope_sub_622_i3 envelope_origin_622_i3
def checked_622_i3 : CheckedCard where
  required := required_622_i3
  envelope := envelope_622_i3
  height := height_622_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_622_i3
def height_622_i1 : ℕ := 6
def childrenH_622_i1 : Fin 3 → ℕ := ![height_61, height_622_i2, height_622_i3]
theorem height_exact_622_i1 : height_622_i1 = 1 + Finset.univ.sup childrenH_622_i1 := by decide +kernel
theorem required_origin_622_i1 : ∀ x ∈ required_622_i1,
    (∃ j, x ∈ childrenC_622_i1 j) ∨ ∀ j, x ∈ childrenD_622_i1 j := by decide +kernel
theorem required_exact_622_i1 : required_622_i1 =
    ((Finset.univ.biUnion childrenC_622_i1) ∪ commonEnvelope childrenD_622_i1).erase (2, 2) := by
  exact required_eq_combination childrenC_622_i1 childrenD_622_i1 (2, 2) required_622_i1
    (by decide +kernel) child_required_sub_622_i1 common_sub_622_i1 required_origin_622_i1
theorem envelope_origin_622_i1 : ∀ x ∈ envelope_622_i1,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_622_i1 j := by decide +kernel
theorem envelope_exact_622_i1 : envelope_622_i1 =
    insert (2, 2) (Finset.univ.biUnion childrenD_622_i1) := by
  exact envelope_eq_combination childrenD_622_i1 (2, 2) envelope_622_i1
    pivot_mem_622_i1 child_envelope_sub_622_i1 envelope_origin_622_i1
def checked_622_i1 : CheckedCard where
  required := required_622_i1
  envelope := envelope_622_i1
  height := height_622_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_622_i1
def height_622_i4 : ℕ := 8
def childrenH_622_i4 : Fin 2 → ℕ := ![height_23, height_621]
theorem height_exact_622_i4 : height_622_i4 = 1 + Finset.univ.sup childrenH_622_i4 := by decide +kernel
theorem required_origin_622_i4 : ∀ x ∈ required_622_i4,
    (∃ j, x ∈ childrenC_622_i4 j) ∨ ∀ j, x ∈ childrenD_622_i4 j := by decide +kernel
theorem required_exact_622_i4 : required_622_i4 =
    ((Finset.univ.biUnion childrenC_622_i4) ∪ commonEnvelope childrenD_622_i4).erase (4, 5) := by
  exact required_eq_combination childrenC_622_i4 childrenD_622_i4 (4, 5) required_622_i4
    (by decide +kernel) child_required_sub_622_i4 common_sub_622_i4 required_origin_622_i4
theorem envelope_origin_622_i4 : ∀ x ∈ envelope_622_i4,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_622_i4 j := by decide +kernel
theorem envelope_exact_622_i4 : envelope_622_i4 =
    insert (4, 5) (Finset.univ.biUnion childrenD_622_i4) := by
  exact envelope_eq_combination childrenD_622_i4 (4, 5) envelope_622_i4
    pivot_mem_622_i4 child_envelope_sub_622_i4 envelope_origin_622_i4
def checked_622_i4 : CheckedCard where
  required := required_622_i4
  envelope := envelope_622_i4
  height := height_622_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_622_i4
def height_622 : ℕ := 9
def childrenH_622 : Fin 4 → ℕ := ![height_57, height_622_i0, height_622_i1, height_622_i4]
theorem height_exact_622 : height_622 = 1 + Finset.univ.sup childrenH_622 := by decide +kernel
theorem required_origin_622 : ∀ x ∈ required_622,
    (∃ j, x ∈ childrenC_622 j) ∨ ∀ j, x ∈ childrenD_622 j := by decide +kernel
theorem required_exact_622 : required_622 =
    ((Finset.univ.biUnion childrenC_622) ∪ commonEnvelope childrenD_622).erase (4, 4) := by
  exact required_eq_combination childrenC_622 childrenD_622 (4, 4) required_622
    (by decide +kernel) child_required_sub_622 common_sub_622 required_origin_622
theorem envelope_origin_622 : ∀ x ∈ envelope_622,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_622 j := by decide +kernel
theorem envelope_exact_622 : envelope_622 =
    insert (4, 4) (Finset.univ.biUnion childrenD_622) := by
  exact envelope_eq_combination childrenD_622 (4, 4) envelope_622
    pivot_mem_622 child_envelope_sub_622 envelope_origin_622
def checked_622 : CheckedCard where
  required := required_622
  envelope := envelope_622
  height := height_622
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_622
def height_629 : ℕ := 9
def childrenH_629 : Fin 5 → ℕ := ![height_190, height_295, height_364, height_518, height_628]
theorem height_exact_629 : height_629 = 1 + Finset.univ.sup childrenH_629 := by decide +kernel
theorem required_origin_629 : ∀ x ∈ required_629,
    (∃ j, x ∈ childrenC_629 j) ∨ ∀ j, x ∈ childrenD_629 j := by decide +kernel
theorem required_exact_629 : required_629 =
    ((Finset.univ.biUnion childrenC_629) ∪ commonEnvelope childrenD_629).erase (3, 5) := by
  exact required_eq_combination childrenC_629 childrenD_629 (3, 5) required_629
    (by decide +kernel) child_required_sub_629 common_sub_629 required_origin_629
theorem envelope_origin_629 : ∀ x ∈ envelope_629,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_629 j := by decide +kernel
theorem envelope_exact_629 : envelope_629 =
    insert (3, 5) (Finset.univ.biUnion childrenD_629) := by
  exact envelope_eq_combination childrenD_629 (3, 5) envelope_629
    pivot_mem_629 child_envelope_sub_629 envelope_origin_629
def checked_629 : CheckedCard where
  required := required_629
  envelope := envelope_629
  height := height_629
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_629
def height_638_i0 : ℕ := 7
def childrenH_638_i0 : Fin 2 → ℕ := ![height_15, height_85]
theorem height_exact_638_i0 : height_638_i0 = 1 + Finset.univ.sup childrenH_638_i0 := by decide +kernel
theorem required_origin_638_i0 : ∀ x ∈ required_638_i0,
    (∃ j, x ∈ childrenC_638_i0 j) ∨ ∀ j, x ∈ childrenD_638_i0 j := by decide +kernel
theorem required_exact_638_i0 : required_638_i0 =
    ((Finset.univ.biUnion childrenC_638_i0) ∪ commonEnvelope childrenD_638_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_638_i0 childrenD_638_i0 (3, 4) required_638_i0
    (by decide +kernel) child_required_sub_638_i0 common_sub_638_i0 required_origin_638_i0
theorem envelope_origin_638_i0 : ∀ x ∈ envelope_638_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_638_i0 j := by decide +kernel
theorem envelope_exact_638_i0 : envelope_638_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_638_i0) := by
  exact envelope_eq_combination childrenD_638_i0 (3, 4) envelope_638_i0
    pivot_mem_638_i0 child_envelope_sub_638_i0 envelope_origin_638_i0
def checked_638_i0 : CheckedCard where
  required := required_638_i0
  envelope := envelope_638_i0
  height := height_638_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_638_i0
def height_638 : ℕ := 9
def childrenH_638 : Fin 6 → ℕ := ![height_57, height_136, height_217, height_530, height_638_i0, height_637]
theorem height_exact_638 : height_638 = 1 + Finset.univ.sup childrenH_638 := by decide +kernel
theorem required_origin_638 : ∀ x ∈ required_638,
    (∃ j, x ∈ childrenC_638 j) ∨ ∀ j, x ∈ childrenD_638 j := by decide +kernel
theorem required_exact_638 : required_638 =
    ((Finset.univ.biUnion childrenC_638) ∪ commonEnvelope childrenD_638).erase (3, 3) := by
  exact required_eq_combination childrenC_638 childrenD_638 (3, 3) required_638
    (by decide +kernel) child_required_sub_638 common_sub_638 required_origin_638
theorem envelope_origin_638 : ∀ x ∈ envelope_638,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_638 j := by decide +kernel
theorem envelope_exact_638 : envelope_638 =
    insert (3, 3) (Finset.univ.biUnion childrenD_638) := by
  exact envelope_eq_combination childrenD_638 (3, 3) envelope_638
    pivot_mem_638 child_envelope_sub_638 envelope_origin_638
def checked_638 : CheckedCard where
  required := required_638
  envelope := envelope_638
  height := height_638
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_638
def height_640_i3 : ℕ := 5
def childrenH_640_i3 : Fin 2 → ℕ := ![height_5, height_90]
theorem height_exact_640_i3 : height_640_i3 = 1 + Finset.univ.sup childrenH_640_i3 := by decide +kernel
theorem required_origin_640_i3 : ∀ x ∈ required_640_i3,
    (∃ j, x ∈ childrenC_640_i3 j) ∨ ∀ j, x ∈ childrenD_640_i3 j := by decide +kernel
theorem required_exact_640_i3 : required_640_i3 =
    ((Finset.univ.biUnion childrenC_640_i3) ∪ commonEnvelope childrenD_640_i3).erase (5, 6) := by
  exact required_eq_combination childrenC_640_i3 childrenD_640_i3 (5, 6) required_640_i3
    (by decide +kernel) child_required_sub_640_i3 common_sub_640_i3 required_origin_640_i3
theorem envelope_origin_640_i3 : ∀ x ∈ envelope_640_i3,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_640_i3 j := by decide +kernel
theorem envelope_exact_640_i3 : envelope_640_i3 =
    insert (5, 6) (Finset.univ.biUnion childrenD_640_i3) := by
  exact envelope_eq_combination childrenD_640_i3 (5, 6) envelope_640_i3
    pivot_mem_640_i3 child_envelope_sub_640_i3 envelope_origin_640_i3
def checked_640_i3 : CheckedCard where
  required := required_640_i3
  envelope := envelope_640_i3
  height := height_640_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_640_i3
def height_640_i2 : ℕ := 6
def childrenH_640_i2 : Fin 3 → ℕ := ![height_44, height_260, height_640_i3]
theorem height_exact_640_i2 : height_640_i2 = 1 + Finset.univ.sup childrenH_640_i2 := by decide +kernel
theorem required_origin_640_i2 : ∀ x ∈ required_640_i2,
    (∃ j, x ∈ childrenC_640_i2 j) ∨ ∀ j, x ∈ childrenD_640_i2 j := by decide +kernel
theorem required_exact_640_i2 : required_640_i2 =
    ((Finset.univ.biUnion childrenC_640_i2) ∪ commonEnvelope childrenD_640_i2).erase (2, 6) := by
  exact required_eq_combination childrenC_640_i2 childrenD_640_i2 (2, 6) required_640_i2
    (by decide +kernel) child_required_sub_640_i2 common_sub_640_i2 required_origin_640_i2
theorem envelope_origin_640_i2 : ∀ x ∈ envelope_640_i2,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_640_i2 j := by decide +kernel
theorem envelope_exact_640_i2 : envelope_640_i2 =
    insert (2, 6) (Finset.univ.biUnion childrenD_640_i2) := by
  exact envelope_eq_combination childrenD_640_i2 (2, 6) envelope_640_i2
    pivot_mem_640_i2 child_envelope_sub_640_i2 envelope_origin_640_i2
def checked_640_i2 : CheckedCard where
  required := required_640_i2
  envelope := envelope_640_i2
  height := height_640_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_640_i2
def height_640_i1 : ℕ := 7
def childrenH_640_i1 : Fin 2 → ℕ := ![height_5, height_640_i2]
theorem height_exact_640_i1 : height_640_i1 = 1 + Finset.univ.sup childrenH_640_i1 := by decide +kernel
theorem required_origin_640_i1 : ∀ x ∈ required_640_i1,
    (∃ j, x ∈ childrenC_640_i1 j) ∨ ∀ j, x ∈ childrenD_640_i1 j := by decide +kernel
theorem required_exact_640_i1 : required_640_i1 =
    ((Finset.univ.biUnion childrenC_640_i1) ∪ commonEnvelope childrenD_640_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_640_i1 childrenD_640_i1 (4, 6) required_640_i1
    (by decide +kernel) child_required_sub_640_i1 common_sub_640_i1 required_origin_640_i1
theorem envelope_origin_640_i1 : ∀ x ∈ envelope_640_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_640_i1 j := by decide +kernel
theorem envelope_exact_640_i1 : envelope_640_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_640_i1) := by
  exact envelope_eq_combination childrenD_640_i1 (4, 6) envelope_640_i1
    pivot_mem_640_i1 child_envelope_sub_640_i1 envelope_origin_640_i1
def checked_640_i1 : CheckedCard where
  required := required_640_i1
  envelope := envelope_640_i1
  height := height_640_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_640_i1
def height_640_i0 : ℕ := 8
def childrenH_640_i0 : Fin 4 → ℕ := ![height_61, height_89, height_183, height_640_i1]
theorem height_exact_640_i0 : height_640_i0 = 1 + Finset.univ.sup childrenH_640_i0 := by decide +kernel
theorem required_origin_640_i0 : ∀ x ∈ required_640_i0,
    (∃ j, x ∈ childrenC_640_i0 j) ∨ ∀ j, x ∈ childrenD_640_i0 j := by decide +kernel
theorem required_exact_640_i0 : required_640_i0 =
    ((Finset.univ.biUnion childrenC_640_i0) ∪ commonEnvelope childrenD_640_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_640_i0 childrenD_640_i0 (3, 6) required_640_i0
    (by decide +kernel) child_required_sub_640_i0 common_sub_640_i0 required_origin_640_i0
theorem envelope_origin_640_i0 : ∀ x ∈ envelope_640_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_640_i0 j := by decide +kernel
theorem envelope_exact_640_i0 : envelope_640_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_640_i0) := by
  exact envelope_eq_combination childrenD_640_i0 (3, 6) envelope_640_i0
    pivot_mem_640_i0 child_envelope_sub_640_i0 envelope_origin_640_i0
def checked_640_i0 : CheckedCard where
  required := required_640_i0
  envelope := envelope_640_i0
  height := height_640_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_640_i0
def height_640 : ℕ := 9
def childrenH_640 : Fin 4 → ℕ := ![height_10, height_47, height_52, height_640_i0]
theorem height_exact_640 : height_640 = 1 + Finset.univ.sup childrenH_640 := by decide +kernel
theorem required_origin_640 : ∀ x ∈ required_640,
    (∃ j, x ∈ childrenC_640 j) ∨ ∀ j, x ∈ childrenD_640 j := by decide +kernel
theorem required_exact_640 : required_640 =
    ((Finset.univ.biUnion childrenC_640) ∪ commonEnvelope childrenD_640).erase (4, 5) := by
  exact required_eq_combination childrenC_640 childrenD_640 (4, 5) required_640
    (by decide +kernel) child_required_sub_640 common_sub_640 required_origin_640
theorem envelope_origin_640 : ∀ x ∈ envelope_640,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_640 j := by decide +kernel
theorem envelope_exact_640 : envelope_640 =
    insert (4, 5) (Finset.univ.biUnion childrenD_640) := by
  exact envelope_eq_combination childrenD_640 (4, 5) envelope_640
    pivot_mem_640 child_envelope_sub_640 envelope_origin_640
def checked_640 : CheckedCard where
  required := required_640
  envelope := envelope_640
  height := height_640
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_640
def height_655_i0 : ℕ := 8
def childrenH_655_i0 : Fin 3 → ℕ := ![height_179, height_314, height_344]
theorem height_exact_655_i0 : height_655_i0 = 1 + Finset.univ.sup childrenH_655_i0 := by decide +kernel
theorem required_origin_655_i0 : ∀ x ∈ required_655_i0,
    (∃ j, x ∈ childrenC_655_i0 j) ∨ ∀ j, x ∈ childrenD_655_i0 j := by decide +kernel
theorem required_exact_655_i0 : required_655_i0 =
    ((Finset.univ.biUnion childrenC_655_i0) ∪ commonEnvelope childrenD_655_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_655_i0 childrenD_655_i0 (3, 6) required_655_i0
    (by decide +kernel) child_required_sub_655_i0 common_sub_655_i0 required_origin_655_i0
theorem envelope_origin_655_i0 : ∀ x ∈ envelope_655_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_655_i0 j := by decide +kernel
theorem envelope_exact_655_i0 : envelope_655_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_655_i0) := by
  exact envelope_eq_combination childrenD_655_i0 (3, 6) envelope_655_i0
    pivot_mem_655_i0 child_envelope_sub_655_i0 envelope_origin_655_i0
def checked_655_i0 : CheckedCard where
  required := required_655_i0
  envelope := envelope_655_i0
  height := height_655_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_655_i0
def height_655 : ℕ := 9
def childrenH_655 : Fin 4 → ℕ := ![height_10, height_52, height_435, height_655_i0]
theorem height_exact_655 : height_655 = 1 + Finset.univ.sup childrenH_655 := by decide +kernel
theorem required_origin_655 : ∀ x ∈ required_655,
    (∃ j, x ∈ childrenC_655 j) ∨ ∀ j, x ∈ childrenD_655 j := by decide +kernel
theorem required_exact_655 : required_655 =
    ((Finset.univ.biUnion childrenC_655) ∪ commonEnvelope childrenD_655).erase (3, 3) := by
  exact required_eq_combination childrenC_655 childrenD_655 (3, 3) required_655
    (by decide +kernel) child_required_sub_655 common_sub_655 required_origin_655
theorem envelope_origin_655 : ∀ x ∈ envelope_655,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_655 j := by decide +kernel
theorem envelope_exact_655 : envelope_655 =
    insert (3, 3) (Finset.univ.biUnion childrenD_655) := by
  exact envelope_eq_combination childrenD_655 (3, 3) envelope_655
    pivot_mem_655 child_envelope_sub_655 envelope_origin_655
def checked_655 : CheckedCard where
  required := required_655
  envelope := envelope_655
  height := height_655
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_655
def height_659 : ℕ := 9
def childrenH_659 : Fin 2 → ℕ := ![height_5, height_658]
theorem height_exact_659 : height_659 = 1 + Finset.univ.sup childrenH_659 := by decide +kernel
theorem required_origin_659 : ∀ x ∈ required_659,
    (∃ j, x ∈ childrenC_659 j) ∨ ∀ j, x ∈ childrenD_659 j := by decide +kernel
theorem required_exact_659 : required_659 =
    ((Finset.univ.biUnion childrenC_659) ∪ commonEnvelope childrenD_659).erase (3, 4) := by
  exact required_eq_combination childrenC_659 childrenD_659 (3, 4) required_659
    (by decide +kernel) child_required_sub_659 common_sub_659 required_origin_659
theorem envelope_origin_659 : ∀ x ∈ envelope_659,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_659 j := by decide +kernel
theorem envelope_exact_659 : envelope_659 =
    insert (3, 4) (Finset.univ.biUnion childrenD_659) := by
  exact envelope_eq_combination childrenD_659 (3, 4) envelope_659
    pivot_mem_659 child_envelope_sub_659 envelope_origin_659
def checked_659 : CheckedCard where
  required := required_659
  envelope := envelope_659
  height := height_659
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_659
def height_662_i0 : ℕ := 5
def childrenH_662_i0 : Fin 2 → ℕ := ![height_5, height_141]
theorem height_exact_662_i0 : height_662_i0 = 1 + Finset.univ.sup childrenH_662_i0 := by decide +kernel
theorem required_origin_662_i0 : ∀ x ∈ required_662_i0,
    (∃ j, x ∈ childrenC_662_i0 j) ∨ ∀ j, x ∈ childrenD_662_i0 j := by decide +kernel
theorem required_exact_662_i0 : required_662_i0 =
    ((Finset.univ.biUnion childrenC_662_i0) ∪ commonEnvelope childrenD_662_i0).erase (1, 5) := by
  exact required_eq_combination childrenC_662_i0 childrenD_662_i0 (1, 5) required_662_i0
    (by decide +kernel) child_required_sub_662_i0 common_sub_662_i0 required_origin_662_i0
theorem envelope_origin_662_i0 : ∀ x ∈ envelope_662_i0,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_662_i0 j := by decide +kernel
theorem envelope_exact_662_i0 : envelope_662_i0 =
    insert (1, 5) (Finset.univ.biUnion childrenD_662_i0) := by
  exact envelope_eq_combination childrenD_662_i0 (1, 5) envelope_662_i0
    pivot_mem_662_i0 child_envelope_sub_662_i0 envelope_origin_662_i0
def checked_662_i0 : CheckedCard where
  required := required_662_i0
  envelope := envelope_662_i0
  height := height_662_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_662_i0
def height_662 : ℕ := 9
def childrenH_662 : Fin 3 → ℕ := ![height_52, height_658, height_662_i0]
theorem height_exact_662 : height_662 = 1 + Finset.univ.sup childrenH_662 := by decide +kernel
theorem required_origin_662 : ∀ x ∈ required_662,
    (∃ j, x ∈ childrenC_662 j) ∨ ∀ j, x ∈ childrenD_662 j := by decide +kernel
theorem required_exact_662 : required_662 =
    ((Finset.univ.biUnion childrenC_662) ∪ commonEnvelope childrenD_662).erase (4, 4) := by
  exact required_eq_combination childrenC_662 childrenD_662 (4, 4) required_662
    (by decide +kernel) child_required_sub_662 common_sub_662 required_origin_662
theorem envelope_origin_662 : ∀ x ∈ envelope_662,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_662 j := by decide +kernel
theorem envelope_exact_662 : envelope_662 =
    insert (4, 4) (Finset.univ.biUnion childrenD_662) := by
  exact envelope_eq_combination childrenD_662 (4, 4) envelope_662
    pivot_mem_662 child_envelope_sub_662 envelope_origin_662
def checked_662 : CheckedCard where
  required := required_662
  envelope := envelope_662
  height := height_662
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_662
def height_667 : ℕ := 9
def childrenH_667 : Fin 3 → ℕ := ![height_7, height_9, height_666]
theorem height_exact_667 : height_667 = 1 + Finset.univ.sup childrenH_667 := by decide +kernel
theorem required_origin_667 : ∀ x ∈ required_667,
    (∃ j, x ∈ childrenC_667 j) ∨ ∀ j, x ∈ childrenD_667 j := by decide +kernel
theorem required_exact_667 : required_667 =
    ((Finset.univ.biUnion childrenC_667) ∪ commonEnvelope childrenD_667).erase (3, 4) := by
  exact required_eq_combination childrenC_667 childrenD_667 (3, 4) required_667
    (by decide +kernel) child_required_sub_667 common_sub_667 required_origin_667
theorem envelope_origin_667 : ∀ x ∈ envelope_667,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_667 j := by decide +kernel
theorem envelope_exact_667 : envelope_667 =
    insert (3, 4) (Finset.univ.biUnion childrenD_667) := by
  exact envelope_eq_combination childrenD_667 (3, 4) envelope_667
    pivot_mem_667 child_envelope_sub_667 envelope_origin_667
def checked_667 : CheckedCard where
  required := required_667
  envelope := envelope_667
  height := height_667
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_667
def height_668 : ℕ := 9
def childrenH_668 : Fin 3 → ℕ := ![height_7, height_9, height_666]
theorem height_exact_668 : height_668 = 1 + Finset.univ.sup childrenH_668 := by decide +kernel
theorem required_origin_668 : ∀ x ∈ required_668,
    (∃ j, x ∈ childrenC_668 j) ∨ ∀ j, x ∈ childrenD_668 j := by decide +kernel
theorem required_exact_668 : required_668 =
    ((Finset.univ.biUnion childrenC_668) ∪ commonEnvelope childrenD_668).erase (3, 4) := by
  exact required_eq_combination childrenC_668 childrenD_668 (3, 4) required_668
    (by decide +kernel) child_required_sub_668 common_sub_668 required_origin_668
theorem envelope_origin_668 : ∀ x ∈ envelope_668,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_668 j := by decide +kernel
theorem envelope_exact_668 : envelope_668 =
    insert (3, 4) (Finset.univ.biUnion childrenD_668) := by
  exact envelope_eq_combination childrenD_668 (3, 4) envelope_668
    pivot_mem_668 child_envelope_sub_668 envelope_origin_668
def checked_668 : CheckedCard where
  required := required_668
  envelope := envelope_668
  height := height_668
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_668
end SnakyPrototype.Certificate21

end OAI
