import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part08
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_652_i3 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (3, 3), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_652_i3 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (3, 2), (3, 3), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_652_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) required_0), (placed21 2 (5, 2) required_245)]
def childrenD_652_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) envelope_0), (placed21 2 (5, 2) envelope_245)]
theorem common_sub_652_i3 : commonEnvelope childrenD_652_i3 ⊆ insert (3, 5) required_652_i3 := by decide +kernel
theorem child_required_sub_652_i3 : ∀ j, childrenC_652_i3 j ⊆ insert (3, 5) required_652_i3 := by decide +kernel
theorem child_envelope_sub_652_i3 : ∀ j, childrenD_652_i3 j ⊆ envelope_652_i3 := by decide +kernel
theorem pivot_mem_652_i3 : (3, 5) ∈ envelope_652_i3 := by decide +kernel
theorem children_work_652_i3 : ∀ j, Template HasSnaky 3 (childrenC_652_i3 j) (childrenD_652_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_245 2 (5, 2)).mono (by decide +kernel)
theorem row_works_652_i3 : Template HasSnaky 4 required_652_i3 envelope_652_i3 := by
  refine compose HasSnaky 3 childrenC_652_i3 childrenD_652_i3 children_work_652_i3 (3, 5)
    required_652_i3 envelope_652_i3 pivot_mem_652_i3 child_required_sub_652_i3 child_envelope_sub_652_i3 ?_
  intro b hb
  exact common_sub_652_i3 (mem_commonEnvelope childrenD_652_i3 b hb)
def required_652_i2 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_652_i2 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_652_i2 : Fin 3 → Finset Cell := ![(placed21 1 (1, 4) required_36), (placed21 6 (4, 6) required_44), required_652_i3]
def childrenD_652_i2 : Fin 3 → Finset Cell := ![(placed21 1 (1, 4) envelope_36), (placed21 6 (4, 6) envelope_44), envelope_652_i3]
theorem common_sub_652_i2 : commonEnvelope childrenD_652_i2 ⊆ insert (4, 5) required_652_i2 := by decide +kernel
theorem child_required_sub_652_i2 : ∀ j, childrenC_652_i2 j ⊆ insert (4, 5) required_652_i2 := by decide +kernel
theorem child_envelope_sub_652_i2 : ∀ j, childrenD_652_i2 j ⊆ envelope_652_i2 := by decide +kernel
theorem pivot_mem_652_i2 : (4, 5) ∈ envelope_652_i2 := by decide +kernel
theorem children_work_652_i2 : ∀ j, Template HasSnaky 4 (childrenC_652_i2 j) (childrenD_652_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_36 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 6 (4, 6)).mono (by decide +kernel)
  · exact row_works_652_i3.mono (by decide +kernel)
theorem row_works_652_i2 : Template HasSnaky 5 required_652_i2 envelope_652_i2 := by
  refine compose HasSnaky 4 childrenC_652_i2 childrenD_652_i2 children_work_652_i2 (4, 5)
    required_652_i2 envelope_652_i2 pivot_mem_652_i2 child_required_sub_652_i2 child_envelope_sub_652_i2 ?_
  intro b hb
  exact common_sub_652_i2 (mem_commonEnvelope childrenD_652_i2 b hb)
def required_652_i1 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (2, 5), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_652_i1 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_652_i1 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_222), required_652_i2]
def childrenD_652_i1 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_222), envelope_652_i2]
theorem common_sub_652_i1 : commonEnvelope childrenD_652_i1 ⊆ insert (4, 4) required_652_i1 := by decide +kernel
theorem child_required_sub_652_i1 : ∀ j, childrenC_652_i1 j ⊆ insert (4, 4) required_652_i1 := by decide +kernel
theorem child_envelope_sub_652_i1 : ∀ j, childrenD_652_i1 j ⊆ envelope_652_i1 := by decide +kernel
theorem pivot_mem_652_i1 : (4, 4) ∈ envelope_652_i1 := by decide +kernel
theorem children_work_652_i1 : ∀ j, Template HasSnaky 5 (childrenC_652_i1 j) (childrenD_652_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_222 3 (0, 5)).mono (by decide +kernel)
  · exact row_works_652_i2.mono (by decide +kernel)
theorem row_works_652_i1 : Template HasSnaky 6 required_652_i1 envelope_652_i1 := by
  refine compose HasSnaky 5 childrenC_652_i1 childrenD_652_i1 children_work_652_i1 (4, 4)
    required_652_i1 envelope_652_i1 pivot_mem_652_i1 child_required_sub_652_i1 child_envelope_sub_652_i1 ?_
  intro b hb
  exact common_sub_652_i1 (mem_commonEnvelope childrenD_652_i1 b hb)
def required_652_i0 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_652_i0 : Finset Cell := ⟨(([(0, 2), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_652_i0 : Fin 3 → Finset Cell := ![(placed21 2 (3, 2) required_10), (placed21 1 (0, 3) required_558), required_652_i1]
def childrenD_652_i0 : Fin 3 → Finset Cell := ![(placed21 2 (3, 2) envelope_10), (placed21 1 (0, 3) envelope_558), envelope_652_i1]
theorem common_sub_652_i0 : commonEnvelope childrenD_652_i0 ⊆ insert (2, 5) required_652_i0 := by decide +kernel
theorem child_required_sub_652_i0 : ∀ j, childrenC_652_i0 j ⊆ insert (2, 5) required_652_i0 := by decide +kernel
theorem child_envelope_sub_652_i0 : ∀ j, childrenD_652_i0 j ⊆ envelope_652_i0 := by decide +kernel
theorem pivot_mem_652_i0 : (2, 5) ∈ envelope_652_i0 := by decide +kernel
theorem children_work_652_i0 : ∀ j, Template HasSnaky 8 (childrenC_652_i0 j) (childrenD_652_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 1 (0, 3)).mono (by decide +kernel)
  · exact row_works_652_i1.mono (by decide +kernel)
theorem row_works_652_i0 : Template HasSnaky 9 required_652_i0 envelope_652_i0 := by
  refine compose HasSnaky 8 childrenC_652_i0 childrenD_652_i0 children_work_652_i0 (2, 5)
    required_652_i0 envelope_652_i0 pivot_mem_652_i0 child_required_sub_652_i0 child_envelope_sub_652_i0 ?_
  intro b hb
  exact common_sub_652_i0 (mem_commonEnvelope childrenD_652_i0 b hb)
def required_652 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_652 : Finset Cell := ⟨(([(0, 2), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_652 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) required_0), required_652_i0]
def childrenD_652 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) envelope_0), envelope_652_i0]
theorem common_sub_652 : commonEnvelope childrenD_652 ⊆ insert (4, 3) required_652 := by decide +kernel
theorem child_required_sub_652 : ∀ j, childrenC_652 j ⊆ insert (4, 3) required_652 := by decide +kernel
theorem child_envelope_sub_652 : ∀ j, childrenD_652 j ⊆ envelope_652 := by decide +kernel
theorem pivot_mem_652 : (4, 3) ∈ envelope_652 := by decide +kernel
theorem children_work_652 : ∀ j, Template HasSnaky 9 (childrenC_652 j) (childrenD_652 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (5, 3)).mono (by decide +kernel)
  · exact row_works_652_i0.mono (by decide +kernel)
theorem row_works_652 : Template HasSnaky 10 required_652 envelope_652 := by
  refine compose HasSnaky 9 childrenC_652 childrenD_652 children_work_652 (4, 3)
    required_652 envelope_652 pivot_mem_652 child_required_sub_652 child_envelope_sub_652 ?_
  intro b hb
  exact common_sub_652 (mem_commonEnvelope childrenD_652 b hb)
def required_674 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_674 : Finset Cell := ⟨(([(0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 4), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_674 : Fin 3 → Finset Cell := ![(placed21 2 (2, 2) required_34), (placed21 0 (1, 2) required_149), required_673]
def childrenD_674 : Fin 3 → Finset Cell := ![(placed21 2 (2, 2) envelope_34), (placed21 0 (1, 2) envelope_149), envelope_673]
theorem common_sub_674 : commonEnvelope childrenD_674 ⊆ insert (2, 4) required_674 := by decide +kernel
theorem child_required_sub_674 : ∀ j, childrenC_674 j ⊆ insert (2, 4) required_674 := by decide +kernel
theorem child_envelope_sub_674 : ∀ j, childrenD_674 j ⊆ envelope_674 := by decide +kernel
theorem pivot_mem_674 : (2, 4) ∈ envelope_674 := by decide +kernel
theorem children_work_674 : ∀ j, Template HasSnaky 9 (childrenC_674 j) (childrenD_674 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_149 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_673.mono (by decide +kernel)
theorem row_works_674 : Template HasSnaky 10 required_674 envelope_674 := by
  refine compose HasSnaky 9 childrenC_674 childrenD_674 children_work_674 (2, 4)
    required_674 envelope_674 pivot_mem_674 child_required_sub_674 child_envelope_sub_674 ?_
  intro b hb
  exact common_sub_674 (mem_commonEnvelope childrenD_674 b hb)
def required_702_i1 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (2, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_702_i1 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_702_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_15), (placed21 1 (0, 1) required_40)]
def childrenD_702_i1 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_15), (placed21 1 (0, 1) envelope_40)]
theorem common_sub_702_i1 : commonEnvelope childrenD_702_i1 ⊆ insert (1, 1) required_702_i1 := by decide +kernel
theorem child_required_sub_702_i1 : ∀ j, childrenC_702_i1 j ⊆ insert (1, 1) required_702_i1 := by decide +kernel
theorem child_envelope_sub_702_i1 : ∀ j, childrenD_702_i1 j ⊆ envelope_702_i1 := by decide +kernel
theorem pivot_mem_702_i1 : (1, 1) ∈ envelope_702_i1 := by decide +kernel
theorem children_work_702_i1 : ∀ j, Template HasSnaky 2 (childrenC_702_i1 j) (childrenD_702_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_40 1 (0, 1)).mono (by decide +kernel)
theorem row_works_702_i1 : Template HasSnaky 3 required_702_i1 envelope_702_i1 := by
  refine compose HasSnaky 2 childrenC_702_i1 childrenD_702_i1 children_work_702_i1 (1, 1)
    required_702_i1 envelope_702_i1 pivot_mem_702_i1 child_required_sub_702_i1 child_envelope_sub_702_i1 ?_
  intro b hb
  exact common_sub_702_i1 (mem_commonEnvelope childrenD_702_i1 b hb)
def required_702_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (2, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_702_i0 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_702_i0 : Fin 4 → Finset Cell := ![(placed21 1 (1, 2) required_30), required_108, required_702_i1, (placed21 0 (1, 0) required_511)]
def childrenD_702_i0 : Fin 4 → Finset Cell := ![(placed21 1 (1, 2) envelope_30), envelope_108, envelope_702_i1, (placed21 0 (1, 0) envelope_511)]
theorem common_sub_702_i0 : commonEnvelope childrenD_702_i0 ⊆ insert (4, 2) required_702_i0 := by decide +kernel
theorem child_required_sub_702_i0 : ∀ j, childrenC_702_i0 j ⊆ insert (4, 2) required_702_i0 := by decide +kernel
theorem child_envelope_sub_702_i0 : ∀ j, childrenD_702_i0 j ⊆ envelope_702_i0 := by decide +kernel
theorem pivot_mem_702_i0 : (4, 2) ∈ envelope_702_i0 := by decide +kernel
theorem children_work_702_i0 : ∀ j, Template HasSnaky 7 (childrenC_702_i0 j) (childrenD_702_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_108.mono (by decide +kernel)
  · exact row_works_702_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_511 0 (1, 0)).mono (by decide +kernel)
theorem row_works_702_i0 : Template HasSnaky 8 required_702_i0 envelope_702_i0 := by
  refine compose HasSnaky 7 childrenC_702_i0 childrenD_702_i0 children_work_702_i0 (4, 2)
    required_702_i0 envelope_702_i0 pivot_mem_702_i0 child_required_sub_702_i0 child_envelope_sub_702_i0 ?_
  intro b hb
  exact common_sub_702_i0 (mem_commonEnvelope childrenD_702_i0 b hb)
def required_702 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_702 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_702 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_22), (placed21 0 (0, 1) required_400), required_702_i0]
def childrenD_702 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_22), (placed21 0 (0, 1) envelope_400), envelope_702_i0]
theorem common_sub_702 : commonEnvelope childrenD_702 ⊆ insert (4, 3) required_702 := by decide +kernel
theorem child_required_sub_702 : ∀ j, childrenC_702 j ⊆ insert (4, 3) required_702 := by decide +kernel
theorem child_envelope_sub_702 : ∀ j, childrenD_702 j ⊆ envelope_702 := by decide +kernel
theorem pivot_mem_702 : (4, 3) ∈ envelope_702 := by decide +kernel
theorem children_work_702 : ∀ j, Template HasSnaky 9 (childrenC_702 j) (childrenD_702 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_400 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_702_i0.mono (by decide +kernel)
theorem row_works_702 : Template HasSnaky 10 required_702 envelope_702 := by
  refine compose HasSnaky 9 childrenC_702 childrenD_702 children_work_702 (4, 3)
    required_702 envelope_702 pivot_mem_702 child_required_sub_702 child_envelope_sub_702 ?_
  intro b hb
  exact common_sub_702 (mem_commonEnvelope childrenD_702 b hb)
def required_704_i1 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_704_i1 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 5), (3, 7), (3, 8), (3, 9), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_704_i1 : Fin 3 → Finset Cell := ![(placed21 5 (5, 4) required_28), (placed21 0 (1, 3) required_58), (placed21 0 (1, 2) required_306)]
def childrenD_704_i1 : Fin 3 → Finset Cell := ![(placed21 5 (5, 4) envelope_28), (placed21 0 (1, 3) envelope_58), (placed21 0 (1, 2) envelope_306)]
theorem common_sub_704_i1 : commonEnvelope childrenD_704_i1 ⊆ insert (4, 6) required_704_i1 := by decide +kernel
theorem child_required_sub_704_i1 : ∀ j, childrenC_704_i1 j ⊆ insert (4, 6) required_704_i1 := by decide +kernel
theorem child_envelope_sub_704_i1 : ∀ j, childrenD_704_i1 j ⊆ envelope_704_i1 := by decide +kernel
theorem pivot_mem_704_i1 : (4, 6) ∈ envelope_704_i1 := by decide +kernel
theorem children_work_704_i1 : ∀ j, Template HasSnaky 5 (childrenC_704_i1 j) (childrenD_704_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 5 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_306 0 (1, 2)).mono (by decide +kernel)
theorem row_works_704_i1 : Template HasSnaky 6 required_704_i1 envelope_704_i1 := by
  refine compose HasSnaky 5 childrenC_704_i1 childrenD_704_i1 children_work_704_i1 (4, 6)
    required_704_i1 envelope_704_i1 pivot_mem_704_i1 child_required_sub_704_i1 child_envelope_sub_704_i1 ?_
  intro b hb
  exact common_sub_704_i1 (mem_commonEnvelope childrenD_704_i1 b hb)
def required_704_i3 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_704_i3 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_704_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) required_2), (placed21 0 (4, 2) required_52)]
def childrenD_704_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) envelope_2), (placed21 0 (4, 2) envelope_52)]
theorem common_sub_704_i3 : commonEnvelope childrenD_704_i3 ⊆ insert (5, 5) required_704_i3 := by decide +kernel
theorem child_required_sub_704_i3 : ∀ j, childrenC_704_i3 j ⊆ insert (5, 5) required_704_i3 := by decide +kernel
theorem child_envelope_sub_704_i3 : ∀ j, childrenD_704_i3 j ⊆ envelope_704_i3 := by decide +kernel
theorem pivot_mem_704_i3 : (5, 5) ∈ envelope_704_i3 := by decide +kernel
theorem children_work_704_i3 : ∀ j, Template HasSnaky 3 (childrenC_704_i3 j) (childrenD_704_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 6 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (4, 2)).mono (by decide +kernel)
theorem row_works_704_i3 : Template HasSnaky 4 required_704_i3 envelope_704_i3 := by
  refine compose HasSnaky 3 childrenC_704_i3 childrenD_704_i3 children_work_704_i3 (5, 5)
    required_704_i3 envelope_704_i3 pivot_mem_704_i3 child_required_sub_704_i3 child_envelope_sub_704_i3 ?_
  intro b hb
  exact common_sub_704_i3 (mem_commonEnvelope childrenD_704_i3 b hb)
def required_704_i4 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_704_i4 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_704_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) required_2), (placed21 6 (5, 6) required_10)]
def childrenD_704_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) envelope_2), (placed21 6 (5, 6) envelope_10)]
theorem common_sub_704_i4 : commonEnvelope childrenD_704_i4 ⊆ insert (5, 5) required_704_i4 := by decide +kernel
theorem child_required_sub_704_i4 : ∀ j, childrenC_704_i4 j ⊆ insert (5, 5) required_704_i4 := by decide +kernel
theorem child_envelope_sub_704_i4 : ∀ j, childrenD_704_i4 j ⊆ envelope_704_i4 := by decide +kernel
theorem pivot_mem_704_i4 : (5, 5) ∈ envelope_704_i4 := by decide +kernel
theorem children_work_704_i4 : ∀ j, Template HasSnaky 4 (childrenC_704_i4 j) (childrenD_704_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 6 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_10 6 (5, 6)).mono (by decide +kernel)
theorem row_works_704_i4 : Template HasSnaky 5 required_704_i4 envelope_704_i4 := by
  refine compose HasSnaky 4 childrenC_704_i4 childrenD_704_i4 children_work_704_i4 (5, 5)
    required_704_i4 envelope_704_i4 pivot_mem_704_i4 child_required_sub_704_i4 child_envelope_sub_704_i4 ?_
  intro b hb
  exact common_sub_704_i4 (mem_commonEnvelope childrenD_704_i4 b hb)
def required_704_i5 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_704_i5 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_704_i5 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) required_25), (placed21 7 (5, 6) required_78)]
def childrenD_704_i5 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) envelope_25), (placed21 7 (5, 6) envelope_78)]
theorem common_sub_704_i5 : commonEnvelope childrenD_704_i5 ⊆ insert (4, 6) required_704_i5 := by decide +kernel
theorem child_required_sub_704_i5 : ∀ j, childrenC_704_i5 j ⊆ insert (4, 6) required_704_i5 := by decide +kernel
theorem child_envelope_sub_704_i5 : ∀ j, childrenD_704_i5 j ⊆ envelope_704_i5 := by decide +kernel
theorem pivot_mem_704_i5 : (4, 6) ∈ envelope_704_i5 := by decide +kernel
theorem children_work_704_i5 : ∀ j, Template HasSnaky 3 (childrenC_704_i5 j) (childrenD_704_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 7 (5, 6)).mono (by decide +kernel)
theorem row_works_704_i5 : Template HasSnaky 4 required_704_i5 envelope_704_i5 := by
  refine compose HasSnaky 3 childrenC_704_i5 childrenD_704_i5 children_work_704_i5 (4, 6)
    required_704_i5 envelope_704_i5 pivot_mem_704_i5 child_required_sub_704_i5 child_envelope_sub_704_i5 ?_
  intro b hb
  exact common_sub_704_i5 (mem_commonEnvelope childrenD_704_i5 b hb)
def required_704_i2 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_704_i2 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_704_i2 : Fin 4 → Finset Cell := ![(placed21 4 (1, 6) required_516), required_704_i3, required_704_i4, required_704_i5]
def childrenD_704_i2 : Fin 4 → Finset Cell := ![(placed21 4 (1, 6) envelope_516), envelope_704_i3, envelope_704_i4, envelope_704_i5]
theorem common_sub_704_i2 : commonEnvelope childrenD_704_i2 ⊆ insert (4, 3) required_704_i2 := by decide +kernel
theorem child_required_sub_704_i2 : ∀ j, childrenC_704_i2 j ⊆ insert (4, 3) required_704_i2 := by decide +kernel
theorem child_envelope_sub_704_i2 : ∀ j, childrenD_704_i2 j ⊆ envelope_704_i2 := by decide +kernel
theorem pivot_mem_704_i2 : (4, 3) ∈ envelope_704_i2 := by decide +kernel
theorem children_work_704_i2 : ∀ j, Template HasSnaky 6 (childrenC_704_i2 j) (childrenD_704_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_516 4 (1, 6)).mono (by decide +kernel)
  · exact row_works_704_i3.mono (by decide +kernel)
  · exact row_works_704_i4.mono (by decide +kernel)
  · exact row_works_704_i5.mono (by decide +kernel)
theorem row_works_704_i2 : Template HasSnaky 7 required_704_i2 envelope_704_i2 := by
  refine compose HasSnaky 6 childrenC_704_i2 childrenD_704_i2 children_work_704_i2 (4, 3)
    required_704_i2 envelope_704_i2 pivot_mem_704_i2 child_required_sub_704_i2 child_envelope_sub_704_i2 ?_
  intro b hb
  exact common_sub_704_i2 (mem_commonEnvelope childrenD_704_i2 b hb)
def required_704_i0 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_704_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_704_i0 : Fin 4 → Finset Cell := ![(placed21 3 (1, 5) required_30), required_704_i1, required_703, required_704_i2]
def childrenD_704_i0 : Fin 4 → Finset Cell := ![(placed21 3 (1, 5) envelope_30), envelope_704_i1, envelope_703, envelope_704_i2]
theorem common_sub_704_i0 : commonEnvelope childrenD_704_i0 ⊆ insert (4, 5) required_704_i0 := by decide +kernel
theorem child_required_sub_704_i0 : ∀ j, childrenC_704_i0 j ⊆ insert (4, 5) required_704_i0 := by decide +kernel
theorem child_envelope_sub_704_i0 : ∀ j, childrenD_704_i0 j ⊆ envelope_704_i0 := by decide +kernel
theorem pivot_mem_704_i0 : (4, 5) ∈ envelope_704_i0 := by decide +kernel
theorem children_work_704_i0 : ∀ j, Template HasSnaky 8 (childrenC_704_i0 j) (childrenD_704_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 3 (1, 5)).mono (by decide +kernel)
  · exact row_works_704_i1.mono (by decide +kernel)
  · exact row_works_703.mono (by decide +kernel)
  · exact row_works_704_i2.mono (by decide +kernel)
theorem row_works_704_i0 : Template HasSnaky 9 required_704_i0 envelope_704_i0 := by
  refine compose HasSnaky 8 childrenC_704_i0 childrenD_704_i0 children_work_704_i0 (4, 5)
    required_704_i0 envelope_704_i0 pivot_mem_704_i0 child_required_sub_704_i0 child_envelope_sub_704_i0 ?_
  intro b hb
  exact common_sub_704_i0 (mem_commonEnvelope childrenD_704_i0 b hb)
def required_704 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_704 : Finset Cell := ⟨(([(0, 1), (0, 5), (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_704 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) required_22), (placed21 4 (0, 6) required_400), required_704_i0]
def childrenD_704 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) envelope_22), (placed21 4 (0, 6) envelope_400), envelope_704_i0]
theorem common_sub_704 : commonEnvelope childrenD_704 ⊆ insert (4, 4) required_704 := by decide +kernel
theorem child_required_sub_704 : ∀ j, childrenC_704 j ⊆ insert (4, 4) required_704 := by decide +kernel
theorem child_envelope_sub_704 : ∀ j, childrenD_704 j ⊆ envelope_704 := by decide +kernel
theorem pivot_mem_704 : (4, 4) ∈ envelope_704 := by decide +kernel
theorem children_work_704 : ∀ j, Template HasSnaky 9 (childrenC_704 j) (childrenD_704 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_400 4 (0, 6)).mono (by decide +kernel)
  · exact row_works_704_i0.mono (by decide +kernel)
theorem row_works_704 : Template HasSnaky 10 required_704 envelope_704 := by
  refine compose HasSnaky 9 childrenC_704 childrenD_704 children_work_704 (4, 4)
    required_704 envelope_704 pivot_mem_704 child_required_sub_704 child_envelope_sub_704 ?_
  intro b hb
  exact common_sub_704 (mem_commonEnvelope childrenD_704 b hb)
def required_721_i4 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 6), (4, 6), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_721_i4 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 6), (4, 6), (5, 5), (5, 6), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_721_i4 : Fin 2 → Finset Cell := ![(placed21 4 (2, 6) required_5), (placed21 6 (5, 7) required_208)]
def childrenD_721_i4 : Fin 2 → Finset Cell := ![(placed21 4 (2, 6) envelope_5), (placed21 6 (5, 7) envelope_208)]
theorem common_sub_721_i4 : commonEnvelope childrenD_721_i4 ⊆ insert (2, 6) required_721_i4 := by decide +kernel
theorem child_required_sub_721_i4 : ∀ j, childrenC_721_i4 j ⊆ insert (2, 6) required_721_i4 := by decide +kernel
theorem child_envelope_sub_721_i4 : ∀ j, childrenD_721_i4 j ⊆ envelope_721_i4 := by decide +kernel
theorem pivot_mem_721_i4 : (2, 6) ∈ envelope_721_i4 := by decide +kernel
theorem children_work_721_i4 : ∀ j, Template HasSnaky 4 (childrenC_721_i4 j) (childrenD_721_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_208 6 (5, 7)).mono (by decide +kernel)
theorem row_works_721_i4 : Template HasSnaky 5 required_721_i4 envelope_721_i4 := by
  refine compose HasSnaky 4 childrenC_721_i4 childrenD_721_i4 children_work_721_i4 (2, 6)
    required_721_i4 envelope_721_i4 pivot_mem_721_i4 child_required_sub_721_i4 child_envelope_sub_721_i4 ?_
  intro b hb
  exact common_sub_721_i4 (mem_commonEnvelope childrenD_721_i4 b hb)
def required_721_i3 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 6), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_721_i3 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 6), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_721_i3 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) required_5), required_721_i4]
def childrenD_721_i3 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) envelope_5), envelope_721_i4]
theorem common_sub_721_i3 : commonEnvelope childrenD_721_i3 ⊆ insert (4, 6) required_721_i3 := by decide +kernel
theorem child_required_sub_721_i3 : ∀ j, childrenC_721_i3 j ⊆ insert (4, 6) required_721_i3 := by decide +kernel
theorem child_envelope_sub_721_i3 : ∀ j, childrenD_721_i3 j ⊆ envelope_721_i3 := by decide +kernel
theorem pivot_mem_721_i3 : (4, 6) ∈ envelope_721_i3 := by decide +kernel
theorem children_work_721_i3 : ∀ j, Template HasSnaky 5 (childrenC_721_i3 j) (childrenD_721_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact row_works_721_i4.mono (by decide +kernel)
theorem row_works_721_i3 : Template HasSnaky 6 required_721_i3 envelope_721_i3 := by
  refine compose HasSnaky 5 childrenC_721_i3 childrenD_721_i3 children_work_721_i3 (4, 6)
    required_721_i3 envelope_721_i3 pivot_mem_721_i3 child_required_sub_721_i3 child_envelope_sub_721_i3 ?_
  intro b hb
  exact common_sub_721_i3 (mem_commonEnvelope childrenD_721_i3 b hb)
def required_721_i2 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3), (3, 4), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_721_i2 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_721_i2 : Fin 2 → Finset Cell := ![(placed21 2 (3, 2) required_22), required_721_i3]
def childrenD_721_i2 : Fin 2 → Finset Cell := ![(placed21 2 (3, 2) envelope_22), envelope_721_i3]
theorem common_sub_721_i2 : commonEnvelope childrenD_721_i2 ⊆ insert (3, 6) required_721_i2 := by decide +kernel
theorem child_required_sub_721_i2 : ∀ j, childrenC_721_i2 j ⊆ insert (3, 6) required_721_i2 := by decide +kernel
theorem child_envelope_sub_721_i2 : ∀ j, childrenD_721_i2 j ⊆ envelope_721_i2 := by decide +kernel
theorem pivot_mem_721_i2 : (3, 6) ∈ envelope_721_i2 := by decide +kernel
theorem children_work_721_i2 : ∀ j, Template HasSnaky 6 (childrenC_721_i2 j) (childrenD_721_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 2 (3, 2)).mono (by decide +kernel)
  · exact row_works_721_i3.mono (by decide +kernel)
theorem row_works_721_i2 : Template HasSnaky 7 required_721_i2 envelope_721_i2 := by
  refine compose HasSnaky 6 childrenC_721_i2 childrenD_721_i2 children_work_721_i2 (3, 6)
    required_721_i2 envelope_721_i2 pivot_mem_721_i2 child_required_sub_721_i2 child_envelope_sub_721_i2 ?_
  intro b hb
  exact common_sub_721_i2 (mem_commonEnvelope childrenD_721_i2 b hb)
def required_721_i1 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_721_i1 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_721_i1 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) required_25), required_721_i2]
def childrenD_721_i1 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) envelope_25), envelope_721_i2]
theorem common_sub_721_i1 : commonEnvelope childrenD_721_i1 ⊆ insert (2, 4) required_721_i1 := by decide +kernel
theorem child_required_sub_721_i1 : ∀ j, childrenC_721_i1 j ⊆ insert (2, 4) required_721_i1 := by decide +kernel
theorem child_envelope_sub_721_i1 : ∀ j, childrenD_721_i1 j ⊆ envelope_721_i1 := by decide +kernel
theorem pivot_mem_721_i1 : (2, 4) ∈ envelope_721_i1 := by decide +kernel
theorem children_work_721_i1 : ∀ j, Template HasSnaky 7 (childrenC_721_i1 j) (childrenD_721_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 7 (6, 6)).mono (by decide +kernel)
  · exact row_works_721_i2.mono (by decide +kernel)
theorem row_works_721_i1 : Template HasSnaky 8 required_721_i1 envelope_721_i1 := by
  refine compose HasSnaky 7 childrenC_721_i1 childrenD_721_i1 children_work_721_i1 (2, 4)
    required_721_i1 envelope_721_i1 pivot_mem_721_i1 child_required_sub_721_i1 child_envelope_sub_721_i1 ?_
  intro b hb
  exact common_sub_721_i1 (mem_commonEnvelope childrenD_721_i1 b hb)
def required_721_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_721_i0 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_721_i0 : Fin 3 → Finset Cell := ![(placed21 4 (5, 7) required_7), (placed21 5 (6, 3) required_8), required_721_i1]
def childrenD_721_i0 : Fin 3 → Finset Cell := ![(placed21 4 (5, 7) envelope_7), (placed21 5 (6, 3) envelope_8), envelope_721_i1]
theorem common_sub_721_i0 : commonEnvelope childrenD_721_i0 ⊆ insert (5, 6) required_721_i0 := by decide +kernel
theorem child_required_sub_721_i0 : ∀ j, childrenC_721_i0 j ⊆ insert (5, 6) required_721_i0 := by decide +kernel
theorem child_envelope_sub_721_i0 : ∀ j, childrenD_721_i0 j ⊆ envelope_721_i0 := by decide +kernel
theorem pivot_mem_721_i0 : (5, 6) ∈ envelope_721_i0 := by decide +kernel
theorem children_work_721_i0 : ∀ j, Template HasSnaky 8 (childrenC_721_i0 j) (childrenD_721_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 5 (6, 3)).mono (by decide +kernel)
  · exact row_works_721_i1.mono (by decide +kernel)
theorem row_works_721_i0 : Template HasSnaky 9 required_721_i0 envelope_721_i0 := by
  refine compose HasSnaky 8 childrenC_721_i0 childrenD_721_i0 children_work_721_i0 (5, 6)
    required_721_i0 envelope_721_i0 pivot_mem_721_i0 child_required_sub_721_i0 child_envelope_sub_721_i0 ?_
  intro b hb
  exact common_sub_721_i0 (mem_commonEnvelope childrenD_721_i0 b hb)
def required_721 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_721 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 5), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_721 : Fin 5 → Finset Cell := ![(placed21 2 (6, 1) required_14), (placed21 4 (2, 6) required_176), (placed21 0 (2, 2) required_216), (placed21 1 (2, 3) required_218), required_721_i0]
def childrenD_721 : Fin 5 → Finset Cell := ![(placed21 2 (6, 1) envelope_14), (placed21 4 (2, 6) envelope_176), (placed21 0 (2, 2) envelope_216), (placed21 1 (2, 3) envelope_218), envelope_721_i0]
theorem common_sub_721 : commonEnvelope childrenD_721 ⊆ insert (5, 4) required_721 := by decide +kernel
theorem child_required_sub_721 : ∀ j, childrenC_721 j ⊆ insert (5, 4) required_721 := by decide +kernel
theorem child_envelope_sub_721 : ∀ j, childrenD_721 j ⊆ envelope_721 := by decide +kernel
theorem pivot_mem_721 : (5, 4) ∈ envelope_721 := by decide +kernel
theorem children_work_721 : ∀ j, Template HasSnaky 9 (childrenC_721 j) (childrenD_721 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 2 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_176 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_216 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_218 1 (2, 3)).mono (by decide +kernel)
  · exact row_works_721_i0.mono (by decide +kernel)
theorem row_works_721 : Template HasSnaky 10 required_721 envelope_721 := by
  refine compose HasSnaky 9 childrenC_721 childrenD_721 children_work_721 (5, 4)
    required_721 envelope_721 pivot_mem_721 child_required_sub_721 child_envelope_sub_721 ?_
  intro b hb
  exact common_sub_721 (mem_commonEnvelope childrenD_721 b hb)
def height_652_i3 : ℕ := 4
def childrenH_652_i3 : Fin 2 → ℕ := ![height_0, height_245]
theorem height_exact_652_i3 : height_652_i3 = 1 + Finset.univ.sup childrenH_652_i3 := by decide +kernel
theorem required_origin_652_i3 : ∀ x ∈ required_652_i3,
    (∃ j, x ∈ childrenC_652_i3 j) ∨ ∀ j, x ∈ childrenD_652_i3 j := by decide +kernel
theorem required_exact_652_i3 : required_652_i3 =
    ((Finset.univ.biUnion childrenC_652_i3) ∪ commonEnvelope childrenD_652_i3).erase (3, 5) := by
  exact required_eq_combination childrenC_652_i3 childrenD_652_i3 (3, 5) required_652_i3
    (by decide +kernel) child_required_sub_652_i3 common_sub_652_i3 required_origin_652_i3
theorem envelope_origin_652_i3 : ∀ x ∈ envelope_652_i3,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_652_i3 j := by decide +kernel
theorem envelope_exact_652_i3 : envelope_652_i3 =
    insert (3, 5) (Finset.univ.biUnion childrenD_652_i3) := by
  exact envelope_eq_combination childrenD_652_i3 (3, 5) envelope_652_i3
    pivot_mem_652_i3 child_envelope_sub_652_i3 envelope_origin_652_i3
def checked_652_i3 : CheckedCard where
  required := required_652_i3
  envelope := envelope_652_i3
  height := height_652_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_652_i3
def height_652_i2 : ℕ := 5
def childrenH_652_i2 : Fin 3 → ℕ := ![height_36, height_44, height_652_i3]
theorem height_exact_652_i2 : height_652_i2 = 1 + Finset.univ.sup childrenH_652_i2 := by decide +kernel
theorem required_origin_652_i2 : ∀ x ∈ required_652_i2,
    (∃ j, x ∈ childrenC_652_i2 j) ∨ ∀ j, x ∈ childrenD_652_i2 j := by decide +kernel
theorem required_exact_652_i2 : required_652_i2 =
    ((Finset.univ.biUnion childrenC_652_i2) ∪ commonEnvelope childrenD_652_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_652_i2 childrenD_652_i2 (4, 5) required_652_i2
    (by decide +kernel) child_required_sub_652_i2 common_sub_652_i2 required_origin_652_i2
theorem envelope_origin_652_i2 : ∀ x ∈ envelope_652_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_652_i2 j := by decide +kernel
theorem envelope_exact_652_i2 : envelope_652_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_652_i2) := by
  exact envelope_eq_combination childrenD_652_i2 (4, 5) envelope_652_i2
    pivot_mem_652_i2 child_envelope_sub_652_i2 envelope_origin_652_i2
def checked_652_i2 : CheckedCard where
  required := required_652_i2
  envelope := envelope_652_i2
  height := height_652_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_652_i2
def height_652_i1 : ℕ := 6
def childrenH_652_i1 : Fin 2 → ℕ := ![height_222, height_652_i2]
theorem height_exact_652_i1 : height_652_i1 = 1 + Finset.univ.sup childrenH_652_i1 := by decide +kernel
theorem required_origin_652_i1 : ∀ x ∈ required_652_i1,
    (∃ j, x ∈ childrenC_652_i1 j) ∨ ∀ j, x ∈ childrenD_652_i1 j := by decide +kernel
theorem required_exact_652_i1 : required_652_i1 =
    ((Finset.univ.biUnion childrenC_652_i1) ∪ commonEnvelope childrenD_652_i1).erase (4, 4) := by
  exact required_eq_combination childrenC_652_i1 childrenD_652_i1 (4, 4) required_652_i1
    (by decide +kernel) child_required_sub_652_i1 common_sub_652_i1 required_origin_652_i1
theorem envelope_origin_652_i1 : ∀ x ∈ envelope_652_i1,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_652_i1 j := by decide +kernel
theorem envelope_exact_652_i1 : envelope_652_i1 =
    insert (4, 4) (Finset.univ.biUnion childrenD_652_i1) := by
  exact envelope_eq_combination childrenD_652_i1 (4, 4) envelope_652_i1
    pivot_mem_652_i1 child_envelope_sub_652_i1 envelope_origin_652_i1
def checked_652_i1 : CheckedCard where
  required := required_652_i1
  envelope := envelope_652_i1
  height := height_652_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_652_i1
def height_652_i0 : ℕ := 9
def childrenH_652_i0 : Fin 3 → ℕ := ![height_10, height_558, height_652_i1]
theorem height_exact_652_i0 : height_652_i0 = 1 + Finset.univ.sup childrenH_652_i0 := by decide +kernel
theorem required_origin_652_i0 : ∀ x ∈ required_652_i0,
    (∃ j, x ∈ childrenC_652_i0 j) ∨ ∀ j, x ∈ childrenD_652_i0 j := by decide +kernel
theorem required_exact_652_i0 : required_652_i0 =
    ((Finset.univ.biUnion childrenC_652_i0) ∪ commonEnvelope childrenD_652_i0).erase (2, 5) := by
  exact required_eq_combination childrenC_652_i0 childrenD_652_i0 (2, 5) required_652_i0
    (by decide +kernel) child_required_sub_652_i0 common_sub_652_i0 required_origin_652_i0
theorem envelope_origin_652_i0 : ∀ x ∈ envelope_652_i0,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_652_i0 j := by decide +kernel
theorem envelope_exact_652_i0 : envelope_652_i0 =
    insert (2, 5) (Finset.univ.biUnion childrenD_652_i0) := by
  exact envelope_eq_combination childrenD_652_i0 (2, 5) envelope_652_i0
    pivot_mem_652_i0 child_envelope_sub_652_i0 envelope_origin_652_i0
def checked_652_i0 : CheckedCard where
  required := required_652_i0
  envelope := envelope_652_i0
  height := height_652_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_652_i0
def height_652 : ℕ := 10
def childrenH_652 : Fin 2 → ℕ := ![height_0, height_652_i0]
theorem height_exact_652 : height_652 = 1 + Finset.univ.sup childrenH_652 := by decide +kernel
theorem required_origin_652 : ∀ x ∈ required_652,
    (∃ j, x ∈ childrenC_652 j) ∨ ∀ j, x ∈ childrenD_652 j := by decide +kernel
theorem required_exact_652 : required_652 =
    ((Finset.univ.biUnion childrenC_652) ∪ commonEnvelope childrenD_652).erase (4, 3) := by
  exact required_eq_combination childrenC_652 childrenD_652 (4, 3) required_652
    (by decide +kernel) child_required_sub_652 common_sub_652 required_origin_652
theorem envelope_origin_652 : ∀ x ∈ envelope_652,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_652 j := by decide +kernel
theorem envelope_exact_652 : envelope_652 =
    insert (4, 3) (Finset.univ.biUnion childrenD_652) := by
  exact envelope_eq_combination childrenD_652 (4, 3) envelope_652
    pivot_mem_652 child_envelope_sub_652 envelope_origin_652
def checked_652 : CheckedCard where
  required := required_652
  envelope := envelope_652
  height := height_652
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_652
def height_674 : ℕ := 10
def childrenH_674 : Fin 3 → ℕ := ![height_34, height_149, height_673]
theorem height_exact_674 : height_674 = 1 + Finset.univ.sup childrenH_674 := by decide +kernel
theorem required_origin_674 : ∀ x ∈ required_674,
    (∃ j, x ∈ childrenC_674 j) ∨ ∀ j, x ∈ childrenD_674 j := by decide +kernel
theorem required_exact_674 : required_674 =
    ((Finset.univ.biUnion childrenC_674) ∪ commonEnvelope childrenD_674).erase (2, 4) := by
  exact required_eq_combination childrenC_674 childrenD_674 (2, 4) required_674
    (by decide +kernel) child_required_sub_674 common_sub_674 required_origin_674
theorem envelope_origin_674 : ∀ x ∈ envelope_674,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_674 j := by decide +kernel
theorem envelope_exact_674 : envelope_674 =
    insert (2, 4) (Finset.univ.biUnion childrenD_674) := by
  exact envelope_eq_combination childrenD_674 (2, 4) envelope_674
    pivot_mem_674 child_envelope_sub_674 envelope_origin_674
def checked_674 : CheckedCard where
  required := required_674
  envelope := envelope_674
  height := height_674
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_674
def height_702_i1 : ℕ := 3
def childrenH_702_i1 : Fin 2 → ℕ := ![height_15, height_40]
theorem height_exact_702_i1 : height_702_i1 = 1 + Finset.univ.sup childrenH_702_i1 := by decide +kernel
theorem required_origin_702_i1 : ∀ x ∈ required_702_i1,
    (∃ j, x ∈ childrenC_702_i1 j) ∨ ∀ j, x ∈ childrenD_702_i1 j := by decide +kernel
theorem required_exact_702_i1 : required_702_i1 =
    ((Finset.univ.biUnion childrenC_702_i1) ∪ commonEnvelope childrenD_702_i1).erase (1, 1) := by
  exact required_eq_combination childrenC_702_i1 childrenD_702_i1 (1, 1) required_702_i1
    (by decide +kernel) child_required_sub_702_i1 common_sub_702_i1 required_origin_702_i1
theorem envelope_origin_702_i1 : ∀ x ∈ envelope_702_i1,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_702_i1 j := by decide +kernel
theorem envelope_exact_702_i1 : envelope_702_i1 =
    insert (1, 1) (Finset.univ.biUnion childrenD_702_i1) := by
  exact envelope_eq_combination childrenD_702_i1 (1, 1) envelope_702_i1
    pivot_mem_702_i1 child_envelope_sub_702_i1 envelope_origin_702_i1
def checked_702_i1 : CheckedCard where
  required := required_702_i1
  envelope := envelope_702_i1
  height := height_702_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_702_i1
def height_702_i0 : ℕ := 8
def childrenH_702_i0 : Fin 4 → ℕ := ![height_30, height_108, height_702_i1, height_511]
theorem height_exact_702_i0 : height_702_i0 = 1 + Finset.univ.sup childrenH_702_i0 := by decide +kernel
theorem required_origin_702_i0 : ∀ x ∈ required_702_i0,
    (∃ j, x ∈ childrenC_702_i0 j) ∨ ∀ j, x ∈ childrenD_702_i0 j := by decide +kernel
theorem required_exact_702_i0 : required_702_i0 =
    ((Finset.univ.biUnion childrenC_702_i0) ∪ commonEnvelope childrenD_702_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_702_i0 childrenD_702_i0 (4, 2) required_702_i0
    (by decide +kernel) child_required_sub_702_i0 common_sub_702_i0 required_origin_702_i0
theorem envelope_origin_702_i0 : ∀ x ∈ envelope_702_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_702_i0 j := by decide +kernel
theorem envelope_exact_702_i0 : envelope_702_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_702_i0) := by
  exact envelope_eq_combination childrenD_702_i0 (4, 2) envelope_702_i0
    pivot_mem_702_i0 child_envelope_sub_702_i0 envelope_origin_702_i0
def checked_702_i0 : CheckedCard where
  required := required_702_i0
  envelope := envelope_702_i0
  height := height_702_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_702_i0
def height_702 : ℕ := 10
def childrenH_702 : Fin 3 → ℕ := ![height_22, height_400, height_702_i0]
theorem height_exact_702 : height_702 = 1 + Finset.univ.sup childrenH_702 := by decide +kernel
theorem required_origin_702 : ∀ x ∈ required_702,
    (∃ j, x ∈ childrenC_702 j) ∨ ∀ j, x ∈ childrenD_702 j := by decide +kernel
theorem required_exact_702 : required_702 =
    ((Finset.univ.biUnion childrenC_702) ∪ commonEnvelope childrenD_702).erase (4, 3) := by
  exact required_eq_combination childrenC_702 childrenD_702 (4, 3) required_702
    (by decide +kernel) child_required_sub_702 common_sub_702 required_origin_702
theorem envelope_origin_702 : ∀ x ∈ envelope_702,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_702 j := by decide +kernel
theorem envelope_exact_702 : envelope_702 =
    insert (4, 3) (Finset.univ.biUnion childrenD_702) := by
  exact envelope_eq_combination childrenD_702 (4, 3) envelope_702
    pivot_mem_702 child_envelope_sub_702 envelope_origin_702
def checked_702 : CheckedCard where
  required := required_702
  envelope := envelope_702
  height := height_702
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_702
def height_704_i1 : ℕ := 6
def childrenH_704_i1 : Fin 3 → ℕ := ![height_28, height_58, height_306]
theorem height_exact_704_i1 : height_704_i1 = 1 + Finset.univ.sup childrenH_704_i1 := by decide +kernel
theorem required_origin_704_i1 : ∀ x ∈ required_704_i1,
    (∃ j, x ∈ childrenC_704_i1 j) ∨ ∀ j, x ∈ childrenD_704_i1 j := by decide +kernel
theorem required_exact_704_i1 : required_704_i1 =
    ((Finset.univ.biUnion childrenC_704_i1) ∪ commonEnvelope childrenD_704_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_704_i1 childrenD_704_i1 (4, 6) required_704_i1
    (by decide +kernel) child_required_sub_704_i1 common_sub_704_i1 required_origin_704_i1
theorem envelope_origin_704_i1 : ∀ x ∈ envelope_704_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_704_i1 j := by decide +kernel
theorem envelope_exact_704_i1 : envelope_704_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_704_i1) := by
  exact envelope_eq_combination childrenD_704_i1 (4, 6) envelope_704_i1
    pivot_mem_704_i1 child_envelope_sub_704_i1 envelope_origin_704_i1
def checked_704_i1 : CheckedCard where
  required := required_704_i1
  envelope := envelope_704_i1
  height := height_704_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_704_i1
def height_704_i3 : ℕ := 4
def childrenH_704_i3 : Fin 2 → ℕ := ![height_2, height_52]
theorem height_exact_704_i3 : height_704_i3 = 1 + Finset.univ.sup childrenH_704_i3 := by decide +kernel
theorem required_origin_704_i3 : ∀ x ∈ required_704_i3,
    (∃ j, x ∈ childrenC_704_i3 j) ∨ ∀ j, x ∈ childrenD_704_i3 j := by decide +kernel
theorem required_exact_704_i3 : required_704_i3 =
    ((Finset.univ.biUnion childrenC_704_i3) ∪ commonEnvelope childrenD_704_i3).erase (5, 5) := by
  exact required_eq_combination childrenC_704_i3 childrenD_704_i3 (5, 5) required_704_i3
    (by decide +kernel) child_required_sub_704_i3 common_sub_704_i3 required_origin_704_i3
theorem envelope_origin_704_i3 : ∀ x ∈ envelope_704_i3,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_704_i3 j := by decide +kernel
theorem envelope_exact_704_i3 : envelope_704_i3 =
    insert (5, 5) (Finset.univ.biUnion childrenD_704_i3) := by
  exact envelope_eq_combination childrenD_704_i3 (5, 5) envelope_704_i3
    pivot_mem_704_i3 child_envelope_sub_704_i3 envelope_origin_704_i3
def checked_704_i3 : CheckedCard where
  required := required_704_i3
  envelope := envelope_704_i3
  height := height_704_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_704_i3
def height_704_i4 : ℕ := 5
def childrenH_704_i4 : Fin 2 → ℕ := ![height_2, height_10]
theorem height_exact_704_i4 : height_704_i4 = 1 + Finset.univ.sup childrenH_704_i4 := by decide +kernel
theorem required_origin_704_i4 : ∀ x ∈ required_704_i4,
    (∃ j, x ∈ childrenC_704_i4 j) ∨ ∀ j, x ∈ childrenD_704_i4 j := by decide +kernel
theorem required_exact_704_i4 : required_704_i4 =
    ((Finset.univ.biUnion childrenC_704_i4) ∪ commonEnvelope childrenD_704_i4).erase (5, 5) := by
  exact required_eq_combination childrenC_704_i4 childrenD_704_i4 (5, 5) required_704_i4
    (by decide +kernel) child_required_sub_704_i4 common_sub_704_i4 required_origin_704_i4
theorem envelope_origin_704_i4 : ∀ x ∈ envelope_704_i4,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_704_i4 j := by decide +kernel
theorem envelope_exact_704_i4 : envelope_704_i4 =
    insert (5, 5) (Finset.univ.biUnion childrenD_704_i4) := by
  exact envelope_eq_combination childrenD_704_i4 (5, 5) envelope_704_i4
    pivot_mem_704_i4 child_envelope_sub_704_i4 envelope_origin_704_i4
def checked_704_i4 : CheckedCard where
  required := required_704_i4
  envelope := envelope_704_i4
  height := height_704_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_704_i4
def height_704_i5 : ℕ := 4
def childrenH_704_i5 : Fin 2 → ℕ := ![height_25, height_78]
theorem height_exact_704_i5 : height_704_i5 = 1 + Finset.univ.sup childrenH_704_i5 := by decide +kernel
theorem required_origin_704_i5 : ∀ x ∈ required_704_i5,
    (∃ j, x ∈ childrenC_704_i5 j) ∨ ∀ j, x ∈ childrenD_704_i5 j := by decide +kernel
theorem required_exact_704_i5 : required_704_i5 =
    ((Finset.univ.biUnion childrenC_704_i5) ∪ commonEnvelope childrenD_704_i5).erase (4, 6) := by
  exact required_eq_combination childrenC_704_i5 childrenD_704_i5 (4, 6) required_704_i5
    (by decide +kernel) child_required_sub_704_i5 common_sub_704_i5 required_origin_704_i5
theorem envelope_origin_704_i5 : ∀ x ∈ envelope_704_i5,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_704_i5 j := by decide +kernel
theorem envelope_exact_704_i5 : envelope_704_i5 =
    insert (4, 6) (Finset.univ.biUnion childrenD_704_i5) := by
  exact envelope_eq_combination childrenD_704_i5 (4, 6) envelope_704_i5
    pivot_mem_704_i5 child_envelope_sub_704_i5 envelope_origin_704_i5
def checked_704_i5 : CheckedCard where
  required := required_704_i5
  envelope := envelope_704_i5
  height := height_704_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_704_i5
def height_704_i2 : ℕ := 7
def childrenH_704_i2 : Fin 4 → ℕ := ![height_516, height_704_i3, height_704_i4, height_704_i5]
theorem height_exact_704_i2 : height_704_i2 = 1 + Finset.univ.sup childrenH_704_i2 := by decide +kernel
theorem required_origin_704_i2 : ∀ x ∈ required_704_i2,
    (∃ j, x ∈ childrenC_704_i2 j) ∨ ∀ j, x ∈ childrenD_704_i2 j := by decide +kernel
theorem required_exact_704_i2 : required_704_i2 =
    ((Finset.univ.biUnion childrenC_704_i2) ∪ commonEnvelope childrenD_704_i2).erase (4, 3) := by
  exact required_eq_combination childrenC_704_i2 childrenD_704_i2 (4, 3) required_704_i2
    (by decide +kernel) child_required_sub_704_i2 common_sub_704_i2 required_origin_704_i2
theorem envelope_origin_704_i2 : ∀ x ∈ envelope_704_i2,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_704_i2 j := by decide +kernel
theorem envelope_exact_704_i2 : envelope_704_i2 =
    insert (4, 3) (Finset.univ.biUnion childrenD_704_i2) := by
  exact envelope_eq_combination childrenD_704_i2 (4, 3) envelope_704_i2
    pivot_mem_704_i2 child_envelope_sub_704_i2 envelope_origin_704_i2
def checked_704_i2 : CheckedCard where
  required := required_704_i2
  envelope := envelope_704_i2
  height := height_704_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_704_i2
def height_704_i0 : ℕ := 9
def childrenH_704_i0 : Fin 4 → ℕ := ![height_30, height_704_i1, height_703, height_704_i2]
theorem height_exact_704_i0 : height_704_i0 = 1 + Finset.univ.sup childrenH_704_i0 := by decide +kernel
theorem required_origin_704_i0 : ∀ x ∈ required_704_i0,
    (∃ j, x ∈ childrenC_704_i0 j) ∨ ∀ j, x ∈ childrenD_704_i0 j := by decide +kernel
theorem required_exact_704_i0 : required_704_i0 =
    ((Finset.univ.biUnion childrenC_704_i0) ∪ commonEnvelope childrenD_704_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_704_i0 childrenD_704_i0 (4, 5) required_704_i0
    (by decide +kernel) child_required_sub_704_i0 common_sub_704_i0 required_origin_704_i0
theorem envelope_origin_704_i0 : ∀ x ∈ envelope_704_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_704_i0 j := by decide +kernel
theorem envelope_exact_704_i0 : envelope_704_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_704_i0) := by
  exact envelope_eq_combination childrenD_704_i0 (4, 5) envelope_704_i0
    pivot_mem_704_i0 child_envelope_sub_704_i0 envelope_origin_704_i0
def checked_704_i0 : CheckedCard where
  required := required_704_i0
  envelope := envelope_704_i0
  height := height_704_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_704_i0
def height_704 : ℕ := 10
def childrenH_704 : Fin 3 → ℕ := ![height_22, height_400, height_704_i0]
theorem height_exact_704 : height_704 = 1 + Finset.univ.sup childrenH_704 := by decide +kernel
theorem required_origin_704 : ∀ x ∈ required_704,
    (∃ j, x ∈ childrenC_704 j) ∨ ∀ j, x ∈ childrenD_704 j := by decide +kernel
theorem required_exact_704 : required_704 =
    ((Finset.univ.biUnion childrenC_704) ∪ commonEnvelope childrenD_704).erase (4, 4) := by
  exact required_eq_combination childrenC_704 childrenD_704 (4, 4) required_704
    (by decide +kernel) child_required_sub_704 common_sub_704 required_origin_704
theorem envelope_origin_704 : ∀ x ∈ envelope_704,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_704 j := by decide +kernel
theorem envelope_exact_704 : envelope_704 =
    insert (4, 4) (Finset.univ.biUnion childrenD_704) := by
  exact envelope_eq_combination childrenD_704 (4, 4) envelope_704
    pivot_mem_704 child_envelope_sub_704 envelope_origin_704
def checked_704 : CheckedCard where
  required := required_704
  envelope := envelope_704
  height := height_704
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_704
def height_721_i4 : ℕ := 5
def childrenH_721_i4 : Fin 2 → ℕ := ![height_5, height_208]
theorem height_exact_721_i4 : height_721_i4 = 1 + Finset.univ.sup childrenH_721_i4 := by decide +kernel
theorem required_origin_721_i4 : ∀ x ∈ required_721_i4,
    (∃ j, x ∈ childrenC_721_i4 j) ∨ ∀ j, x ∈ childrenD_721_i4 j := by decide +kernel
theorem required_exact_721_i4 : required_721_i4 =
    ((Finset.univ.biUnion childrenC_721_i4) ∪ commonEnvelope childrenD_721_i4).erase (2, 6) := by
  exact required_eq_combination childrenC_721_i4 childrenD_721_i4 (2, 6) required_721_i4
    (by decide +kernel) child_required_sub_721_i4 common_sub_721_i4 required_origin_721_i4
theorem envelope_origin_721_i4 : ∀ x ∈ envelope_721_i4,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_721_i4 j := by decide +kernel
theorem envelope_exact_721_i4 : envelope_721_i4 =
    insert (2, 6) (Finset.univ.biUnion childrenD_721_i4) := by
  exact envelope_eq_combination childrenD_721_i4 (2, 6) envelope_721_i4
    pivot_mem_721_i4 child_envelope_sub_721_i4 envelope_origin_721_i4
def checked_721_i4 : CheckedCard where
  required := required_721_i4
  envelope := envelope_721_i4
  height := height_721_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_721_i4
def height_721_i3 : ℕ := 6
def childrenH_721_i3 : Fin 2 → ℕ := ![height_5, height_721_i4]
theorem height_exact_721_i3 : height_721_i3 = 1 + Finset.univ.sup childrenH_721_i3 := by decide +kernel
theorem required_origin_721_i3 : ∀ x ∈ required_721_i3,
    (∃ j, x ∈ childrenC_721_i3 j) ∨ ∀ j, x ∈ childrenD_721_i3 j := by decide +kernel
theorem required_exact_721_i3 : required_721_i3 =
    ((Finset.univ.biUnion childrenC_721_i3) ∪ commonEnvelope childrenD_721_i3).erase (4, 6) := by
  exact required_eq_combination childrenC_721_i3 childrenD_721_i3 (4, 6) required_721_i3
    (by decide +kernel) child_required_sub_721_i3 common_sub_721_i3 required_origin_721_i3
theorem envelope_origin_721_i3 : ∀ x ∈ envelope_721_i3,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_721_i3 j := by decide +kernel
theorem envelope_exact_721_i3 : envelope_721_i3 =
    insert (4, 6) (Finset.univ.biUnion childrenD_721_i3) := by
  exact envelope_eq_combination childrenD_721_i3 (4, 6) envelope_721_i3
    pivot_mem_721_i3 child_envelope_sub_721_i3 envelope_origin_721_i3
def checked_721_i3 : CheckedCard where
  required := required_721_i3
  envelope := envelope_721_i3
  height := height_721_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_721_i3
def height_721_i2 : ℕ := 7
def childrenH_721_i2 : Fin 2 → ℕ := ![height_22, height_721_i3]
theorem height_exact_721_i2 : height_721_i2 = 1 + Finset.univ.sup childrenH_721_i2 := by decide +kernel
theorem required_origin_721_i2 : ∀ x ∈ required_721_i2,
    (∃ j, x ∈ childrenC_721_i2 j) ∨ ∀ j, x ∈ childrenD_721_i2 j := by decide +kernel
theorem required_exact_721_i2 : required_721_i2 =
    ((Finset.univ.biUnion childrenC_721_i2) ∪ commonEnvelope childrenD_721_i2).erase (3, 6) := by
  exact required_eq_combination childrenC_721_i2 childrenD_721_i2 (3, 6) required_721_i2
    (by decide +kernel) child_required_sub_721_i2 common_sub_721_i2 required_origin_721_i2
theorem envelope_origin_721_i2 : ∀ x ∈ envelope_721_i2,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_721_i2 j := by decide +kernel
theorem envelope_exact_721_i2 : envelope_721_i2 =
    insert (3, 6) (Finset.univ.biUnion childrenD_721_i2) := by
  exact envelope_eq_combination childrenD_721_i2 (3, 6) envelope_721_i2
    pivot_mem_721_i2 child_envelope_sub_721_i2 envelope_origin_721_i2
def checked_721_i2 : CheckedCard where
  required := required_721_i2
  envelope := envelope_721_i2
  height := height_721_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_721_i2
def height_721_i1 : ℕ := 8
def childrenH_721_i1 : Fin 2 → ℕ := ![height_25, height_721_i2]
theorem height_exact_721_i1 : height_721_i1 = 1 + Finset.univ.sup childrenH_721_i1 := by decide +kernel
theorem required_origin_721_i1 : ∀ x ∈ required_721_i1,
    (∃ j, x ∈ childrenC_721_i1 j) ∨ ∀ j, x ∈ childrenD_721_i1 j := by decide +kernel
theorem required_exact_721_i1 : required_721_i1 =
    ((Finset.univ.biUnion childrenC_721_i1) ∪ commonEnvelope childrenD_721_i1).erase (2, 4) := by
  exact required_eq_combination childrenC_721_i1 childrenD_721_i1 (2, 4) required_721_i1
    (by decide +kernel) child_required_sub_721_i1 common_sub_721_i1 required_origin_721_i1
theorem envelope_origin_721_i1 : ∀ x ∈ envelope_721_i1,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_721_i1 j := by decide +kernel
theorem envelope_exact_721_i1 : envelope_721_i1 =
    insert (2, 4) (Finset.univ.biUnion childrenD_721_i1) := by
  exact envelope_eq_combination childrenD_721_i1 (2, 4) envelope_721_i1
    pivot_mem_721_i1 child_envelope_sub_721_i1 envelope_origin_721_i1
def checked_721_i1 : CheckedCard where
  required := required_721_i1
  envelope := envelope_721_i1
  height := height_721_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_721_i1
def height_721_i0 : ℕ := 9
def childrenH_721_i0 : Fin 3 → ℕ := ![height_7, height_8, height_721_i1]
theorem height_exact_721_i0 : height_721_i0 = 1 + Finset.univ.sup childrenH_721_i0 := by decide +kernel
theorem required_origin_721_i0 : ∀ x ∈ required_721_i0,
    (∃ j, x ∈ childrenC_721_i0 j) ∨ ∀ j, x ∈ childrenD_721_i0 j := by decide +kernel
theorem required_exact_721_i0 : required_721_i0 =
    ((Finset.univ.biUnion childrenC_721_i0) ∪ commonEnvelope childrenD_721_i0).erase (5, 6) := by
  exact required_eq_combination childrenC_721_i0 childrenD_721_i0 (5, 6) required_721_i0
    (by decide +kernel) child_required_sub_721_i0 common_sub_721_i0 required_origin_721_i0
theorem envelope_origin_721_i0 : ∀ x ∈ envelope_721_i0,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_721_i0 j := by decide +kernel
theorem envelope_exact_721_i0 : envelope_721_i0 =
    insert (5, 6) (Finset.univ.biUnion childrenD_721_i0) := by
  exact envelope_eq_combination childrenD_721_i0 (5, 6) envelope_721_i0
    pivot_mem_721_i0 child_envelope_sub_721_i0 envelope_origin_721_i0
def checked_721_i0 : CheckedCard where
  required := required_721_i0
  envelope := envelope_721_i0
  height := height_721_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_721_i0
def height_721 : ℕ := 10
def childrenH_721 : Fin 5 → ℕ := ![height_14, height_176, height_216, height_218, height_721_i0]
theorem height_exact_721 : height_721 = 1 + Finset.univ.sup childrenH_721 := by decide +kernel
theorem required_origin_721 : ∀ x ∈ required_721,
    (∃ j, x ∈ childrenC_721 j) ∨ ∀ j, x ∈ childrenD_721 j := by decide +kernel
theorem required_exact_721 : required_721 =
    ((Finset.univ.biUnion childrenC_721) ∪ commonEnvelope childrenD_721).erase (5, 4) := by
  exact required_eq_combination childrenC_721 childrenD_721 (5, 4) required_721
    (by decide +kernel) child_required_sub_721 common_sub_721 required_origin_721
theorem envelope_origin_721 : ∀ x ∈ envelope_721,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_721 j := by decide +kernel
theorem envelope_exact_721 : envelope_721 =
    insert (5, 4) (Finset.univ.biUnion childrenD_721) := by
  exact envelope_eq_combination childrenD_721 (5, 4) envelope_721
    pivot_mem_721 child_envelope_sub_721 envelope_origin_721
def checked_721 : CheckedCard where
  required := required_721
  envelope := envelope_721
  height := height_721
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_721
end SnakyPrototype.Certificate21

end OAI
