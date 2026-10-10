import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_593_i0 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_593_i0 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_593_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) required_36), (placed21 0 (3, 1) required_105), (placed21 4 (3, 6) required_250), (placed21 4 (3, 6) required_592)]
def childrenD_593_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) envelope_36), (placed21 0 (3, 1) envelope_105), (placed21 4 (3, 6) envelope_250), (placed21 4 (3, 6) envelope_592)]
theorem common_sub_593_i0 : commonEnvelope childrenD_593_i0 ⊆ insert (4, 5) required_593_i0 := by decide +kernel
theorem child_required_sub_593_i0 : ∀ j, childrenC_593_i0 j ⊆ insert (4, 5) required_593_i0 := by decide +kernel
theorem child_envelope_sub_593_i0 : ∀ j, childrenD_593_i0 j ⊆ envelope_593_i0 := by decide +kernel
theorem pivot_mem_593_i0 : (4, 5) ∈ envelope_593_i0 := by decide +kernel
theorem children_work_593_i0 : ∀ j, Template HasSnaky 5 (childrenC_593_i0 j) (childrenD_593_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_36 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_105 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_250 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_592 4 (3, 6)).mono (by decide +kernel)
theorem row_works_593_i0 : Template HasSnaky 6 required_593_i0 envelope_593_i0 := by
  refine compose HasSnaky 5 childrenC_593_i0 childrenD_593_i0 children_work_593_i0 (4, 5)
    required_593_i0 envelope_593_i0 pivot_mem_593_i0 child_required_sub_593_i0 child_envelope_sub_593_i0 ?_
  intro b hb
  exact common_sub_593_i0 (mem_commonEnvelope childrenD_593_i0 b hb)
def required_593 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 2), (3, 3), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_593 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_593 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_2), required_593_i0]
def childrenD_593 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_2), envelope_593_i0]
theorem common_sub_593 : commonEnvelope childrenD_593 ⊆ insert (4, 3) required_593 := by decide +kernel
theorem child_required_sub_593 : ∀ j, childrenC_593 j ⊆ insert (4, 3) required_593 := by decide +kernel
theorem child_envelope_sub_593 : ∀ j, childrenD_593 j ⊆ envelope_593 := by decide +kernel
theorem pivot_mem_593 : (4, 3) ∈ envelope_593 := by decide +kernel
theorem children_work_593 : ∀ j, Template HasSnaky 6 (childrenC_593 j) (childrenD_593 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_593_i0.mono (by decide +kernel)
theorem row_works_593 : Template HasSnaky 7 required_593 envelope_593 := by
  refine compose HasSnaky 6 childrenC_593 childrenD_593 children_work_593 (4, 3)
    required_593 envelope_593 pivot_mem_593 child_required_sub_593 child_envelope_sub_593 ?_
  intro b hb
  exact common_sub_593 (mem_commonEnvelope childrenD_593 b hb)
def required_610 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_610 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_610 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) required_19), (placed21 5 (2, 2) required_197), (placed21 0 (0, 1) required_225), (placed21 4 (0, 6) required_609)]
def childrenD_610 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) envelope_19), (placed21 5 (2, 2) envelope_197), (placed21 0 (0, 1) envelope_225), (placed21 4 (0, 6) envelope_609)]
theorem common_sub_610 : commonEnvelope childrenD_610 ⊆ insert (1, 5) required_610 := by decide +kernel
theorem child_required_sub_610 : ∀ j, childrenC_610 j ⊆ insert (1, 5) required_610 := by decide +kernel
theorem child_envelope_sub_610 : ∀ j, childrenD_610 j ⊆ envelope_610 := by decide +kernel
theorem pivot_mem_610 : (1, 5) ∈ envelope_610 := by decide +kernel
theorem children_work_610 : ∀ j, Template HasSnaky 6 (childrenC_610 j) (childrenD_610 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 5 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_225 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_609 4 (0, 6)).mono (by decide +kernel)
theorem row_works_610 : Template HasSnaky 7 required_610 envelope_610 := by
  refine compose HasSnaky 6 childrenC_610 childrenD_610 children_work_610 (1, 5)
    required_610 envelope_610 pivot_mem_610 child_required_sub_610 child_envelope_sub_610 ?_
  intro b hb
  exact common_sub_610 (mem_commonEnvelope childrenD_610 b hb)
def required_620_i0 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 6), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_620_i0 : Finset Cell := ⟨(([(2, 1), (2, 2), (2, 3), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_620_i0 : Fin 3 → Finset Cell := ![(placed21 6 (4, 6) required_17), (placed21 6 (4, 6) required_37), (placed21 5 (4, 3) required_233)]
def childrenD_620_i0 : Fin 3 → Finset Cell := ![(placed21 6 (4, 6) envelope_17), (placed21 6 (4, 6) envelope_37), (placed21 5 (4, 3) envelope_233)]
theorem common_sub_620_i0 : commonEnvelope childrenD_620_i0 ⊆ insert (3, 3) required_620_i0 := by decide +kernel
theorem child_required_sub_620_i0 : ∀ j, childrenC_620_i0 j ⊆ insert (3, 3) required_620_i0 := by decide +kernel
theorem child_envelope_sub_620_i0 : ∀ j, childrenD_620_i0 j ⊆ envelope_620_i0 := by decide +kernel
theorem pivot_mem_620_i0 : (3, 3) ∈ envelope_620_i0 := by decide +kernel
theorem children_work_620_i0 : ∀ j, Template HasSnaky 5 (childrenC_620_i0 j) (childrenD_620_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_233 5 (4, 3)).mono (by decide +kernel)
theorem row_works_620_i0 : Template HasSnaky 6 required_620_i0 envelope_620_i0 := by
  refine compose HasSnaky 5 childrenC_620_i0 childrenD_620_i0 children_work_620_i0 (3, 3)
    required_620_i0 envelope_620_i0 pivot_mem_620_i0 child_required_sub_620_i0 child_envelope_sub_620_i0 ?_
  intro b hb
  exact common_sub_620_i0 (mem_commonEnvelope childrenD_620_i0 b hb)
def required_620 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_620 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_620 : Fin 5 → Finset Cell := ![(placed21 5 (6, 3) required_57), (placed21 7 (6, 7) required_57), (placed21 5 (6, 3) required_293), (placed21 7 (6, 7) required_293), required_620_i0]
def childrenD_620 : Fin 5 → Finset Cell := ![(placed21 5 (6, 3) envelope_57), (placed21 7 (6, 7) envelope_57), (placed21 5 (6, 3) envelope_293), (placed21 7 (6, 7) envelope_293), envelope_620_i0]
theorem common_sub_620 : commonEnvelope childrenD_620 ⊆ insert (4, 5) required_620 := by decide +kernel
theorem child_required_sub_620 : ∀ j, childrenC_620 j ⊆ insert (4, 5) required_620 := by decide +kernel
theorem child_envelope_sub_620 : ∀ j, childrenD_620 j ⊆ envelope_620 := by decide +kernel
theorem pivot_mem_620 : (4, 5) ∈ envelope_620 := by decide +kernel
theorem children_work_620 : ∀ j, Template HasSnaky 6 (childrenC_620 j) (childrenD_620 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_57 5 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_57 7 (6, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_293 5 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_293 7 (6, 7)).mono (by decide +kernel)
  · exact row_works_620_i0.mono (by decide +kernel)
theorem row_works_620 : Template HasSnaky 7 required_620 envelope_620 := by
  refine compose HasSnaky 6 childrenC_620 childrenD_620 children_work_620 (4, 5)
    required_620 envelope_620 pivot_mem_620 child_required_sub_620 child_envelope_sub_620 ?_
  intro b hb
  exact common_sub_620 (mem_commonEnvelope childrenD_620 b hb)
def required_621_i0 : Finset Cell := ⟨(([(2, 4), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_621_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_621_i0 : Fin 3 → Finset Cell := ![(placed21 7 (5, 4) required_15), (placed21 1 (1, 2) required_159), (placed21 6 (4, 6) required_164)]
def childrenD_621_i0 : Fin 3 → Finset Cell := ![(placed21 7 (5, 4) envelope_15), (placed21 1 (1, 2) envelope_159), (placed21 6 (4, 6) envelope_164)]
theorem common_sub_621_i0 : commonEnvelope childrenD_621_i0 ⊆ insert (2, 3) required_621_i0 := by decide +kernel
theorem child_required_sub_621_i0 : ∀ j, childrenC_621_i0 j ⊆ insert (2, 3) required_621_i0 := by decide +kernel
theorem child_envelope_sub_621_i0 : ∀ j, childrenD_621_i0 j ⊆ envelope_621_i0 := by decide +kernel
theorem pivot_mem_621_i0 : (2, 3) ∈ envelope_621_i0 := by decide +kernel
theorem children_work_621_i0 : ∀ j, Template HasSnaky 5 (childrenC_621_i0 j) (childrenD_621_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 7 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_159 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_164 6 (4, 6)).mono (by decide +kernel)
theorem row_works_621_i0 : Template HasSnaky 6 required_621_i0 envelope_621_i0 := by
  refine compose HasSnaky 5 childrenC_621_i0 childrenD_621_i0 children_work_621_i0 (2, 3)
    required_621_i0 envelope_621_i0 pivot_mem_621_i0 child_required_sub_621_i0 child_envelope_sub_621_i0 ?_
  intro b hb
  exact common_sub_621_i0 (mem_commonEnvelope childrenD_621_i0 b hb)
def required_621_i1 : Finset Cell := ⟨(([(2, 4), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_621_i1 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 3), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_621_i1 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) required_0), (placed21 4 (0, 6) required_133)]
def childrenD_621_i1 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) envelope_0), (placed21 4 (0, 6) envelope_133)]
theorem common_sub_621_i1 : commonEnvelope childrenD_621_i1 ⊆ insert (1, 4) required_621_i1 := by decide +kernel
theorem child_required_sub_621_i1 : ∀ j, childrenC_621_i1 j ⊆ insert (1, 4) required_621_i1 := by decide +kernel
theorem child_envelope_sub_621_i1 : ∀ j, childrenD_621_i1 j ⊆ envelope_621_i1 := by decide +kernel
theorem pivot_mem_621_i1 : (1, 4) ∈ envelope_621_i1 := by decide +kernel
theorem children_work_621_i1 : ∀ j, Template HasSnaky 5 (childrenC_621_i1 j) (childrenD_621_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 4 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 4 (0, 6)).mono (by decide +kernel)
theorem row_works_621_i1 : Template HasSnaky 6 required_621_i1 envelope_621_i1 := by
  refine compose HasSnaky 5 childrenC_621_i1 childrenD_621_i1 children_work_621_i1 (1, 4)
    required_621_i1 envelope_621_i1 pivot_mem_621_i1 child_required_sub_621_i1 child_envelope_sub_621_i1 ?_
  intro b hb
  exact common_sub_621_i1 (mem_commonEnvelope childrenD_621_i1 b hb)
def required_621 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_621 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_621 : Fin 6 → Finset Cell := ![(placed21 1 (0, 3) required_206), (placed21 5 (5, 2) required_238), (placed21 7 (5, 5) required_414), (placed21 6 (4, 6) required_417), required_621_i0, required_621_i1]
def childrenD_621 : Fin 6 → Finset Cell := ![(placed21 1 (0, 3) envelope_206), (placed21 5 (5, 2) envelope_238), (placed21 7 (5, 5) envelope_414), (placed21 6 (4, 6) envelope_417), envelope_621_i0, envelope_621_i1]
theorem common_sub_621 : commonEnvelope childrenD_621 ⊆ insert (2, 4) required_621 := by decide +kernel
theorem child_required_sub_621 : ∀ j, childrenC_621 j ⊆ insert (2, 4) required_621 := by decide +kernel
theorem child_envelope_sub_621 : ∀ j, childrenD_621 j ⊆ envelope_621 := by decide +kernel
theorem pivot_mem_621 : (2, 4) ∈ envelope_621 := by decide +kernel
theorem children_work_621 : ∀ j, Template HasSnaky 6 (childrenC_621 j) (childrenD_621 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_206 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_238 5 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_414 7 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_417 6 (4, 6)).mono (by decide +kernel)
  · exact row_works_621_i0.mono (by decide +kernel)
  · exact row_works_621_i1.mono (by decide +kernel)
theorem row_works_621 : Template HasSnaky 7 required_621 envelope_621 := by
  refine compose HasSnaky 6 childrenC_621 childrenD_621 children_work_621 (2, 4)
    required_621 envelope_621 pivot_mem_621 child_required_sub_621 child_envelope_sub_621 ?_
  intro b hb
  exact common_sub_621 (mem_commonEnvelope childrenD_621 b hb)
def required_628_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_628_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_628_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 3) required_36), (placed21 0 (3, 0) required_53)]
def childrenD_628_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 3) envelope_36), (placed21 0 (3, 0) envelope_53)]
theorem common_sub_628_i0 : commonEnvelope childrenD_628_i0 ⊆ insert (3, 2) required_628_i0 := by decide +kernel
theorem child_required_sub_628_i0 : ∀ j, childrenC_628_i0 j ⊆ insert (3, 2) required_628_i0 := by decide +kernel
theorem child_envelope_sub_628_i0 : ∀ j, childrenD_628_i0 j ⊆ envelope_628_i0 := by decide +kernel
theorem pivot_mem_628_i0 : (3, 2) ∈ envelope_628_i0 := by decide +kernel
theorem children_work_628_i0 : ∀ j, Template HasSnaky 3 (childrenC_628_i0 j) (childrenD_628_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_36 7 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 0 (3, 0)).mono (by decide +kernel)
theorem row_works_628_i0 : Template HasSnaky 4 required_628_i0 envelope_628_i0 := by
  refine compose HasSnaky 3 childrenC_628_i0 childrenD_628_i0 children_work_628_i0 (3, 2)
    required_628_i0 envelope_628_i0 pivot_mem_628_i0 child_required_sub_628_i0 child_envelope_sub_628_i0 ?_
  intro b hb
  exact common_sub_628_i0 (mem_commonEnvelope childrenD_628_i0 b hb)
def required_628_i1 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_628_i1 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_628_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) required_34), (placed21 2 (4, 0) required_464)]
def childrenD_628_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) envelope_34), (placed21 2 (4, 0) envelope_464)]
theorem common_sub_628_i1 : commonEnvelope childrenD_628_i1 ⊆ insert (3, 4) required_628_i1 := by decide +kernel
theorem child_required_sub_628_i1 : ∀ j, childrenC_628_i1 j ⊆ insert (3, 4) required_628_i1 := by decide +kernel
theorem child_envelope_sub_628_i1 : ∀ j, childrenD_628_i1 j ⊆ envelope_628_i1 := by decide +kernel
theorem pivot_mem_628_i1 : (3, 4) ∈ envelope_628_i1 := by decide +kernel
theorem children_work_628_i1 : ∀ j, Template HasSnaky 5 (childrenC_628_i1 j) (childrenD_628_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 7 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_464 2 (4, 0)).mono (by decide +kernel)
theorem row_works_628_i1 : Template HasSnaky 6 required_628_i1 envelope_628_i1 := by
  refine compose HasSnaky 5 childrenC_628_i1 childrenD_628_i1 children_work_628_i1 (3, 4)
    required_628_i1 envelope_628_i1 pivot_mem_628_i1 child_required_sub_628_i1 child_envelope_sub_628_i1 ?_
  intro b hb
  exact common_sub_628_i1 (mem_commonEnvelope childrenD_628_i1 b hb)
def required_628_i2 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_628_i2 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 3), (4, 4), (5, 2), (5, 3), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_628_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_5), (placed21 3 (1, 4) required_265)]
def childrenD_628_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_5), (placed21 3 (1, 4) envelope_265)]
theorem common_sub_628_i2 : commonEnvelope childrenD_628_i2 ⊆ insert (2, 3) required_628_i2 := by decide +kernel
theorem child_required_sub_628_i2 : ∀ j, childrenC_628_i2 j ⊆ insert (2, 3) required_628_i2 := by decide +kernel
theorem child_envelope_sub_628_i2 : ∀ j, childrenD_628_i2 j ⊆ envelope_628_i2 := by decide +kernel
theorem pivot_mem_628_i2 : (2, 3) ∈ envelope_628_i2 := by decide +kernel
theorem children_work_628_i2 : ∀ j, Template HasSnaky 5 (childrenC_628_i2 j) (childrenD_628_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_265 3 (1, 4)).mono (by decide +kernel)
theorem row_works_628_i2 : Template HasSnaky 6 required_628_i2 envelope_628_i2 := by
  refine compose HasSnaky 5 childrenC_628_i2 childrenD_628_i2 children_work_628_i2 (2, 3)
    required_628_i2 envelope_628_i2 pivot_mem_628_i2 child_required_sub_628_i2 child_envelope_sub_628_i2 ?_
  intro b hb
  exact common_sub_628_i2 (mem_commonEnvelope childrenD_628_i2 b hb)
def required_628 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_628 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_628 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) required_126), (placed21 4 (1, 5) required_270), required_628_i0, required_628_i1, required_628_i2]
def childrenD_628 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) envelope_126), (placed21 4 (1, 5) envelope_270), envelope_628_i0, envelope_628_i1, envelope_628_i2]
theorem common_sub_628 : commonEnvelope childrenD_628 ⊆ insert (3, 3) required_628 := by decide +kernel
theorem child_required_sub_628 : ∀ j, childrenC_628 j ⊆ insert (3, 3) required_628 := by decide +kernel
theorem child_envelope_sub_628 : ∀ j, childrenD_628 j ⊆ envelope_628 := by decide +kernel
theorem pivot_mem_628 : (3, 3) ∈ envelope_628 := by decide +kernel
theorem children_work_628 : ∀ j, Template HasSnaky 6 (childrenC_628 j) (childrenD_628 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_126 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_270 4 (1, 5)).mono (by decide +kernel)
  · exact row_works_628_i0.mono (by decide +kernel)
  · exact row_works_628_i1.mono (by decide +kernel)
  · exact row_works_628_i2.mono (by decide +kernel)
theorem row_works_628 : Template HasSnaky 7 required_628 envelope_628 := by
  refine compose HasSnaky 6 childrenC_628 childrenD_628 children_work_628 (3, 3)
    required_628 envelope_628 pivot_mem_628 child_required_sub_628 child_envelope_sub_628 ?_
  intro b hb
  exact common_sub_628 (mem_commonEnvelope childrenD_628 b hb)
def required_633_i1 : Finset Cell := ⟨(([(4, 4), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_633_i1 : Finset Cell := ⟨(([(4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_633_i1 : Fin 2 → Finset Cell := ![(placed21 1 (4, 3) required_8), (placed21 3 (4, 6) required_93)]
def childrenD_633_i1 : Fin 2 → Finset Cell := ![(placed21 1 (4, 3) envelope_8), (placed21 3 (4, 6) envelope_93)]
theorem common_sub_633_i1 : commonEnvelope childrenD_633_i1 ⊆ insert (5, 3) required_633_i1 := by decide +kernel
theorem child_required_sub_633_i1 : ∀ j, childrenC_633_i1 j ⊆ insert (5, 3) required_633_i1 := by decide +kernel
theorem child_envelope_sub_633_i1 : ∀ j, childrenD_633_i1 j ⊆ envelope_633_i1 := by decide +kernel
theorem pivot_mem_633_i1 : (5, 3) ∈ envelope_633_i1 := by decide +kernel
theorem children_work_633_i1 : ∀ j, Template HasSnaky 4 (childrenC_633_i1 j) (childrenD_633_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_93 3 (4, 6)).mono (by decide +kernel)
theorem row_works_633_i1 : Template HasSnaky 5 required_633_i1 envelope_633_i1 := by
  refine compose HasSnaky 4 childrenC_633_i1 childrenD_633_i1 children_work_633_i1 (5, 3)
    required_633_i1 envelope_633_i1 pivot_mem_633_i1 child_required_sub_633_i1 child_envelope_sub_633_i1 ?_
  intro b hb
  exact common_sub_633_i1 (mem_commonEnvelope childrenD_633_i1 b hb)
def required_633_i0 : Finset Cell := ⟨(([(4, 4), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_633_i0 : Finset Cell := ⟨(([(3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8), (7, 3), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_633_i0 : Fin 4 → Finset Cell := ![(placed21 2 (5, 3) required_27), (placed21 6 (5, 7) required_52), (placed21 3 (3, 6) required_144), required_633_i1]
def childrenD_633_i0 : Fin 4 → Finset Cell := ![(placed21 2 (5, 3) envelope_27), (placed21 6 (5, 7) envelope_52), (placed21 3 (3, 6) envelope_144), envelope_633_i1]
theorem common_sub_633_i0 : commonEnvelope childrenD_633_i0 ⊆ insert (5, 6) required_633_i0 := by decide +kernel
theorem child_required_sub_633_i0 : ∀ j, childrenC_633_i0 j ⊆ insert (5, 6) required_633_i0 := by decide +kernel
theorem child_envelope_sub_633_i0 : ∀ j, childrenD_633_i0 j ⊆ envelope_633_i0 := by decide +kernel
theorem pivot_mem_633_i0 : (5, 6) ∈ envelope_633_i0 := by decide +kernel
theorem children_work_633_i0 : ∀ j, Template HasSnaky 5 (childrenC_633_i0 j) (childrenD_633_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_27 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_144 3 (3, 6)).mono (by decide +kernel)
  · exact row_works_633_i1.mono (by decide +kernel)
theorem row_works_633_i0 : Template HasSnaky 6 required_633_i0 envelope_633_i0 := by
  refine compose HasSnaky 5 childrenC_633_i0 childrenD_633_i0 children_work_633_i0 (5, 6)
    required_633_i0 envelope_633_i0 pivot_mem_633_i0 child_required_sub_633_i0 child_envelope_sub_633_i0 ?_
  intro b hb
  exact common_sub_633_i0 (mem_commonEnvelope childrenD_633_i0 b hb)
def required_633 : Finset Cell := ⟨(([(3, 4), (3, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_633 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8), (7, 3), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_633 : Fin 3 → Finset Cell := ![(placed21 6 (6, 6) required_47), (placed21 6 (5, 6) required_144), required_633_i0]
def childrenD_633 : Fin 3 → Finset Cell := ![(placed21 6 (6, 6) envelope_47), (placed21 6 (5, 6) envelope_144), envelope_633_i0]
theorem common_sub_633 : commonEnvelope childrenD_633 ⊆ insert (4, 4) required_633 := by decide +kernel
theorem child_required_sub_633 : ∀ j, childrenC_633 j ⊆ insert (4, 4) required_633 := by decide +kernel
theorem child_envelope_sub_633 : ∀ j, childrenD_633 j ⊆ envelope_633 := by decide +kernel
theorem pivot_mem_633 : (4, 4) ∈ envelope_633 := by decide +kernel
theorem children_work_633 : ∀ j, Template HasSnaky 6 (childrenC_633 j) (childrenD_633 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_47 6 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_144 6 (5, 6)).mono (by decide +kernel)
  · exact row_works_633_i0.mono (by decide +kernel)
theorem row_works_633 : Template HasSnaky 7 required_633 envelope_633 := by
  refine compose HasSnaky 6 childrenC_633 childrenD_633 children_work_633 (4, 4)
    required_633 envelope_633 pivot_mem_633 child_required_sub_633 child_envelope_sub_633 ?_
  intro b hb
  exact common_sub_633 (mem_commonEnvelope childrenD_633 b hb)
def required_637_i2 : Finset Cell := ⟨(([(2, 3), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_637_i2 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_637_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) required_15), (placed21 1 (1, 3) required_44)]
def childrenD_637_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) envelope_15), (placed21 1 (1, 3) envelope_44)]
theorem common_sub_637_i2 : commonEnvelope childrenD_637_i2 ⊆ insert (4, 4) required_637_i2 := by decide +kernel
theorem child_required_sub_637_i2 : ∀ j, childrenC_637_i2 j ⊆ insert (4, 4) required_637_i2 := by decide +kernel
theorem child_envelope_sub_637_i2 : ∀ j, childrenD_637_i2 j ⊆ envelope_637_i2 := by decide +kernel
theorem pivot_mem_637_i2 : (4, 4) ∈ envelope_637_i2 := by decide +kernel
theorem children_work_637_i2 : ∀ j, Template HasSnaky 3 (childrenC_637_i2 j) (childrenD_637_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 6 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 1 (1, 3)).mono (by decide +kernel)
theorem row_works_637_i2 : Template HasSnaky 4 required_637_i2 envelope_637_i2 := by
  refine compose HasSnaky 3 childrenC_637_i2 childrenD_637_i2 children_work_637_i2 (4, 4)
    required_637_i2 envelope_637_i2 pivot_mem_637_i2 child_required_sub_637_i2 child_envelope_sub_637_i2 ?_
  intro b hb
  exact common_sub_637_i2 (mem_commonEnvelope childrenD_637_i2 b hb)
def required_637_i1 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_637_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_637_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_0), required_637_i2]
def childrenD_637_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_0), envelope_637_i2]
theorem common_sub_637_i1 : commonEnvelope childrenD_637_i1 ⊆ insert (3, 3) required_637_i1 := by decide +kernel
theorem child_required_sub_637_i1 : ∀ j, childrenC_637_i1 j ⊆ insert (3, 3) required_637_i1 := by decide +kernel
theorem child_envelope_sub_637_i1 : ∀ j, childrenD_637_i1 j ⊆ envelope_637_i1 := by decide +kernel
theorem pivot_mem_637_i1 : (3, 3) ∈ envelope_637_i1 := by decide +kernel
theorem children_work_637_i1 : ∀ j, Template HasSnaky 4 (childrenC_637_i1 j) (childrenD_637_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_637_i2.mono (by decide +kernel)
theorem row_works_637_i1 : Template HasSnaky 5 required_637_i1 envelope_637_i1 := by
  refine compose HasSnaky 4 childrenC_637_i1 childrenD_637_i1 children_work_637_i1 (3, 3)
    required_637_i1 envelope_637_i1 pivot_mem_637_i1 child_required_sub_637_i1 child_envelope_sub_637_i1 ?_
  intro b hb
  exact common_sub_637_i1 (mem_commonEnvelope childrenD_637_i1 b hb)
def required_637_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_637_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_637_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) required_5), required_637_i1]
def childrenD_637_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) envelope_5), envelope_637_i1]
theorem common_sub_637_i0 : commonEnvelope childrenD_637_i0 ⊆ insert (4, 3) required_637_i0 := by decide +kernel
theorem child_required_sub_637_i0 : ∀ j, childrenC_637_i0 j ⊆ insert (4, 3) required_637_i0 := by decide +kernel
theorem child_envelope_sub_637_i0 : ∀ j, childrenD_637_i0 j ⊆ envelope_637_i0 := by decide +kernel
theorem pivot_mem_637_i0 : (4, 3) ∈ envelope_637_i0 := by decide +kernel
theorem children_work_637_i0 : ∀ j, Template HasSnaky 5 (childrenC_637_i0 j) (childrenD_637_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_637_i1.mono (by decide +kernel)
theorem row_works_637_i0 : Template HasSnaky 6 required_637_i0 envelope_637_i0 := by
  refine compose HasSnaky 5 childrenC_637_i0 childrenD_637_i0 children_work_637_i0 (4, 3)
    required_637_i0 envelope_637_i0 pivot_mem_637_i0 child_required_sub_637_i0 child_envelope_sub_637_i0 ?_
  intro b hb
  exact common_sub_637_i0 (mem_commonEnvelope childrenD_637_i0 b hb)
def required_637 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_637 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_637 : Fin 4 → Finset Cell := ![(placed21 1 (1, 2) required_21), (placed21 3 (1, 3) required_41), (placed21 3 (1, 3) required_48), required_637_i0]
def childrenD_637 : Fin 4 → Finset Cell := ![(placed21 1 (1, 2) envelope_21), (placed21 3 (1, 3) envelope_41), (placed21 3 (1, 3) envelope_48), envelope_637_i0]
theorem common_sub_637 : commonEnvelope childrenD_637 ⊆ insert (4, 2) required_637 := by decide +kernel
theorem child_required_sub_637 : ∀ j, childrenC_637 j ⊆ insert (4, 2) required_637 := by decide +kernel
theorem child_envelope_sub_637 : ∀ j, childrenD_637 j ⊆ envelope_637 := by decide +kernel
theorem pivot_mem_637 : (4, 2) ∈ envelope_637 := by decide +kernel
theorem children_work_637 : ∀ j, Template HasSnaky 6 (childrenC_637 j) (childrenD_637 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_41 3 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_48 3 (1, 3)).mono (by decide +kernel)
  · exact row_works_637_i0.mono (by decide +kernel)
theorem row_works_637 : Template HasSnaky 7 required_637 envelope_637 := by
  refine compose HasSnaky 6 childrenC_637 childrenD_637 children_work_637 (4, 2)
    required_637 envelope_637 pivot_mem_637 child_required_sub_637 child_envelope_sub_637 ?_
  intro b hb
  exact common_sub_637 (mem_commonEnvelope childrenD_637 b hb)
def required_671_i0 : Finset Cell := ⟨(([(1, 2), (1, 4), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_671_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_671_i0 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) required_22), (placed21 2 (4, 0) required_464)]
def childrenD_671_i0 : Fin 2 → Finset Cell := ![(placed21 7 (5, 4) envelope_22), (placed21 2 (4, 0) envelope_464)]
theorem common_sub_671_i0 : commonEnvelope childrenD_671_i0 ⊆ insert (3, 4) required_671_i0 := by decide +kernel
theorem child_required_sub_671_i0 : ∀ j, childrenC_671_i0 j ⊆ insert (3, 4) required_671_i0 := by decide +kernel
theorem child_envelope_sub_671_i0 : ∀ j, childrenD_671_i0 j ⊆ envelope_671_i0 := by decide +kernel
theorem pivot_mem_671_i0 : (3, 4) ∈ envelope_671_i0 := by decide +kernel
theorem children_work_671_i0 : ∀ j, Template HasSnaky 5 (childrenC_671_i0 j) (childrenD_671_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 7 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_464 2 (4, 0)).mono (by decide +kernel)
theorem row_works_671_i0 : Template HasSnaky 6 required_671_i0 envelope_671_i0 := by
  refine compose HasSnaky 5 childrenC_671_i0 childrenD_671_i0 children_work_671_i0 (3, 4)
    required_671_i0 envelope_671_i0 pivot_mem_671_i0 child_required_sub_671_i0 child_envelope_sub_671_i0 ?_
  intro b hb
  exact common_sub_671_i0 (mem_commonEnvelope childrenD_671_i0 b hb)
def required_671 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_671 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_671 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_28), (placed21 1 (0, 2) required_126), (placed21 3 (0, 4) required_126), required_671_i0]
def childrenD_671 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_28), (placed21 1 (0, 2) envelope_126), (placed21 3 (0, 4) envelope_126), envelope_671_i0]
theorem common_sub_671 : commonEnvelope childrenD_671 ⊆ insert (3, 3) required_671 := by decide +kernel
theorem child_required_sub_671 : ∀ j, childrenC_671 j ⊆ insert (3, 3) required_671 := by decide +kernel
theorem child_envelope_sub_671 : ∀ j, childrenD_671 j ⊆ envelope_671 := by decide +kernel
theorem pivot_mem_671 : (3, 3) ∈ envelope_671 := by decide +kernel
theorem children_work_671 : ∀ j, Template HasSnaky 6 (childrenC_671 j) (childrenD_671 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_126 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_126 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_671_i0.mono (by decide +kernel)
theorem row_works_671 : Template HasSnaky 7 required_671 envelope_671 := by
  refine compose HasSnaky 6 childrenC_671 childrenD_671 children_work_671 (3, 3)
    required_671 envelope_671 pivot_mem_671 child_required_sub_671 child_envelope_sub_671 ?_
  intro b hb
  exact common_sub_671 (mem_commonEnvelope childrenD_671 b hb)
def required_680_i0 : Finset Cell := ⟨(([(2, 2), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_680_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_680_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 0) required_56), (placed21 6 (5, 5) required_179)]
def childrenD_680_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 0) envelope_56), (placed21 6 (5, 5) envelope_179)]
theorem common_sub_680_i0 : commonEnvelope childrenD_680_i0 ⊆ insert (1, 3) required_680_i0 := by decide +kernel
theorem child_required_sub_680_i0 : ∀ j, childrenC_680_i0 j ⊆ insert (1, 3) required_680_i0 := by decide +kernel
theorem child_envelope_sub_680_i0 : ∀ j, childrenD_680_i0 j ⊆ envelope_680_i0 := by decide +kernel
theorem pivot_mem_680_i0 : (1, 3) ∈ envelope_680_i0 := by decide +kernel
theorem children_work_680_i0 : ∀ j, Template HasSnaky 5 (childrenC_680_i0 j) (childrenD_680_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_56 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 6 (5, 5)).mono (by decide +kernel)
theorem row_works_680_i0 : Template HasSnaky 6 required_680_i0 envelope_680_i0 := by
  refine compose HasSnaky 5 childrenC_680_i0 childrenD_680_i0 children_work_680_i0 (1, 3)
    required_680_i0 envelope_680_i0 pivot_mem_680_i0 child_required_sub_680_i0 child_envelope_sub_680_i0 ?_
  intro b hb
  exact common_sub_680_i0 (mem_commonEnvelope childrenD_680_i0 b hb)
def required_680 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_680 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_680 : Fin 2 → Finset Cell := ![(placed21 6 (5, 3) required_0), required_680_i0]
def childrenD_680 : Fin 2 → Finset Cell := ![(placed21 6 (5, 3) envelope_0), envelope_680_i0]
theorem common_sub_680 : commonEnvelope childrenD_680 ⊆ insert (3, 3) required_680 := by decide +kernel
theorem child_required_sub_680 : ∀ j, childrenC_680 j ⊆ insert (3, 3) required_680 := by decide +kernel
theorem child_envelope_sub_680 : ∀ j, childrenD_680 j ⊆ envelope_680 := by decide +kernel
theorem pivot_mem_680 : (3, 3) ∈ envelope_680 := by decide +kernel
theorem children_work_680 : ∀ j, Template HasSnaky 6 (childrenC_680 j) (childrenD_680 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 3)).mono (by decide +kernel)
  · exact row_works_680_i0.mono (by decide +kernel)
theorem row_works_680 : Template HasSnaky 7 required_680 envelope_680 := by
  refine compose HasSnaky 6 childrenC_680 childrenD_680 children_work_680 (3, 3)
    required_680 envelope_680 pivot_mem_680 child_required_sub_680 child_envelope_sub_680 ?_
  intro b hb
  exact common_sub_680 (mem_commonEnvelope childrenD_680 b hb)
def height_593_i0 : ℕ := 6
def childrenH_593_i0 : Fin 4 → ℕ := ![height_36, height_105, height_250, height_592]
theorem height_exact_593_i0 : height_593_i0 = 1 + Finset.univ.sup childrenH_593_i0 := by decide +kernel
theorem required_origin_593_i0 : ∀ x ∈ required_593_i0,
    (∃ j, x ∈ childrenC_593_i0 j) ∨ ∀ j, x ∈ childrenD_593_i0 j := by decide +kernel
theorem required_exact_593_i0 : required_593_i0 =
    ((Finset.univ.biUnion childrenC_593_i0) ∪ commonEnvelope childrenD_593_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_593_i0 childrenD_593_i0 (4, 5) required_593_i0
    (by decide +kernel) child_required_sub_593_i0 common_sub_593_i0 required_origin_593_i0
theorem envelope_origin_593_i0 : ∀ x ∈ envelope_593_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_593_i0 j := by decide +kernel
theorem envelope_exact_593_i0 : envelope_593_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_593_i0) := by
  exact envelope_eq_combination childrenD_593_i0 (4, 5) envelope_593_i0
    pivot_mem_593_i0 child_envelope_sub_593_i0 envelope_origin_593_i0
def checked_593_i0 : CheckedCard where
  required := required_593_i0
  envelope := envelope_593_i0
  height := height_593_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_593_i0
def height_593 : ℕ := 7
def childrenH_593 : Fin 2 → ℕ := ![height_2, height_593_i0]
theorem height_exact_593 : height_593 = 1 + Finset.univ.sup childrenH_593 := by decide +kernel
theorem required_origin_593 : ∀ x ∈ required_593,
    (∃ j, x ∈ childrenC_593 j) ∨ ∀ j, x ∈ childrenD_593 j := by decide +kernel
theorem required_exact_593 : required_593 =
    ((Finset.univ.biUnion childrenC_593) ∪ commonEnvelope childrenD_593).erase (4, 3) := by
  exact required_eq_combination childrenC_593 childrenD_593 (4, 3) required_593
    (by decide +kernel) child_required_sub_593 common_sub_593 required_origin_593
theorem envelope_origin_593 : ∀ x ∈ envelope_593,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_593 j := by decide +kernel
theorem envelope_exact_593 : envelope_593 =
    insert (4, 3) (Finset.univ.biUnion childrenD_593) := by
  exact envelope_eq_combination childrenD_593 (4, 3) envelope_593
    pivot_mem_593 child_envelope_sub_593 envelope_origin_593
def checked_593 : CheckedCard where
  required := required_593
  envelope := envelope_593
  height := height_593
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_593
def height_610 : ℕ := 7
def childrenH_610 : Fin 4 → ℕ := ![height_19, height_197, height_225, height_609]
theorem height_exact_610 : height_610 = 1 + Finset.univ.sup childrenH_610 := by decide +kernel
theorem required_origin_610 : ∀ x ∈ required_610,
    (∃ j, x ∈ childrenC_610 j) ∨ ∀ j, x ∈ childrenD_610 j := by decide +kernel
theorem required_exact_610 : required_610 =
    ((Finset.univ.biUnion childrenC_610) ∪ commonEnvelope childrenD_610).erase (1, 5) := by
  exact required_eq_combination childrenC_610 childrenD_610 (1, 5) required_610
    (by decide +kernel) child_required_sub_610 common_sub_610 required_origin_610
theorem envelope_origin_610 : ∀ x ∈ envelope_610,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_610 j := by decide +kernel
theorem envelope_exact_610 : envelope_610 =
    insert (1, 5) (Finset.univ.biUnion childrenD_610) := by
  exact envelope_eq_combination childrenD_610 (1, 5) envelope_610
    pivot_mem_610 child_envelope_sub_610 envelope_origin_610
def checked_610 : CheckedCard where
  required := required_610
  envelope := envelope_610
  height := height_610
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_610
def height_620_i0 : ℕ := 6
def childrenH_620_i0 : Fin 3 → ℕ := ![height_17, height_37, height_233]
theorem height_exact_620_i0 : height_620_i0 = 1 + Finset.univ.sup childrenH_620_i0 := by decide +kernel
theorem required_origin_620_i0 : ∀ x ∈ required_620_i0,
    (∃ j, x ∈ childrenC_620_i0 j) ∨ ∀ j, x ∈ childrenD_620_i0 j := by decide +kernel
theorem required_exact_620_i0 : required_620_i0 =
    ((Finset.univ.biUnion childrenC_620_i0) ∪ commonEnvelope childrenD_620_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_620_i0 childrenD_620_i0 (3, 3) required_620_i0
    (by decide +kernel) child_required_sub_620_i0 common_sub_620_i0 required_origin_620_i0
theorem envelope_origin_620_i0 : ∀ x ∈ envelope_620_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_620_i0 j := by decide +kernel
theorem envelope_exact_620_i0 : envelope_620_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_620_i0) := by
  exact envelope_eq_combination childrenD_620_i0 (3, 3) envelope_620_i0
    pivot_mem_620_i0 child_envelope_sub_620_i0 envelope_origin_620_i0
def checked_620_i0 : CheckedCard where
  required := required_620_i0
  envelope := envelope_620_i0
  height := height_620_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_620_i0
def height_620 : ℕ := 7
def childrenH_620 : Fin 5 → ℕ := ![height_57, height_57, height_293, height_293, height_620_i0]
theorem height_exact_620 : height_620 = 1 + Finset.univ.sup childrenH_620 := by decide +kernel
theorem required_origin_620 : ∀ x ∈ required_620,
    (∃ j, x ∈ childrenC_620 j) ∨ ∀ j, x ∈ childrenD_620 j := by decide +kernel
theorem required_exact_620 : required_620 =
    ((Finset.univ.biUnion childrenC_620) ∪ commonEnvelope childrenD_620).erase (4, 5) := by
  exact required_eq_combination childrenC_620 childrenD_620 (4, 5) required_620
    (by decide +kernel) child_required_sub_620 common_sub_620 required_origin_620
theorem envelope_origin_620 : ∀ x ∈ envelope_620,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_620 j := by decide +kernel
theorem envelope_exact_620 : envelope_620 =
    insert (4, 5) (Finset.univ.biUnion childrenD_620) := by
  exact envelope_eq_combination childrenD_620 (4, 5) envelope_620
    pivot_mem_620 child_envelope_sub_620 envelope_origin_620
def checked_620 : CheckedCard where
  required := required_620
  envelope := envelope_620
  height := height_620
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_620
def height_621_i0 : ℕ := 6
def childrenH_621_i0 : Fin 3 → ℕ := ![height_15, height_159, height_164]
theorem height_exact_621_i0 : height_621_i0 = 1 + Finset.univ.sup childrenH_621_i0 := by decide +kernel
theorem required_origin_621_i0 : ∀ x ∈ required_621_i0,
    (∃ j, x ∈ childrenC_621_i0 j) ∨ ∀ j, x ∈ childrenD_621_i0 j := by decide +kernel
theorem required_exact_621_i0 : required_621_i0 =
    ((Finset.univ.biUnion childrenC_621_i0) ∪ commonEnvelope childrenD_621_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_621_i0 childrenD_621_i0 (2, 3) required_621_i0
    (by decide +kernel) child_required_sub_621_i0 common_sub_621_i0 required_origin_621_i0
theorem envelope_origin_621_i0 : ∀ x ∈ envelope_621_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_621_i0 j := by decide +kernel
theorem envelope_exact_621_i0 : envelope_621_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_621_i0) := by
  exact envelope_eq_combination childrenD_621_i0 (2, 3) envelope_621_i0
    pivot_mem_621_i0 child_envelope_sub_621_i0 envelope_origin_621_i0
def checked_621_i0 : CheckedCard where
  required := required_621_i0
  envelope := envelope_621_i0
  height := height_621_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_621_i0
def height_621_i1 : ℕ := 6
def childrenH_621_i1 : Fin 2 → ℕ := ![height_0, height_133]
theorem height_exact_621_i1 : height_621_i1 = 1 + Finset.univ.sup childrenH_621_i1 := by decide +kernel
theorem required_origin_621_i1 : ∀ x ∈ required_621_i1,
    (∃ j, x ∈ childrenC_621_i1 j) ∨ ∀ j, x ∈ childrenD_621_i1 j := by decide +kernel
theorem required_exact_621_i1 : required_621_i1 =
    ((Finset.univ.biUnion childrenC_621_i1) ∪ commonEnvelope childrenD_621_i1).erase (1, 4) := by
  exact required_eq_combination childrenC_621_i1 childrenD_621_i1 (1, 4) required_621_i1
    (by decide +kernel) child_required_sub_621_i1 common_sub_621_i1 required_origin_621_i1
theorem envelope_origin_621_i1 : ∀ x ∈ envelope_621_i1,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_621_i1 j := by decide +kernel
theorem envelope_exact_621_i1 : envelope_621_i1 =
    insert (1, 4) (Finset.univ.biUnion childrenD_621_i1) := by
  exact envelope_eq_combination childrenD_621_i1 (1, 4) envelope_621_i1
    pivot_mem_621_i1 child_envelope_sub_621_i1 envelope_origin_621_i1
def checked_621_i1 : CheckedCard where
  required := required_621_i1
  envelope := envelope_621_i1
  height := height_621_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_621_i1
def height_621 : ℕ := 7
def childrenH_621 : Fin 6 → ℕ := ![height_206, height_238, height_414, height_417, height_621_i0, height_621_i1]
theorem height_exact_621 : height_621 = 1 + Finset.univ.sup childrenH_621 := by decide +kernel
theorem required_origin_621 : ∀ x ∈ required_621,
    (∃ j, x ∈ childrenC_621 j) ∨ ∀ j, x ∈ childrenD_621 j := by decide +kernel
theorem required_exact_621 : required_621 =
    ((Finset.univ.biUnion childrenC_621) ∪ commonEnvelope childrenD_621).erase (2, 4) := by
  exact required_eq_combination childrenC_621 childrenD_621 (2, 4) required_621
    (by decide +kernel) child_required_sub_621 common_sub_621 required_origin_621
theorem envelope_origin_621 : ∀ x ∈ envelope_621,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_621 j := by decide +kernel
theorem envelope_exact_621 : envelope_621 =
    insert (2, 4) (Finset.univ.biUnion childrenD_621) := by
  exact envelope_eq_combination childrenD_621 (2, 4) envelope_621
    pivot_mem_621 child_envelope_sub_621 envelope_origin_621
def checked_621 : CheckedCard where
  required := required_621
  envelope := envelope_621
  height := height_621
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_621
def height_628_i0 : ℕ := 4
def childrenH_628_i0 : Fin 2 → ℕ := ![height_36, height_53]
theorem height_exact_628_i0 : height_628_i0 = 1 + Finset.univ.sup childrenH_628_i0 := by decide +kernel
theorem required_origin_628_i0 : ∀ x ∈ required_628_i0,
    (∃ j, x ∈ childrenC_628_i0 j) ∨ ∀ j, x ∈ childrenD_628_i0 j := by decide +kernel
theorem required_exact_628_i0 : required_628_i0 =
    ((Finset.univ.biUnion childrenC_628_i0) ∪ commonEnvelope childrenD_628_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_628_i0 childrenD_628_i0 (3, 2) required_628_i0
    (by decide +kernel) child_required_sub_628_i0 common_sub_628_i0 required_origin_628_i0
theorem envelope_origin_628_i0 : ∀ x ∈ envelope_628_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_628_i0 j := by decide +kernel
theorem envelope_exact_628_i0 : envelope_628_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_628_i0) := by
  exact envelope_eq_combination childrenD_628_i0 (3, 2) envelope_628_i0
    pivot_mem_628_i0 child_envelope_sub_628_i0 envelope_origin_628_i0
def checked_628_i0 : CheckedCard where
  required := required_628_i0
  envelope := envelope_628_i0
  height := height_628_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_628_i0
def height_628_i1 : ℕ := 6
def childrenH_628_i1 : Fin 2 → ℕ := ![height_34, height_464]
theorem height_exact_628_i1 : height_628_i1 = 1 + Finset.univ.sup childrenH_628_i1 := by decide +kernel
theorem required_origin_628_i1 : ∀ x ∈ required_628_i1,
    (∃ j, x ∈ childrenC_628_i1 j) ∨ ∀ j, x ∈ childrenD_628_i1 j := by decide +kernel
theorem required_exact_628_i1 : required_628_i1 =
    ((Finset.univ.biUnion childrenC_628_i1) ∪ commonEnvelope childrenD_628_i1).erase (3, 4) := by
  exact required_eq_combination childrenC_628_i1 childrenD_628_i1 (3, 4) required_628_i1
    (by decide +kernel) child_required_sub_628_i1 common_sub_628_i1 required_origin_628_i1
theorem envelope_origin_628_i1 : ∀ x ∈ envelope_628_i1,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_628_i1 j := by decide +kernel
theorem envelope_exact_628_i1 : envelope_628_i1 =
    insert (3, 4) (Finset.univ.biUnion childrenD_628_i1) := by
  exact envelope_eq_combination childrenD_628_i1 (3, 4) envelope_628_i1
    pivot_mem_628_i1 child_envelope_sub_628_i1 envelope_origin_628_i1
def checked_628_i1 : CheckedCard where
  required := required_628_i1
  envelope := envelope_628_i1
  height := height_628_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_628_i1
def height_628_i2 : ℕ := 6
def childrenH_628_i2 : Fin 2 → ℕ := ![height_5, height_265]
theorem height_exact_628_i2 : height_628_i2 = 1 + Finset.univ.sup childrenH_628_i2 := by decide +kernel
theorem required_origin_628_i2 : ∀ x ∈ required_628_i2,
    (∃ j, x ∈ childrenC_628_i2 j) ∨ ∀ j, x ∈ childrenD_628_i2 j := by decide +kernel
theorem required_exact_628_i2 : required_628_i2 =
    ((Finset.univ.biUnion childrenC_628_i2) ∪ commonEnvelope childrenD_628_i2).erase (2, 3) := by
  exact required_eq_combination childrenC_628_i2 childrenD_628_i2 (2, 3) required_628_i2
    (by decide +kernel) child_required_sub_628_i2 common_sub_628_i2 required_origin_628_i2
theorem envelope_origin_628_i2 : ∀ x ∈ envelope_628_i2,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_628_i2 j := by decide +kernel
theorem envelope_exact_628_i2 : envelope_628_i2 =
    insert (2, 3) (Finset.univ.biUnion childrenD_628_i2) := by
  exact envelope_eq_combination childrenD_628_i2 (2, 3) envelope_628_i2
    pivot_mem_628_i2 child_envelope_sub_628_i2 envelope_origin_628_i2
def checked_628_i2 : CheckedCard where
  required := required_628_i2
  envelope := envelope_628_i2
  height := height_628_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_628_i2
def height_628 : ℕ := 7
def childrenH_628 : Fin 5 → ℕ := ![height_126, height_270, height_628_i0, height_628_i1, height_628_i2]
theorem height_exact_628 : height_628 = 1 + Finset.univ.sup childrenH_628 := by decide +kernel
theorem required_origin_628 : ∀ x ∈ required_628,
    (∃ j, x ∈ childrenC_628 j) ∨ ∀ j, x ∈ childrenD_628 j := by decide +kernel
theorem required_exact_628 : required_628 =
    ((Finset.univ.biUnion childrenC_628) ∪ commonEnvelope childrenD_628).erase (3, 3) := by
  exact required_eq_combination childrenC_628 childrenD_628 (3, 3) required_628
    (by decide +kernel) child_required_sub_628 common_sub_628 required_origin_628
theorem envelope_origin_628 : ∀ x ∈ envelope_628,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_628 j := by decide +kernel
theorem envelope_exact_628 : envelope_628 =
    insert (3, 3) (Finset.univ.biUnion childrenD_628) := by
  exact envelope_eq_combination childrenD_628 (3, 3) envelope_628
    pivot_mem_628 child_envelope_sub_628 envelope_origin_628
def checked_628 : CheckedCard where
  required := required_628
  envelope := envelope_628
  height := height_628
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_628
def height_633_i1 : ℕ := 5
def childrenH_633_i1 : Fin 2 → ℕ := ![height_8, height_93]
theorem height_exact_633_i1 : height_633_i1 = 1 + Finset.univ.sup childrenH_633_i1 := by decide +kernel
theorem required_origin_633_i1 : ∀ x ∈ required_633_i1,
    (∃ j, x ∈ childrenC_633_i1 j) ∨ ∀ j, x ∈ childrenD_633_i1 j := by decide +kernel
theorem required_exact_633_i1 : required_633_i1 =
    ((Finset.univ.biUnion childrenC_633_i1) ∪ commonEnvelope childrenD_633_i1).erase (5, 3) := by
  exact required_eq_combination childrenC_633_i1 childrenD_633_i1 (5, 3) required_633_i1
    (by decide +kernel) child_required_sub_633_i1 common_sub_633_i1 required_origin_633_i1
theorem envelope_origin_633_i1 : ∀ x ∈ envelope_633_i1,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_633_i1 j := by decide +kernel
theorem envelope_exact_633_i1 : envelope_633_i1 =
    insert (5, 3) (Finset.univ.biUnion childrenD_633_i1) := by
  exact envelope_eq_combination childrenD_633_i1 (5, 3) envelope_633_i1
    pivot_mem_633_i1 child_envelope_sub_633_i1 envelope_origin_633_i1
def checked_633_i1 : CheckedCard where
  required := required_633_i1
  envelope := envelope_633_i1
  height := height_633_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_633_i1
def height_633_i0 : ℕ := 6
def childrenH_633_i0 : Fin 4 → ℕ := ![height_27, height_52, height_144, height_633_i1]
theorem height_exact_633_i0 : height_633_i0 = 1 + Finset.univ.sup childrenH_633_i0 := by decide +kernel
theorem required_origin_633_i0 : ∀ x ∈ required_633_i0,
    (∃ j, x ∈ childrenC_633_i0 j) ∨ ∀ j, x ∈ childrenD_633_i0 j := by decide +kernel
theorem required_exact_633_i0 : required_633_i0 =
    ((Finset.univ.biUnion childrenC_633_i0) ∪ commonEnvelope childrenD_633_i0).erase (5, 6) := by
  exact required_eq_combination childrenC_633_i0 childrenD_633_i0 (5, 6) required_633_i0
    (by decide +kernel) child_required_sub_633_i0 common_sub_633_i0 required_origin_633_i0
theorem envelope_origin_633_i0 : ∀ x ∈ envelope_633_i0,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_633_i0 j := by decide +kernel
theorem envelope_exact_633_i0 : envelope_633_i0 =
    insert (5, 6) (Finset.univ.biUnion childrenD_633_i0) := by
  exact envelope_eq_combination childrenD_633_i0 (5, 6) envelope_633_i0
    pivot_mem_633_i0 child_envelope_sub_633_i0 envelope_origin_633_i0
def checked_633_i0 : CheckedCard where
  required := required_633_i0
  envelope := envelope_633_i0
  height := height_633_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_633_i0
def height_633 : ℕ := 7
def childrenH_633 : Fin 3 → ℕ := ![height_47, height_144, height_633_i0]
theorem height_exact_633 : height_633 = 1 + Finset.univ.sup childrenH_633 := by decide +kernel
theorem required_origin_633 : ∀ x ∈ required_633,
    (∃ j, x ∈ childrenC_633 j) ∨ ∀ j, x ∈ childrenD_633 j := by decide +kernel
theorem required_exact_633 : required_633 =
    ((Finset.univ.biUnion childrenC_633) ∪ commonEnvelope childrenD_633).erase (4, 4) := by
  exact required_eq_combination childrenC_633 childrenD_633 (4, 4) required_633
    (by decide +kernel) child_required_sub_633 common_sub_633 required_origin_633
theorem envelope_origin_633 : ∀ x ∈ envelope_633,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_633 j := by decide +kernel
theorem envelope_exact_633 : envelope_633 =
    insert (4, 4) (Finset.univ.biUnion childrenD_633) := by
  exact envelope_eq_combination childrenD_633 (4, 4) envelope_633
    pivot_mem_633 child_envelope_sub_633 envelope_origin_633
def checked_633 : CheckedCard where
  required := required_633
  envelope := envelope_633
  height := height_633
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_633
def height_637_i2 : ℕ := 4
def childrenH_637_i2 : Fin 2 → ℕ := ![height_15, height_44]
theorem height_exact_637_i2 : height_637_i2 = 1 + Finset.univ.sup childrenH_637_i2 := by decide +kernel
theorem required_origin_637_i2 : ∀ x ∈ required_637_i2,
    (∃ j, x ∈ childrenC_637_i2 j) ∨ ∀ j, x ∈ childrenD_637_i2 j := by decide +kernel
theorem required_exact_637_i2 : required_637_i2 =
    ((Finset.univ.biUnion childrenC_637_i2) ∪ commonEnvelope childrenD_637_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_637_i2 childrenD_637_i2 (4, 4) required_637_i2
    (by decide +kernel) child_required_sub_637_i2 common_sub_637_i2 required_origin_637_i2
theorem envelope_origin_637_i2 : ∀ x ∈ envelope_637_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_637_i2 j := by decide +kernel
theorem envelope_exact_637_i2 : envelope_637_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_637_i2) := by
  exact envelope_eq_combination childrenD_637_i2 (4, 4) envelope_637_i2
    pivot_mem_637_i2 child_envelope_sub_637_i2 envelope_origin_637_i2
def checked_637_i2 : CheckedCard where
  required := required_637_i2
  envelope := envelope_637_i2
  height := height_637_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_637_i2
def height_637_i1 : ℕ := 5
def childrenH_637_i1 : Fin 2 → ℕ := ![height_0, height_637_i2]
theorem height_exact_637_i1 : height_637_i1 = 1 + Finset.univ.sup childrenH_637_i1 := by decide +kernel
theorem required_origin_637_i1 : ∀ x ∈ required_637_i1,
    (∃ j, x ∈ childrenC_637_i1 j) ∨ ∀ j, x ∈ childrenD_637_i1 j := by decide +kernel
theorem required_exact_637_i1 : required_637_i1 =
    ((Finset.univ.biUnion childrenC_637_i1) ∪ commonEnvelope childrenD_637_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_637_i1 childrenD_637_i1 (3, 3) required_637_i1
    (by decide +kernel) child_required_sub_637_i1 common_sub_637_i1 required_origin_637_i1
theorem envelope_origin_637_i1 : ∀ x ∈ envelope_637_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_637_i1 j := by decide +kernel
theorem envelope_exact_637_i1 : envelope_637_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_637_i1) := by
  exact envelope_eq_combination childrenD_637_i1 (3, 3) envelope_637_i1
    pivot_mem_637_i1 child_envelope_sub_637_i1 envelope_origin_637_i1
def checked_637_i1 : CheckedCard where
  required := required_637_i1
  envelope := envelope_637_i1
  height := height_637_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_637_i1
def height_637_i0 : ℕ := 6
def childrenH_637_i0 : Fin 2 → ℕ := ![height_5, height_637_i1]
theorem height_exact_637_i0 : height_637_i0 = 1 + Finset.univ.sup childrenH_637_i0 := by decide +kernel
theorem required_origin_637_i0 : ∀ x ∈ required_637_i0,
    (∃ j, x ∈ childrenC_637_i0 j) ∨ ∀ j, x ∈ childrenD_637_i0 j := by decide +kernel
theorem required_exact_637_i0 : required_637_i0 =
    ((Finset.univ.biUnion childrenC_637_i0) ∪ commonEnvelope childrenD_637_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_637_i0 childrenD_637_i0 (4, 3) required_637_i0
    (by decide +kernel) child_required_sub_637_i0 common_sub_637_i0 required_origin_637_i0
theorem envelope_origin_637_i0 : ∀ x ∈ envelope_637_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_637_i0 j := by decide +kernel
theorem envelope_exact_637_i0 : envelope_637_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_637_i0) := by
  exact envelope_eq_combination childrenD_637_i0 (4, 3) envelope_637_i0
    pivot_mem_637_i0 child_envelope_sub_637_i0 envelope_origin_637_i0
def checked_637_i0 : CheckedCard where
  required := required_637_i0
  envelope := envelope_637_i0
  height := height_637_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_637_i0
def height_637 : ℕ := 7
def childrenH_637 : Fin 4 → ℕ := ![height_21, height_41, height_48, height_637_i0]
theorem height_exact_637 : height_637 = 1 + Finset.univ.sup childrenH_637 := by decide +kernel
theorem required_origin_637 : ∀ x ∈ required_637,
    (∃ j, x ∈ childrenC_637 j) ∨ ∀ j, x ∈ childrenD_637 j := by decide +kernel
theorem required_exact_637 : required_637 =
    ((Finset.univ.biUnion childrenC_637) ∪ commonEnvelope childrenD_637).erase (4, 2) := by
  exact required_eq_combination childrenC_637 childrenD_637 (4, 2) required_637
    (by decide +kernel) child_required_sub_637 common_sub_637 required_origin_637
theorem envelope_origin_637 : ∀ x ∈ envelope_637,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_637 j := by decide +kernel
theorem envelope_exact_637 : envelope_637 =
    insert (4, 2) (Finset.univ.biUnion childrenD_637) := by
  exact envelope_eq_combination childrenD_637 (4, 2) envelope_637
    pivot_mem_637 child_envelope_sub_637 envelope_origin_637
def checked_637 : CheckedCard where
  required := required_637
  envelope := envelope_637
  height := height_637
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_637
def height_671_i0 : ℕ := 6
def childrenH_671_i0 : Fin 2 → ℕ := ![height_22, height_464]
theorem height_exact_671_i0 : height_671_i0 = 1 + Finset.univ.sup childrenH_671_i0 := by decide +kernel
theorem required_origin_671_i0 : ∀ x ∈ required_671_i0,
    (∃ j, x ∈ childrenC_671_i0 j) ∨ ∀ j, x ∈ childrenD_671_i0 j := by decide +kernel
theorem required_exact_671_i0 : required_671_i0 =
    ((Finset.univ.biUnion childrenC_671_i0) ∪ commonEnvelope childrenD_671_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_671_i0 childrenD_671_i0 (3, 4) required_671_i0
    (by decide +kernel) child_required_sub_671_i0 common_sub_671_i0 required_origin_671_i0
theorem envelope_origin_671_i0 : ∀ x ∈ envelope_671_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_671_i0 j := by decide +kernel
theorem envelope_exact_671_i0 : envelope_671_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_671_i0) := by
  exact envelope_eq_combination childrenD_671_i0 (3, 4) envelope_671_i0
    pivot_mem_671_i0 child_envelope_sub_671_i0 envelope_origin_671_i0
def checked_671_i0 : CheckedCard where
  required := required_671_i0
  envelope := envelope_671_i0
  height := height_671_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_671_i0
def height_671 : ℕ := 7
def childrenH_671 : Fin 4 → ℕ := ![height_28, height_126, height_126, height_671_i0]
theorem height_exact_671 : height_671 = 1 + Finset.univ.sup childrenH_671 := by decide +kernel
theorem required_origin_671 : ∀ x ∈ required_671,
    (∃ j, x ∈ childrenC_671 j) ∨ ∀ j, x ∈ childrenD_671 j := by decide +kernel
theorem required_exact_671 : required_671 =
    ((Finset.univ.biUnion childrenC_671) ∪ commonEnvelope childrenD_671).erase (3, 3) := by
  exact required_eq_combination childrenC_671 childrenD_671 (3, 3) required_671
    (by decide +kernel) child_required_sub_671 common_sub_671 required_origin_671
theorem envelope_origin_671 : ∀ x ∈ envelope_671,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_671 j := by decide +kernel
theorem envelope_exact_671 : envelope_671 =
    insert (3, 3) (Finset.univ.biUnion childrenD_671) := by
  exact envelope_eq_combination childrenD_671 (3, 3) envelope_671
    pivot_mem_671 child_envelope_sub_671 envelope_origin_671
def checked_671 : CheckedCard where
  required := required_671
  envelope := envelope_671
  height := height_671
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_671
def height_680_i0 : ℕ := 6
def childrenH_680_i0 : Fin 2 → ℕ := ![height_56, height_179]
theorem height_exact_680_i0 : height_680_i0 = 1 + Finset.univ.sup childrenH_680_i0 := by decide +kernel
theorem required_origin_680_i0 : ∀ x ∈ required_680_i0,
    (∃ j, x ∈ childrenC_680_i0 j) ∨ ∀ j, x ∈ childrenD_680_i0 j := by decide +kernel
theorem required_exact_680_i0 : required_680_i0 =
    ((Finset.univ.biUnion childrenC_680_i0) ∪ commonEnvelope childrenD_680_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_680_i0 childrenD_680_i0 (1, 3) required_680_i0
    (by decide +kernel) child_required_sub_680_i0 common_sub_680_i0 required_origin_680_i0
theorem envelope_origin_680_i0 : ∀ x ∈ envelope_680_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_680_i0 j := by decide +kernel
theorem envelope_exact_680_i0 : envelope_680_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_680_i0) := by
  exact envelope_eq_combination childrenD_680_i0 (1, 3) envelope_680_i0
    pivot_mem_680_i0 child_envelope_sub_680_i0 envelope_origin_680_i0
def checked_680_i0 : CheckedCard where
  required := required_680_i0
  envelope := envelope_680_i0
  height := height_680_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_680_i0
def height_680 : ℕ := 7
def childrenH_680 : Fin 2 → ℕ := ![height_0, height_680_i0]
theorem height_exact_680 : height_680 = 1 + Finset.univ.sup childrenH_680 := by decide +kernel
theorem required_origin_680 : ∀ x ∈ required_680,
    (∃ j, x ∈ childrenC_680 j) ∨ ∀ j, x ∈ childrenD_680 j := by decide +kernel
theorem required_exact_680 : required_680 =
    ((Finset.univ.biUnion childrenC_680) ∪ commonEnvelope childrenD_680).erase (3, 3) := by
  exact required_eq_combination childrenC_680 childrenD_680 (3, 3) required_680
    (by decide +kernel) child_required_sub_680 common_sub_680 required_origin_680
theorem envelope_origin_680 : ∀ x ∈ envelope_680,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_680 j := by decide +kernel
theorem envelope_exact_680 : envelope_680 =
    insert (3, 3) (Finset.univ.biUnion childrenD_680) := by
  exact envelope_eq_combination childrenD_680 (3, 3) envelope_680
    pivot_mem_680 child_envelope_sub_680 envelope_origin_680
def checked_680 : CheckedCard where
  required := required_680
  envelope := envelope_680
  height := height_680
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_680
end SnakyPrototype.Certificate21

end OAI
