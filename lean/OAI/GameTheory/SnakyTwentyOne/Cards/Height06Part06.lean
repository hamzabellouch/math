import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_521_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_521_i1 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 4), (3, 5), (4, 1), (4, 4), (5, 1), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_521_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_45), (placed21 3 (0, 4) required_45)]
def childrenD_521_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_45), (placed21 3 (0, 4) envelope_45)]
theorem common_sub_521_i1 : commonEnvelope childrenD_521_i1 ⊆ insert (2, 3) required_521_i1 := by decide +kernel
theorem child_required_sub_521_i1 : ∀ j, childrenC_521_i1 j ⊆ insert (2, 3) required_521_i1 := by decide +kernel
theorem child_envelope_sub_521_i1 : ∀ j, childrenD_521_i1 j ⊆ envelope_521_i1 := by decide +kernel
theorem pivot_mem_521_i1 : (2, 3) ∈ envelope_521_i1 := by decide +kernel
theorem children_work_521_i1 : ∀ j, Template HasSnaky 3 (childrenC_521_i1 j) (childrenD_521_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_45 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_45 3 (0, 4)).mono (by decide +kernel)
theorem row_works_521_i1 : Template HasSnaky 4 required_521_i1 envelope_521_i1 := by
  refine compose HasSnaky 3 childrenC_521_i1 childrenD_521_i1 children_work_521_i1 (2, 3)
    required_521_i1 envelope_521_i1 pivot_mem_521_i1 child_required_sub_521_i1 child_envelope_sub_521_i1 ?_
  intro b hb
  exact common_sub_521_i1 (mem_commonEnvelope childrenD_521_i1 b hb)
def required_521_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_521_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 4), (3, 5), (4, 1), (4, 4), (5, 1), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_521_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_521_i1]
def childrenD_521_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_521_i1]
theorem common_sub_521_i0 : commonEnvelope childrenD_521_i0 ⊆ insert (2, 4) required_521_i0 := by decide +kernel
theorem child_required_sub_521_i0 : ∀ j, childrenC_521_i0 j ⊆ insert (2, 4) required_521_i0 := by decide +kernel
theorem child_envelope_sub_521_i0 : ∀ j, childrenD_521_i0 j ⊆ envelope_521_i0 := by decide +kernel
theorem pivot_mem_521_i0 : (2, 4) ∈ envelope_521_i0 := by decide +kernel
theorem children_work_521_i0 : ∀ j, Template HasSnaky 4 (childrenC_521_i0 j) (childrenD_521_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_521_i1.mono (by decide +kernel)
theorem row_works_521_i0 : Template HasSnaky 5 required_521_i0 envelope_521_i0 := by
  refine compose HasSnaky 4 childrenC_521_i0 childrenD_521_i0 children_work_521_i0 (2, 4)
    required_521_i0 envelope_521_i0 pivot_mem_521_i0 child_required_sub_521_i0 child_envelope_sub_521_i0 ?_
  intro b hb
  exact common_sub_521_i0 (mem_commonEnvelope childrenD_521_i0 b hb)
def required_521 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_521 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 4), (3, 5), (4, 1), (4, 4), (5, 1), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_521 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), required_521_i0]
def childrenD_521 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), envelope_521_i0]
theorem common_sub_521 : commonEnvelope childrenD_521 ⊆ insert (2, 1) required_521 := by decide +kernel
theorem child_required_sub_521 : ∀ j, childrenC_521 j ⊆ insert (2, 1) required_521 := by decide +kernel
theorem child_envelope_sub_521 : ∀ j, childrenD_521 j ⊆ envelope_521 := by decide +kernel
theorem pivot_mem_521 : (2, 1) ∈ envelope_521 := by decide +kernel
theorem children_work_521 : ∀ j, Template HasSnaky 5 (childrenC_521 j) (childrenD_521 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_521_i0.mono (by decide +kernel)
theorem row_works_521 : Template HasSnaky 6 required_521 envelope_521 := by
  refine compose HasSnaky 5 childrenC_521 childrenD_521 children_work_521 (2, 1)
    required_521 envelope_521 pivot_mem_521 child_required_sub_521 child_envelope_sub_521 ?_
  intro b hb
  exact common_sub_521 (mem_commonEnvelope childrenD_521 b hb)
def required_525_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (3, 0), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_525_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_525_i1 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) required_21), (placed21 0 (2, 0) required_37), (placed21 5 (4, 0) required_78)]
def childrenD_525_i1 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) envelope_21), (placed21 0 (2, 0) envelope_37), (placed21 5 (4, 0) envelope_78)]
theorem common_sub_525_i1 : commonEnvelope childrenD_525_i1 ⊆ insert (3, 3) required_525_i1 := by decide +kernel
theorem child_required_sub_525_i1 : ∀ j, childrenC_525_i1 j ⊆ insert (3, 3) required_525_i1 := by decide +kernel
theorem child_envelope_sub_525_i1 : ∀ j, childrenD_525_i1 j ⊆ envelope_525_i1 := by decide +kernel
theorem pivot_mem_525_i1 : (3, 3) ∈ envelope_525_i1 := by decide +kernel
theorem children_work_525_i1 : ∀ j, Template HasSnaky 3 (childrenC_525_i1 j) (childrenD_525_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 5 (4, 0)).mono (by decide +kernel)
theorem row_works_525_i1 : Template HasSnaky 4 required_525_i1 envelope_525_i1 := by
  refine compose HasSnaky 3 childrenC_525_i1 childrenD_525_i1 children_work_525_i1 (3, 3)
    required_525_i1 envelope_525_i1 pivot_mem_525_i1 child_required_sub_525_i1 child_envelope_sub_525_i1 ?_
  intro b hb
  exact common_sub_525_i1 (mem_commonEnvelope childrenD_525_i1 b hb)
def required_525_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_525_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_525_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_525_i1]
def childrenD_525_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_525_i1]
theorem common_sub_525_i0 : commonEnvelope childrenD_525_i0 ⊆ insert (3, 2) required_525_i0 := by decide +kernel
theorem child_required_sub_525_i0 : ∀ j, childrenC_525_i0 j ⊆ insert (3, 2) required_525_i0 := by decide +kernel
theorem child_envelope_sub_525_i0 : ∀ j, childrenD_525_i0 j ⊆ envelope_525_i0 := by decide +kernel
theorem pivot_mem_525_i0 : (3, 2) ∈ envelope_525_i0 := by decide +kernel
theorem children_work_525_i0 : ∀ j, Template HasSnaky 4 (childrenC_525_i0 j) (childrenD_525_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_525_i1.mono (by decide +kernel)
theorem row_works_525_i0 : Template HasSnaky 5 required_525_i0 envelope_525_i0 := by
  refine compose HasSnaky 4 childrenC_525_i0 childrenD_525_i0 children_work_525_i0 (3, 2)
    required_525_i0 envelope_525_i0 pivot_mem_525_i0 child_required_sub_525_i0 child_envelope_sub_525_i0 ?_
  intro b hb
  exact common_sub_525_i0 (mem_commonEnvelope childrenD_525_i0 b hb)
def required_525 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_525 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_525 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), required_525_i0]
def childrenD_525 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), envelope_525_i0]
theorem common_sub_525 : commonEnvelope childrenD_525 ⊆ insert (3, 0) required_525 := by decide +kernel
theorem child_required_sub_525 : ∀ j, childrenC_525 j ⊆ insert (3, 0) required_525 := by decide +kernel
theorem child_envelope_sub_525 : ∀ j, childrenD_525 j ⊆ envelope_525 := by decide +kernel
theorem pivot_mem_525 : (3, 0) ∈ envelope_525 := by decide +kernel
theorem children_work_525 : ∀ j, Template HasSnaky 5 (childrenC_525 j) (childrenD_525 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_525_i0.mono (by decide +kernel)
theorem row_works_525 : Template HasSnaky 6 required_525 envelope_525 := by
  refine compose HasSnaky 5 childrenC_525 childrenD_525 children_work_525 (3, 0)
    required_525 envelope_525 pivot_mem_525 child_required_sub_525 child_envelope_sub_525 ?_
  intro b hb
  exact common_sub_525 (mem_commonEnvelope childrenD_525 b hb)
def required_544_i1 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_544_i1 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_544_i1 : Fin 2 → Finset Cell := ![(placed21 2 (6, 3) required_0), (placed21 7 (6, 4) required_62)]
def childrenD_544_i1 : Fin 2 → Finset Cell := ![(placed21 2 (6, 3) envelope_0), (placed21 7 (6, 4) envelope_62)]
theorem common_sub_544_i1 : commonEnvelope childrenD_544_i1 ⊆ insert (5, 3) required_544_i1 := by decide +kernel
theorem child_required_sub_544_i1 : ∀ j, childrenC_544_i1 j ⊆ insert (5, 3) required_544_i1 := by decide +kernel
theorem child_envelope_sub_544_i1 : ∀ j, childrenD_544_i1 j ⊆ envelope_544_i1 := by decide +kernel
theorem pivot_mem_544_i1 : (5, 3) ∈ envelope_544_i1 := by decide +kernel
theorem children_work_544_i1 : ∀ j, Template HasSnaky 3 (childrenC_544_i1 j) (childrenD_544_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_62 7 (6, 4)).mono (by decide +kernel)
theorem row_works_544_i1 : Template HasSnaky 4 required_544_i1 envelope_544_i1 := by
  refine compose HasSnaky 3 childrenC_544_i1 childrenD_544_i1 children_work_544_i1 (5, 3)
    required_544_i1 envelope_544_i1 pivot_mem_544_i1 child_required_sub_544_i1 child_envelope_sub_544_i1 ?_
  intro b hb
  exact common_sub_544_i1 (mem_commonEnvelope childrenD_544_i1 b hb)
def required_544_i0 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_544_i0 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_544_i0 : Fin 3 → Finset Cell := ![(placed21 5 (5, 3) required_15), (placed21 1 (0, 2) required_259), required_544_i1]
def childrenD_544_i0 : Fin 3 → Finset Cell := ![(placed21 5 (5, 3) envelope_15), (placed21 1 (0, 2) envelope_259), envelope_544_i1]
theorem common_sub_544_i0 : commonEnvelope childrenD_544_i0 ⊆ insert (4, 3) required_544_i0 := by decide +kernel
theorem child_required_sub_544_i0 : ∀ j, childrenC_544_i0 j ⊆ insert (4, 3) required_544_i0 := by decide +kernel
theorem child_envelope_sub_544_i0 : ∀ j, childrenD_544_i0 j ⊆ envelope_544_i0 := by decide +kernel
theorem pivot_mem_544_i0 : (4, 3) ∈ envelope_544_i0 := by decide +kernel
theorem children_work_544_i0 : ∀ j, Template HasSnaky 4 (childrenC_544_i0 j) (childrenD_544_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_259 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_544_i1.mono (by decide +kernel)
theorem row_works_544_i0 : Template HasSnaky 5 required_544_i0 envelope_544_i0 := by
  refine compose HasSnaky 4 childrenC_544_i0 childrenD_544_i0 children_work_544_i0 (4, 3)
    required_544_i0 envelope_544_i0 pivot_mem_544_i0 child_required_sub_544_i0 child_envelope_sub_544_i0 ?_
  intro b hb
  exact common_sub_544_i0 (mem_commonEnvelope childrenD_544_i0 b hb)
def required_544 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_544 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_544 : Fin 2 → Finset Cell := ![(placed21 4 (2, 5) required_23), required_544_i0]
def childrenD_544 : Fin 2 → Finset Cell := ![(placed21 4 (2, 5) envelope_23), envelope_544_i0]
theorem common_sub_544 : commonEnvelope childrenD_544 ⊆ insert (3, 4) required_544 := by decide +kernel
theorem child_required_sub_544 : ∀ j, childrenC_544 j ⊆ insert (3, 4) required_544 := by decide +kernel
theorem child_envelope_sub_544 : ∀ j, childrenD_544 j ⊆ envelope_544 := by decide +kernel
theorem pivot_mem_544 : (3, 4) ∈ envelope_544 := by decide +kernel
theorem children_work_544 : ∀ j, Template HasSnaky 5 (childrenC_544 j) (childrenD_544 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_23 4 (2, 5)).mono (by decide +kernel)
  · exact row_works_544_i0.mono (by decide +kernel)
theorem row_works_544 : Template HasSnaky 6 required_544 envelope_544 := by
  refine compose HasSnaky 5 childrenC_544 childrenD_544 children_work_544 (3, 4)
    required_544 envelope_544 pivot_mem_544 child_required_sub_544 child_envelope_sub_544 ?_
  intro b hb
  exact common_sub_544 (mem_commonEnvelope childrenD_544 b hb)
def required_600_i0 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_600_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_600_i0 : Fin 2 → Finset Cell := ![(placed21 0 (2, 2) required_20), (placed21 3 (0, 5) required_55)]
def childrenD_600_i0 : Fin 2 → Finset Cell := ![(placed21 0 (2, 2) envelope_20), (placed21 3 (0, 5) envelope_55)]
theorem common_sub_600_i0 : commonEnvelope childrenD_600_i0 ⊆ insert (3, 5) required_600_i0 := by decide +kernel
theorem child_required_sub_600_i0 : ∀ j, childrenC_600_i0 j ⊆ insert (3, 5) required_600_i0 := by decide +kernel
theorem child_envelope_sub_600_i0 : ∀ j, childrenD_600_i0 j ⊆ envelope_600_i0 := by decide +kernel
theorem pivot_mem_600_i0 : (3, 5) ∈ envelope_600_i0 := by decide +kernel
theorem children_work_600_i0 : ∀ j, Template HasSnaky 4 (childrenC_600_i0 j) (childrenD_600_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_55 3 (0, 5)).mono (by decide +kernel)
theorem row_works_600_i0 : Template HasSnaky 5 required_600_i0 envelope_600_i0 := by
  refine compose HasSnaky 4 childrenC_600_i0 childrenD_600_i0 children_work_600_i0 (3, 5)
    required_600_i0 envelope_600_i0 pivot_mem_600_i0 child_required_sub_600_i0 child_envelope_sub_600_i0 ?_
  intro b hb
  exact common_sub_600_i0 (mem_commonEnvelope childrenD_600_i0 b hb)
def required_600 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_600 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_600 : Fin 2 → Finset Cell := ![(placed21 6 (3, 5) required_23), required_600_i0]
def childrenD_600 : Fin 2 → Finset Cell := ![(placed21 6 (3, 5) envelope_23), envelope_600_i0]
theorem common_sub_600 : commonEnvelope childrenD_600 ⊆ insert (3, 2) required_600 := by decide +kernel
theorem child_required_sub_600 : ∀ j, childrenC_600 j ⊆ insert (3, 2) required_600 := by decide +kernel
theorem child_envelope_sub_600 : ∀ j, childrenD_600 j ⊆ envelope_600 := by decide +kernel
theorem pivot_mem_600 : (3, 2) ∈ envelope_600 := by decide +kernel
theorem children_work_600 : ∀ j, Template HasSnaky 5 (childrenC_600 j) (childrenD_600 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_23 6 (3, 5)).mono (by decide +kernel)
  · exact row_works_600_i0.mono (by decide +kernel)
theorem row_works_600 : Template HasSnaky 6 required_600 envelope_600 := by
  refine compose HasSnaky 5 childrenC_600 childrenD_600 children_work_600 (3, 2)
    required_600 envelope_600 pivot_mem_600 child_required_sub_600 child_envelope_sub_600 ?_
  intro b hb
  exact common_sub_600 (mem_commonEnvelope childrenD_600 b hb)
def required_606_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_606_i0 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_606_i0 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) required_53), (placed21 2 (4, 1) required_240)]
def childrenD_606_i0 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) envelope_53), (placed21 2 (4, 1) envelope_240)]
theorem common_sub_606_i0 : commonEnvelope childrenD_606_i0 ⊆ insert (3, 4) required_606_i0 := by decide +kernel
theorem child_required_sub_606_i0 : ∀ j, childrenC_606_i0 j ⊆ insert (3, 4) required_606_i0 := by decide +kernel
theorem child_envelope_sub_606_i0 : ∀ j, childrenD_606_i0 j ⊆ envelope_606_i0 := by decide +kernel
theorem pivot_mem_606_i0 : (3, 4) ∈ envelope_606_i0 := by decide +kernel
theorem children_work_606_i0 : ∀ j, Template HasSnaky 4 (childrenC_606_i0 j) (childrenD_606_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_240 2 (4, 1)).mono (by decide +kernel)
theorem row_works_606_i0 : Template HasSnaky 5 required_606_i0 envelope_606_i0 := by
  refine compose HasSnaky 4 childrenC_606_i0 childrenD_606_i0 children_work_606_i0 (3, 4)
    required_606_i0 envelope_606_i0 pivot_mem_606_i0 child_required_sub_606_i0 child_envelope_sub_606_i0 ?_
  intro b hb
  exact common_sub_606_i0 (mem_commonEnvelope childrenD_606_i0 b hb)
def required_606 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_606 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_606 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_28), (placed21 0 (0, 1) required_168), required_606_i0]
def childrenD_606 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_28), (placed21 0 (0, 1) envelope_168), envelope_606_i0]
theorem common_sub_606 : commonEnvelope childrenD_606 ⊆ insert (3, 3) required_606 := by decide +kernel
theorem child_required_sub_606 : ∀ j, childrenC_606 j ⊆ insert (3, 3) required_606 := by decide +kernel
theorem child_envelope_sub_606 : ∀ j, childrenD_606 j ⊆ envelope_606 := by decide +kernel
theorem pivot_mem_606 : (3, 3) ∈ envelope_606 := by decide +kernel
theorem children_work_606 : ∀ j, Template HasSnaky 5 (childrenC_606 j) (childrenD_606 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_168 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_606_i0.mono (by decide +kernel)
theorem row_works_606 : Template HasSnaky 6 required_606 envelope_606 := by
  refine compose HasSnaky 5 childrenC_606 childrenD_606 children_work_606 (3, 3)
    required_606 envelope_606 pivot_mem_606 child_required_sub_606 child_envelope_sub_606 ?_
  intro b hb
  exact common_sub_606 (mem_commonEnvelope childrenD_606 b hb)
def required_609_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_609_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_609_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 3 (0, 2) required_48)]
def childrenD_609_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 3 (0, 2) envelope_48)]
theorem common_sub_609_i0 : commonEnvelope childrenD_609_i0 ⊆ insert (2, 1) required_609_i0 := by decide +kernel
theorem child_required_sub_609_i0 : ∀ j, childrenC_609_i0 j ⊆ insert (2, 1) required_609_i0 := by decide +kernel
theorem child_envelope_sub_609_i0 : ∀ j, childrenD_609_i0 j ⊆ envelope_609_i0 := by decide +kernel
theorem pivot_mem_609_i0 : (2, 1) ∈ envelope_609_i0 := by decide +kernel
theorem children_work_609_i0 : ∀ j, Template HasSnaky 4 (childrenC_609_i0 j) (childrenD_609_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_48 3 (0, 2)).mono (by decide +kernel)
theorem row_works_609_i0 : Template HasSnaky 5 required_609_i0 envelope_609_i0 := by
  refine compose HasSnaky 4 childrenC_609_i0 childrenD_609_i0 children_work_609_i0 (2, 1)
    required_609_i0 envelope_609_i0 pivot_mem_609_i0 child_required_sub_609_i0 child_envelope_sub_609_i0 ?_
  intro b hb
  exact common_sub_609_i0 (mem_commonEnvelope childrenD_609_i0 b hb)
def required_609_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (3, 1), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_609_i1 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_609_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_25), (placed21 0 (3, 0) required_54)]
def childrenD_609_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_25), (placed21 0 (3, 0) envelope_54)]
theorem common_sub_609_i1 : commonEnvelope childrenD_609_i1 ⊆ insert (3, 3) required_609_i1 := by decide +kernel
theorem child_required_sub_609_i1 : ∀ j, childrenC_609_i1 j ⊆ insert (3, 3) required_609_i1 := by decide +kernel
theorem child_envelope_sub_609_i1 : ∀ j, childrenD_609_i1 j ⊆ envelope_609_i1 := by decide +kernel
theorem pivot_mem_609_i1 : (3, 3) ∈ envelope_609_i1 := by decide +kernel
theorem children_work_609_i1 : ∀ j, Template HasSnaky 3 (childrenC_609_i1 j) (childrenD_609_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_54 0 (3, 0)).mono (by decide +kernel)
theorem row_works_609_i1 : Template HasSnaky 4 required_609_i1 envelope_609_i1 := by
  refine compose HasSnaky 3 childrenC_609_i1 childrenD_609_i1 children_work_609_i1 (3, 3)
    required_609_i1 envelope_609_i1 pivot_mem_609_i1 child_required_sub_609_i1 child_envelope_sub_609_i1 ?_
  intro b hb
  exact common_sub_609_i1 (mem_commonEnvelope childrenD_609_i1 b hb)
def required_609 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_609 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_609 : Fin 2 → Finset Cell := ![required_609_i0, required_609_i1]
def childrenD_609 : Fin 2 → Finset Cell := ![envelope_609_i0, envelope_609_i1]
theorem common_sub_609 : commonEnvelope childrenD_609 ⊆ insert (3, 1) required_609 := by decide +kernel
theorem child_required_sub_609 : ∀ j, childrenC_609 j ⊆ insert (3, 1) required_609 := by decide +kernel
theorem child_envelope_sub_609 : ∀ j, childrenD_609 j ⊆ envelope_609 := by decide +kernel
theorem pivot_mem_609 : (3, 1) ∈ envelope_609 := by decide +kernel
theorem children_work_609 : ∀ j, Template HasSnaky 5 (childrenC_609 j) (childrenD_609 j) := by
  intro j
  fin_cases j
  · exact row_works_609_i0.mono (by decide +kernel)
  · exact row_works_609_i1.mono (by decide +kernel)
theorem row_works_609 : Template HasSnaky 6 required_609 envelope_609 := by
  refine compose HasSnaky 5 childrenC_609 childrenD_609 children_work_609 (3, 1)
    required_609 envelope_609 pivot_mem_609 child_required_sub_609 child_envelope_sub_609 ?_
  intro b hb
  exact common_sub_609 (mem_commonEnvelope childrenD_609 b hb)
def required_611_i0 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_611_i0 : Finset Cell := ⟨(([(1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_611_i0 : Fin 3 → Finset Cell := ![(placed21 4 (2, 7) required_7), (placed21 0 (1, 3) required_17), (placed21 3 (1, 6) required_93)]
def childrenD_611_i0 : Fin 3 → Finset Cell := ![(placed21 4 (2, 7) envelope_7), (placed21 0 (1, 3) envelope_17), (placed21 3 (1, 6) envelope_93)]
theorem common_sub_611_i0 : commonEnvelope childrenD_611_i0 ⊆ insert (2, 3) required_611_i0 := by decide +kernel
theorem child_required_sub_611_i0 : ∀ j, childrenC_611_i0 j ⊆ insert (2, 3) required_611_i0 := by decide +kernel
theorem child_envelope_sub_611_i0 : ∀ j, childrenD_611_i0 j ⊆ envelope_611_i0 := by decide +kernel
theorem pivot_mem_611_i0 : (2, 3) ∈ envelope_611_i0 := by decide +kernel
theorem children_work_611_i0 : ∀ j, Template HasSnaky 4 (childrenC_611_i0 j) (childrenD_611_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_93 3 (1, 6)).mono (by decide +kernel)
theorem row_works_611_i0 : Template HasSnaky 5 required_611_i0 envelope_611_i0 := by
  refine compose HasSnaky 4 childrenC_611_i0 childrenD_611_i0 children_work_611_i0 (2, 3)
    required_611_i0 envelope_611_i0 pivot_mem_611_i0 child_required_sub_611_i0 child_envelope_sub_611_i0 ?_
  intro b hb
  exact common_sub_611_i0 (mem_commonEnvelope childrenD_611_i0 b hb)
def required_611 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_611 : Finset Cell := ⟨(([(0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_611 : Fin 3 → Finset Cell := ![(placed21 2 (2, 3) required_27), (placed21 3 (0, 7) required_47), required_611_i0]
def childrenD_611 : Fin 3 → Finset Cell := ![(placed21 2 (2, 3) envelope_27), (placed21 3 (0, 7) envelope_47), envelope_611_i0]
theorem common_sub_611 : commonEnvelope childrenD_611 ⊆ insert (2, 5) required_611 := by decide +kernel
theorem child_required_sub_611 : ∀ j, childrenC_611 j ⊆ insert (2, 5) required_611 := by decide +kernel
theorem child_envelope_sub_611 : ∀ j, childrenD_611 j ⊆ envelope_611 := by decide +kernel
theorem pivot_mem_611 : (2, 5) ∈ envelope_611 := by decide +kernel
theorem children_work_611 : ∀ j, Template HasSnaky 5 (childrenC_611 j) (childrenD_611 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_27 2 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (0, 7)).mono (by decide +kernel)
  · exact row_works_611_i0.mono (by decide +kernel)
theorem row_works_611 : Template HasSnaky 6 required_611 envelope_611 := by
  refine compose HasSnaky 5 childrenC_611 childrenD_611 children_work_611 (2, 5)
    required_611 envelope_611 pivot_mem_611 child_required_sub_611 child_envelope_sub_611 ?_
  intro b hb
  exact common_sub_611 (mem_commonEnvelope childrenD_611 b hb)
def required_641_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_641_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_641_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) required_14), (placed21 1 (0, 3) required_44), (placed21 2 (4, 1) required_60)]
def childrenD_641_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) envelope_14), (placed21 1 (0, 3) envelope_44), (placed21 2 (4, 1) envelope_60)]
theorem common_sub_641_i0 : commonEnvelope childrenD_641_i0 ⊆ insert (3, 4) required_641_i0 := by decide +kernel
theorem child_required_sub_641_i0 : ∀ j, childrenC_641_i0 j ⊆ insert (3, 4) required_641_i0 := by decide +kernel
theorem child_envelope_sub_641_i0 : ∀ j, childrenD_641_i0 j ⊆ envelope_641_i0 := by decide +kernel
theorem pivot_mem_641_i0 : (3, 4) ∈ envelope_641_i0 := by decide +kernel
theorem children_work_641_i0 : ∀ j, Template HasSnaky 4 (childrenC_641_i0 j) (childrenD_641_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_60 2 (4, 1)).mono (by decide +kernel)
theorem row_works_641_i0 : Template HasSnaky 5 required_641_i0 envelope_641_i0 := by
  refine compose HasSnaky 4 childrenC_641_i0 childrenD_641_i0 children_work_641_i0 (3, 4)
    required_641_i0 envelope_641_i0 pivot_mem_641_i0 child_required_sub_641_i0 child_envelope_sub_641_i0 ?_
  intro b hb
  exact common_sub_641_i0 (mem_commonEnvelope childrenD_641_i0 b hb)
def required_641 : Finset Cell := ⟨(([(1, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_641 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_641 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_52), (placed21 0 (1, 1) required_144), required_641_i0]
def childrenD_641 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_52), (placed21 0 (1, 1) envelope_144), envelope_641_i0]
theorem common_sub_641 : commonEnvelope childrenD_641 ⊆ insert (2, 3) required_641 := by decide +kernel
theorem child_required_sub_641 : ∀ j, childrenC_641 j ⊆ insert (2, 3) required_641 := by decide +kernel
theorem child_envelope_sub_641 : ∀ j, childrenD_641 j ⊆ envelope_641 := by decide +kernel
theorem pivot_mem_641 : (2, 3) ∈ envelope_641 := by decide +kernel
theorem children_work_641 : ∀ j, Template HasSnaky 5 (childrenC_641 j) (childrenD_641 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_144 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_641_i0.mono (by decide +kernel)
theorem row_works_641 : Template HasSnaky 6 required_641 envelope_641 := by
  refine compose HasSnaky 5 childrenC_641 childrenD_641 children_work_641 (2, 3)
    required_641 envelope_641 pivot_mem_641 child_required_sub_641 child_envelope_sub_641 ?_
  intro b hb
  exact common_sub_641 (mem_commonEnvelope childrenD_641 b hb)
def required_714_i0 : Finset Cell := ⟨(([(2, 4), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_714_i0 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 7), (4, 8), (4, 9), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_714_i0 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) required_41), (placed21 3 (0, 6) required_55)]
def childrenD_714_i0 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) envelope_41), (placed21 3 (0, 6) envelope_55)]
theorem common_sub_714_i0 : commonEnvelope childrenD_714_i0 ⊆ insert (3, 6) required_714_i0 := by decide +kernel
theorem child_required_sub_714_i0 : ∀ j, childrenC_714_i0 j ⊆ insert (3, 6) required_714_i0 := by decide +kernel
theorem child_envelope_sub_714_i0 : ∀ j, childrenD_714_i0 j ⊆ envelope_714_i0 := by decide +kernel
theorem pivot_mem_714_i0 : (3, 6) ∈ envelope_714_i0 := by decide +kernel
theorem children_work_714_i0 : ∀ j, Template HasSnaky 4 (childrenC_714_i0 j) (childrenD_714_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_41 0 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_55 3 (0, 6)).mono (by decide +kernel)
theorem row_works_714_i0 : Template HasSnaky 5 required_714_i0 envelope_714_i0 := by
  refine compose HasSnaky 4 childrenC_714_i0 childrenD_714_i0 children_work_714_i0 (3, 6)
    required_714_i0 envelope_714_i0 pivot_mem_714_i0 child_required_sub_714_i0 child_envelope_sub_714_i0 ?_
  intro b hb
  exact common_sub_714_i0 (mem_commonEnvelope childrenD_714_i0 b hb)
def required_714 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_714 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 7), (4, 8), (4, 9), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_714 : Fin 3 → Finset Cell := ![(placed21 2 (3, 2) required_15), (placed21 3 (0, 6) required_88), required_714_i0]
def childrenD_714 : Fin 3 → Finset Cell := ![(placed21 2 (3, 2) envelope_15), (placed21 3 (0, 6) envelope_88), envelope_714_i0]
theorem common_sub_714 : commonEnvelope childrenD_714 ⊆ insert (3, 3) required_714 := by decide +kernel
theorem child_required_sub_714 : ∀ j, childrenC_714 j ⊆ insert (3, 3) required_714 := by decide +kernel
theorem child_envelope_sub_714 : ∀ j, childrenD_714 j ⊆ envelope_714 := by decide +kernel
theorem pivot_mem_714 : (3, 3) ∈ envelope_714 := by decide +kernel
theorem children_work_714 : ∀ j, Template HasSnaky 5 (childrenC_714 j) (childrenD_714 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_88 3 (0, 6)).mono (by decide +kernel)
  · exact row_works_714_i0.mono (by decide +kernel)
theorem row_works_714 : Template HasSnaky 6 required_714 envelope_714 := by
  refine compose HasSnaky 5 childrenC_714 childrenD_714 children_work_714 (3, 3)
    required_714 envelope_714 pivot_mem_714 child_required_sub_714 child_envelope_sub_714 ?_
  intro b hb
  exact common_sub_714 (mem_commonEnvelope childrenD_714 b hb)
def height_521_i1 : ℕ := 4
def childrenH_521_i1 : Fin 2 → ℕ := ![height_45, height_45]
theorem height_exact_521_i1 : height_521_i1 = 1 + Finset.univ.sup childrenH_521_i1 := by decide +kernel
theorem required_origin_521_i1 : ∀ x ∈ required_521_i1,
    (∃ j, x ∈ childrenC_521_i1 j) ∨ ∀ j, x ∈ childrenD_521_i1 j := by decide +kernel
theorem required_exact_521_i1 : required_521_i1 =
    ((Finset.univ.biUnion childrenC_521_i1) ∪ commonEnvelope childrenD_521_i1).erase (2, 3) := by
  exact required_eq_combination childrenC_521_i1 childrenD_521_i1 (2, 3) required_521_i1
    (by decide +kernel) child_required_sub_521_i1 common_sub_521_i1 required_origin_521_i1
theorem envelope_origin_521_i1 : ∀ x ∈ envelope_521_i1,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_521_i1 j := by decide +kernel
theorem envelope_exact_521_i1 : envelope_521_i1 =
    insert (2, 3) (Finset.univ.biUnion childrenD_521_i1) := by
  exact envelope_eq_combination childrenD_521_i1 (2, 3) envelope_521_i1
    pivot_mem_521_i1 child_envelope_sub_521_i1 envelope_origin_521_i1
def checked_521_i1 : CheckedCard where
  required := required_521_i1
  envelope := envelope_521_i1
  height := height_521_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_521_i1
def height_521_i0 : ℕ := 5
def childrenH_521_i0 : Fin 2 → ℕ := ![height_5, height_521_i1]
theorem height_exact_521_i0 : height_521_i0 = 1 + Finset.univ.sup childrenH_521_i0 := by decide +kernel
theorem required_origin_521_i0 : ∀ x ∈ required_521_i0,
    (∃ j, x ∈ childrenC_521_i0 j) ∨ ∀ j, x ∈ childrenD_521_i0 j := by decide +kernel
theorem required_exact_521_i0 : required_521_i0 =
    ((Finset.univ.biUnion childrenC_521_i0) ∪ commonEnvelope childrenD_521_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_521_i0 childrenD_521_i0 (2, 4) required_521_i0
    (by decide +kernel) child_required_sub_521_i0 common_sub_521_i0 required_origin_521_i0
theorem envelope_origin_521_i0 : ∀ x ∈ envelope_521_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_521_i0 j := by decide +kernel
theorem envelope_exact_521_i0 : envelope_521_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_521_i0) := by
  exact envelope_eq_combination childrenD_521_i0 (2, 4) envelope_521_i0
    pivot_mem_521_i0 child_envelope_sub_521_i0 envelope_origin_521_i0
def checked_521_i0 : CheckedCard where
  required := required_521_i0
  envelope := envelope_521_i0
  height := height_521_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_521_i0
def height_521 : ℕ := 6
def childrenH_521 : Fin 2 → ℕ := ![height_5, height_521_i0]
theorem height_exact_521 : height_521 = 1 + Finset.univ.sup childrenH_521 := by decide +kernel
theorem required_origin_521 : ∀ x ∈ required_521,
    (∃ j, x ∈ childrenC_521 j) ∨ ∀ j, x ∈ childrenD_521 j := by decide +kernel
theorem required_exact_521 : required_521 =
    ((Finset.univ.biUnion childrenC_521) ∪ commonEnvelope childrenD_521).erase (2, 1) := by
  exact required_eq_combination childrenC_521 childrenD_521 (2, 1) required_521
    (by decide +kernel) child_required_sub_521 common_sub_521 required_origin_521
theorem envelope_origin_521 : ∀ x ∈ envelope_521,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_521 j := by decide +kernel
theorem envelope_exact_521 : envelope_521 =
    insert (2, 1) (Finset.univ.biUnion childrenD_521) := by
  exact envelope_eq_combination childrenD_521 (2, 1) envelope_521
    pivot_mem_521 child_envelope_sub_521 envelope_origin_521
def checked_521 : CheckedCard where
  required := required_521
  envelope := envelope_521
  height := height_521
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_521
def height_525_i1 : ℕ := 4
def childrenH_525_i1 : Fin 3 → ℕ := ![height_21, height_37, height_78]
theorem height_exact_525_i1 : height_525_i1 = 1 + Finset.univ.sup childrenH_525_i1 := by decide +kernel
theorem required_origin_525_i1 : ∀ x ∈ required_525_i1,
    (∃ j, x ∈ childrenC_525_i1 j) ∨ ∀ j, x ∈ childrenD_525_i1 j := by decide +kernel
theorem required_exact_525_i1 : required_525_i1 =
    ((Finset.univ.biUnion childrenC_525_i1) ∪ commonEnvelope childrenD_525_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_525_i1 childrenD_525_i1 (3, 3) required_525_i1
    (by decide +kernel) child_required_sub_525_i1 common_sub_525_i1 required_origin_525_i1
theorem envelope_origin_525_i1 : ∀ x ∈ envelope_525_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_525_i1 j := by decide +kernel
theorem envelope_exact_525_i1 : envelope_525_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_525_i1) := by
  exact envelope_eq_combination childrenD_525_i1 (3, 3) envelope_525_i1
    pivot_mem_525_i1 child_envelope_sub_525_i1 envelope_origin_525_i1
def checked_525_i1 : CheckedCard where
  required := required_525_i1
  envelope := envelope_525_i1
  height := height_525_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_525_i1
def height_525_i0 : ℕ := 5
def childrenH_525_i0 : Fin 2 → ℕ := ![height_5, height_525_i1]
theorem height_exact_525_i0 : height_525_i0 = 1 + Finset.univ.sup childrenH_525_i0 := by decide +kernel
theorem required_origin_525_i0 : ∀ x ∈ required_525_i0,
    (∃ j, x ∈ childrenC_525_i0 j) ∨ ∀ j, x ∈ childrenD_525_i0 j := by decide +kernel
theorem required_exact_525_i0 : required_525_i0 =
    ((Finset.univ.biUnion childrenC_525_i0) ∪ commonEnvelope childrenD_525_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_525_i0 childrenD_525_i0 (3, 2) required_525_i0
    (by decide +kernel) child_required_sub_525_i0 common_sub_525_i0 required_origin_525_i0
theorem envelope_origin_525_i0 : ∀ x ∈ envelope_525_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_525_i0 j := by decide +kernel
theorem envelope_exact_525_i0 : envelope_525_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_525_i0) := by
  exact envelope_eq_combination childrenD_525_i0 (3, 2) envelope_525_i0
    pivot_mem_525_i0 child_envelope_sub_525_i0 envelope_origin_525_i0
def checked_525_i0 : CheckedCard where
  required := required_525_i0
  envelope := envelope_525_i0
  height := height_525_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_525_i0
def height_525 : ℕ := 6
def childrenH_525 : Fin 2 → ℕ := ![height_5, height_525_i0]
theorem height_exact_525 : height_525 = 1 + Finset.univ.sup childrenH_525 := by decide +kernel
theorem required_origin_525 : ∀ x ∈ required_525,
    (∃ j, x ∈ childrenC_525 j) ∨ ∀ j, x ∈ childrenD_525 j := by decide +kernel
theorem required_exact_525 : required_525 =
    ((Finset.univ.biUnion childrenC_525) ∪ commonEnvelope childrenD_525).erase (3, 0) := by
  exact required_eq_combination childrenC_525 childrenD_525 (3, 0) required_525
    (by decide +kernel) child_required_sub_525 common_sub_525 required_origin_525
theorem envelope_origin_525 : ∀ x ∈ envelope_525,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_525 j := by decide +kernel
theorem envelope_exact_525 : envelope_525 =
    insert (3, 0) (Finset.univ.biUnion childrenD_525) := by
  exact envelope_eq_combination childrenD_525 (3, 0) envelope_525
    pivot_mem_525 child_envelope_sub_525 envelope_origin_525
def checked_525 : CheckedCard where
  required := required_525
  envelope := envelope_525
  height := height_525
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_525
def height_544_i1 : ℕ := 4
def childrenH_544_i1 : Fin 2 → ℕ := ![height_0, height_62]
theorem height_exact_544_i1 : height_544_i1 = 1 + Finset.univ.sup childrenH_544_i1 := by decide +kernel
theorem required_origin_544_i1 : ∀ x ∈ required_544_i1,
    (∃ j, x ∈ childrenC_544_i1 j) ∨ ∀ j, x ∈ childrenD_544_i1 j := by decide +kernel
theorem required_exact_544_i1 : required_544_i1 =
    ((Finset.univ.biUnion childrenC_544_i1) ∪ commonEnvelope childrenD_544_i1).erase (5, 3) := by
  exact required_eq_combination childrenC_544_i1 childrenD_544_i1 (5, 3) required_544_i1
    (by decide +kernel) child_required_sub_544_i1 common_sub_544_i1 required_origin_544_i1
theorem envelope_origin_544_i1 : ∀ x ∈ envelope_544_i1,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_544_i1 j := by decide +kernel
theorem envelope_exact_544_i1 : envelope_544_i1 =
    insert (5, 3) (Finset.univ.biUnion childrenD_544_i1) := by
  exact envelope_eq_combination childrenD_544_i1 (5, 3) envelope_544_i1
    pivot_mem_544_i1 child_envelope_sub_544_i1 envelope_origin_544_i1
def checked_544_i1 : CheckedCard where
  required := required_544_i1
  envelope := envelope_544_i1
  height := height_544_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_544_i1
def height_544_i0 : ℕ := 5
def childrenH_544_i0 : Fin 3 → ℕ := ![height_15, height_259, height_544_i1]
theorem height_exact_544_i0 : height_544_i0 = 1 + Finset.univ.sup childrenH_544_i0 := by decide +kernel
theorem required_origin_544_i0 : ∀ x ∈ required_544_i0,
    (∃ j, x ∈ childrenC_544_i0 j) ∨ ∀ j, x ∈ childrenD_544_i0 j := by decide +kernel
theorem required_exact_544_i0 : required_544_i0 =
    ((Finset.univ.biUnion childrenC_544_i0) ∪ commonEnvelope childrenD_544_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_544_i0 childrenD_544_i0 (4, 3) required_544_i0
    (by decide +kernel) child_required_sub_544_i0 common_sub_544_i0 required_origin_544_i0
theorem envelope_origin_544_i0 : ∀ x ∈ envelope_544_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_544_i0 j := by decide +kernel
theorem envelope_exact_544_i0 : envelope_544_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_544_i0) := by
  exact envelope_eq_combination childrenD_544_i0 (4, 3) envelope_544_i0
    pivot_mem_544_i0 child_envelope_sub_544_i0 envelope_origin_544_i0
def checked_544_i0 : CheckedCard where
  required := required_544_i0
  envelope := envelope_544_i0
  height := height_544_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_544_i0
def height_544 : ℕ := 6
def childrenH_544 : Fin 2 → ℕ := ![height_23, height_544_i0]
theorem height_exact_544 : height_544 = 1 + Finset.univ.sup childrenH_544 := by decide +kernel
theorem required_origin_544 : ∀ x ∈ required_544,
    (∃ j, x ∈ childrenC_544 j) ∨ ∀ j, x ∈ childrenD_544 j := by decide +kernel
theorem required_exact_544 : required_544 =
    ((Finset.univ.biUnion childrenC_544) ∪ commonEnvelope childrenD_544).erase (3, 4) := by
  exact required_eq_combination childrenC_544 childrenD_544 (3, 4) required_544
    (by decide +kernel) child_required_sub_544 common_sub_544 required_origin_544
theorem envelope_origin_544 : ∀ x ∈ envelope_544,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_544 j := by decide +kernel
theorem envelope_exact_544 : envelope_544 =
    insert (3, 4) (Finset.univ.biUnion childrenD_544) := by
  exact envelope_eq_combination childrenD_544 (3, 4) envelope_544
    pivot_mem_544 child_envelope_sub_544 envelope_origin_544
def checked_544 : CheckedCard where
  required := required_544
  envelope := envelope_544
  height := height_544
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_544
def height_600_i0 : ℕ := 5
def childrenH_600_i0 : Fin 2 → ℕ := ![height_20, height_55]
theorem height_exact_600_i0 : height_600_i0 = 1 + Finset.univ.sup childrenH_600_i0 := by decide +kernel
theorem required_origin_600_i0 : ∀ x ∈ required_600_i0,
    (∃ j, x ∈ childrenC_600_i0 j) ∨ ∀ j, x ∈ childrenD_600_i0 j := by decide +kernel
theorem required_exact_600_i0 : required_600_i0 =
    ((Finset.univ.biUnion childrenC_600_i0) ∪ commonEnvelope childrenD_600_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_600_i0 childrenD_600_i0 (3, 5) required_600_i0
    (by decide +kernel) child_required_sub_600_i0 common_sub_600_i0 required_origin_600_i0
theorem envelope_origin_600_i0 : ∀ x ∈ envelope_600_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_600_i0 j := by decide +kernel
theorem envelope_exact_600_i0 : envelope_600_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_600_i0) := by
  exact envelope_eq_combination childrenD_600_i0 (3, 5) envelope_600_i0
    pivot_mem_600_i0 child_envelope_sub_600_i0 envelope_origin_600_i0
def checked_600_i0 : CheckedCard where
  required := required_600_i0
  envelope := envelope_600_i0
  height := height_600_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_600_i0
def height_600 : ℕ := 6
def childrenH_600 : Fin 2 → ℕ := ![height_23, height_600_i0]
theorem height_exact_600 : height_600 = 1 + Finset.univ.sup childrenH_600 := by decide +kernel
theorem required_origin_600 : ∀ x ∈ required_600,
    (∃ j, x ∈ childrenC_600 j) ∨ ∀ j, x ∈ childrenD_600 j := by decide +kernel
theorem required_exact_600 : required_600 =
    ((Finset.univ.biUnion childrenC_600) ∪ commonEnvelope childrenD_600).erase (3, 2) := by
  exact required_eq_combination childrenC_600 childrenD_600 (3, 2) required_600
    (by decide +kernel) child_required_sub_600 common_sub_600 required_origin_600
theorem envelope_origin_600 : ∀ x ∈ envelope_600,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_600 j := by decide +kernel
theorem envelope_exact_600 : envelope_600 =
    insert (3, 2) (Finset.univ.biUnion childrenD_600) := by
  exact envelope_eq_combination childrenD_600 (3, 2) envelope_600
    pivot_mem_600 child_envelope_sub_600 envelope_origin_600
def checked_600 : CheckedCard where
  required := required_600
  envelope := envelope_600
  height := height_600
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_600
def height_606_i0 : ℕ := 5
def childrenH_606_i0 : Fin 2 → ℕ := ![height_53, height_240]
theorem height_exact_606_i0 : height_606_i0 = 1 + Finset.univ.sup childrenH_606_i0 := by decide +kernel
theorem required_origin_606_i0 : ∀ x ∈ required_606_i0,
    (∃ j, x ∈ childrenC_606_i0 j) ∨ ∀ j, x ∈ childrenD_606_i0 j := by decide +kernel
theorem required_exact_606_i0 : required_606_i0 =
    ((Finset.univ.biUnion childrenC_606_i0) ∪ commonEnvelope childrenD_606_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_606_i0 childrenD_606_i0 (3, 4) required_606_i0
    (by decide +kernel) child_required_sub_606_i0 common_sub_606_i0 required_origin_606_i0
theorem envelope_origin_606_i0 : ∀ x ∈ envelope_606_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_606_i0 j := by decide +kernel
theorem envelope_exact_606_i0 : envelope_606_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_606_i0) := by
  exact envelope_eq_combination childrenD_606_i0 (3, 4) envelope_606_i0
    pivot_mem_606_i0 child_envelope_sub_606_i0 envelope_origin_606_i0
def checked_606_i0 : CheckedCard where
  required := required_606_i0
  envelope := envelope_606_i0
  height := height_606_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_606_i0
def height_606 : ℕ := 6
def childrenH_606 : Fin 3 → ℕ := ![height_28, height_168, height_606_i0]
theorem height_exact_606 : height_606 = 1 + Finset.univ.sup childrenH_606 := by decide +kernel
theorem required_origin_606 : ∀ x ∈ required_606,
    (∃ j, x ∈ childrenC_606 j) ∨ ∀ j, x ∈ childrenD_606 j := by decide +kernel
theorem required_exact_606 : required_606 =
    ((Finset.univ.biUnion childrenC_606) ∪ commonEnvelope childrenD_606).erase (3, 3) := by
  exact required_eq_combination childrenC_606 childrenD_606 (3, 3) required_606
    (by decide +kernel) child_required_sub_606 common_sub_606 required_origin_606
theorem envelope_origin_606 : ∀ x ∈ envelope_606,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_606 j := by decide +kernel
theorem envelope_exact_606 : envelope_606 =
    insert (3, 3) (Finset.univ.biUnion childrenD_606) := by
  exact envelope_eq_combination childrenD_606 (3, 3) envelope_606
    pivot_mem_606 child_envelope_sub_606 envelope_origin_606
def checked_606 : CheckedCard where
  required := required_606
  envelope := envelope_606
  height := height_606
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_606
def height_609_i0 : ℕ := 5
def childrenH_609_i0 : Fin 2 → ℕ := ![height_5, height_48]
theorem height_exact_609_i0 : height_609_i0 = 1 + Finset.univ.sup childrenH_609_i0 := by decide +kernel
theorem required_origin_609_i0 : ∀ x ∈ required_609_i0,
    (∃ j, x ∈ childrenC_609_i0 j) ∨ ∀ j, x ∈ childrenD_609_i0 j := by decide +kernel
theorem required_exact_609_i0 : required_609_i0 =
    ((Finset.univ.biUnion childrenC_609_i0) ∪ commonEnvelope childrenD_609_i0).erase (2, 1) := by
  exact required_eq_combination childrenC_609_i0 childrenD_609_i0 (2, 1) required_609_i0
    (by decide +kernel) child_required_sub_609_i0 common_sub_609_i0 required_origin_609_i0
theorem envelope_origin_609_i0 : ∀ x ∈ envelope_609_i0,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_609_i0 j := by decide +kernel
theorem envelope_exact_609_i0 : envelope_609_i0 =
    insert (2, 1) (Finset.univ.biUnion childrenD_609_i0) := by
  exact envelope_eq_combination childrenD_609_i0 (2, 1) envelope_609_i0
    pivot_mem_609_i0 child_envelope_sub_609_i0 envelope_origin_609_i0
def checked_609_i0 : CheckedCard where
  required := required_609_i0
  envelope := envelope_609_i0
  height := height_609_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_609_i0
def height_609_i1 : ℕ := 4
def childrenH_609_i1 : Fin 2 → ℕ := ![height_25, height_54]
theorem height_exact_609_i1 : height_609_i1 = 1 + Finset.univ.sup childrenH_609_i1 := by decide +kernel
theorem required_origin_609_i1 : ∀ x ∈ required_609_i1,
    (∃ j, x ∈ childrenC_609_i1 j) ∨ ∀ j, x ∈ childrenD_609_i1 j := by decide +kernel
theorem required_exact_609_i1 : required_609_i1 =
    ((Finset.univ.biUnion childrenC_609_i1) ∪ commonEnvelope childrenD_609_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_609_i1 childrenD_609_i1 (3, 3) required_609_i1
    (by decide +kernel) child_required_sub_609_i1 common_sub_609_i1 required_origin_609_i1
theorem envelope_origin_609_i1 : ∀ x ∈ envelope_609_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_609_i1 j := by decide +kernel
theorem envelope_exact_609_i1 : envelope_609_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_609_i1) := by
  exact envelope_eq_combination childrenD_609_i1 (3, 3) envelope_609_i1
    pivot_mem_609_i1 child_envelope_sub_609_i1 envelope_origin_609_i1
def checked_609_i1 : CheckedCard where
  required := required_609_i1
  envelope := envelope_609_i1
  height := height_609_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_609_i1
def height_609 : ℕ := 6
def childrenH_609 : Fin 2 → ℕ := ![height_609_i0, height_609_i1]
theorem height_exact_609 : height_609 = 1 + Finset.univ.sup childrenH_609 := by decide +kernel
theorem required_origin_609 : ∀ x ∈ required_609,
    (∃ j, x ∈ childrenC_609 j) ∨ ∀ j, x ∈ childrenD_609 j := by decide +kernel
theorem required_exact_609 : required_609 =
    ((Finset.univ.biUnion childrenC_609) ∪ commonEnvelope childrenD_609).erase (3, 1) := by
  exact required_eq_combination childrenC_609 childrenD_609 (3, 1) required_609
    (by decide +kernel) child_required_sub_609 common_sub_609 required_origin_609
theorem envelope_origin_609 : ∀ x ∈ envelope_609,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_609 j := by decide +kernel
theorem envelope_exact_609 : envelope_609 =
    insert (3, 1) (Finset.univ.biUnion childrenD_609) := by
  exact envelope_eq_combination childrenD_609 (3, 1) envelope_609
    pivot_mem_609 child_envelope_sub_609 envelope_origin_609
def checked_609 : CheckedCard where
  required := required_609
  envelope := envelope_609
  height := height_609
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_609
def height_611_i0 : ℕ := 5
def childrenH_611_i0 : Fin 3 → ℕ := ![height_7, height_17, height_93]
theorem height_exact_611_i0 : height_611_i0 = 1 + Finset.univ.sup childrenH_611_i0 := by decide +kernel
theorem required_origin_611_i0 : ∀ x ∈ required_611_i0,
    (∃ j, x ∈ childrenC_611_i0 j) ∨ ∀ j, x ∈ childrenD_611_i0 j := by decide +kernel
theorem required_exact_611_i0 : required_611_i0 =
    ((Finset.univ.biUnion childrenC_611_i0) ∪ commonEnvelope childrenD_611_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_611_i0 childrenD_611_i0 (2, 3) required_611_i0
    (by decide +kernel) child_required_sub_611_i0 common_sub_611_i0 required_origin_611_i0
theorem envelope_origin_611_i0 : ∀ x ∈ envelope_611_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_611_i0 j := by decide +kernel
theorem envelope_exact_611_i0 : envelope_611_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_611_i0) := by
  exact envelope_eq_combination childrenD_611_i0 (2, 3) envelope_611_i0
    pivot_mem_611_i0 child_envelope_sub_611_i0 envelope_origin_611_i0
def checked_611_i0 : CheckedCard where
  required := required_611_i0
  envelope := envelope_611_i0
  height := height_611_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_611_i0
def height_611 : ℕ := 6
def childrenH_611 : Fin 3 → ℕ := ![height_27, height_47, height_611_i0]
theorem height_exact_611 : height_611 = 1 + Finset.univ.sup childrenH_611 := by decide +kernel
theorem required_origin_611 : ∀ x ∈ required_611,
    (∃ j, x ∈ childrenC_611 j) ∨ ∀ j, x ∈ childrenD_611 j := by decide +kernel
theorem required_exact_611 : required_611 =
    ((Finset.univ.biUnion childrenC_611) ∪ commonEnvelope childrenD_611).erase (2, 5) := by
  exact required_eq_combination childrenC_611 childrenD_611 (2, 5) required_611
    (by decide +kernel) child_required_sub_611 common_sub_611 required_origin_611
theorem envelope_origin_611 : ∀ x ∈ envelope_611,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_611 j := by decide +kernel
theorem envelope_exact_611 : envelope_611 =
    insert (2, 5) (Finset.univ.biUnion childrenD_611) := by
  exact envelope_eq_combination childrenD_611 (2, 5) envelope_611
    pivot_mem_611 child_envelope_sub_611 envelope_origin_611
def checked_611 : CheckedCard where
  required := required_611
  envelope := envelope_611
  height := height_611
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_611
def height_641_i0 : ℕ := 5
def childrenH_641_i0 : Fin 3 → ℕ := ![height_14, height_44, height_60]
theorem height_exact_641_i0 : height_641_i0 = 1 + Finset.univ.sup childrenH_641_i0 := by decide +kernel
theorem required_origin_641_i0 : ∀ x ∈ required_641_i0,
    (∃ j, x ∈ childrenC_641_i0 j) ∨ ∀ j, x ∈ childrenD_641_i0 j := by decide +kernel
theorem required_exact_641_i0 : required_641_i0 =
    ((Finset.univ.biUnion childrenC_641_i0) ∪ commonEnvelope childrenD_641_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_641_i0 childrenD_641_i0 (3, 4) required_641_i0
    (by decide +kernel) child_required_sub_641_i0 common_sub_641_i0 required_origin_641_i0
theorem envelope_origin_641_i0 : ∀ x ∈ envelope_641_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_641_i0 j := by decide +kernel
theorem envelope_exact_641_i0 : envelope_641_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_641_i0) := by
  exact envelope_eq_combination childrenD_641_i0 (3, 4) envelope_641_i0
    pivot_mem_641_i0 child_envelope_sub_641_i0 envelope_origin_641_i0
def checked_641_i0 : CheckedCard where
  required := required_641_i0
  envelope := envelope_641_i0
  height := height_641_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_641_i0
def height_641 : ℕ := 6
def childrenH_641 : Fin 3 → ℕ := ![height_52, height_144, height_641_i0]
theorem height_exact_641 : height_641 = 1 + Finset.univ.sup childrenH_641 := by decide +kernel
theorem required_origin_641 : ∀ x ∈ required_641,
    (∃ j, x ∈ childrenC_641 j) ∨ ∀ j, x ∈ childrenD_641 j := by decide +kernel
theorem required_exact_641 : required_641 =
    ((Finset.univ.biUnion childrenC_641) ∪ commonEnvelope childrenD_641).erase (2, 3) := by
  exact required_eq_combination childrenC_641 childrenD_641 (2, 3) required_641
    (by decide +kernel) child_required_sub_641 common_sub_641 required_origin_641
theorem envelope_origin_641 : ∀ x ∈ envelope_641,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_641 j := by decide +kernel
theorem envelope_exact_641 : envelope_641 =
    insert (2, 3) (Finset.univ.biUnion childrenD_641) := by
  exact envelope_eq_combination childrenD_641 (2, 3) envelope_641
    pivot_mem_641 child_envelope_sub_641 envelope_origin_641
def checked_641 : CheckedCard where
  required := required_641
  envelope := envelope_641
  height := height_641
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_641
def height_714_i0 : ℕ := 5
def childrenH_714_i0 : Fin 2 → ℕ := ![height_41, height_55]
theorem height_exact_714_i0 : height_714_i0 = 1 + Finset.univ.sup childrenH_714_i0 := by decide +kernel
theorem required_origin_714_i0 : ∀ x ∈ required_714_i0,
    (∃ j, x ∈ childrenC_714_i0 j) ∨ ∀ j, x ∈ childrenD_714_i0 j := by decide +kernel
theorem required_exact_714_i0 : required_714_i0 =
    ((Finset.univ.biUnion childrenC_714_i0) ∪ commonEnvelope childrenD_714_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_714_i0 childrenD_714_i0 (3, 6) required_714_i0
    (by decide +kernel) child_required_sub_714_i0 common_sub_714_i0 required_origin_714_i0
theorem envelope_origin_714_i0 : ∀ x ∈ envelope_714_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_714_i0 j := by decide +kernel
theorem envelope_exact_714_i0 : envelope_714_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_714_i0) := by
  exact envelope_eq_combination childrenD_714_i0 (3, 6) envelope_714_i0
    pivot_mem_714_i0 child_envelope_sub_714_i0 envelope_origin_714_i0
def checked_714_i0 : CheckedCard where
  required := required_714_i0
  envelope := envelope_714_i0
  height := height_714_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_714_i0
def height_714 : ℕ := 6
def childrenH_714 : Fin 3 → ℕ := ![height_15, height_88, height_714_i0]
theorem height_exact_714 : height_714 = 1 + Finset.univ.sup childrenH_714 := by decide +kernel
theorem required_origin_714 : ∀ x ∈ required_714,
    (∃ j, x ∈ childrenC_714 j) ∨ ∀ j, x ∈ childrenD_714 j := by decide +kernel
theorem required_exact_714 : required_714 =
    ((Finset.univ.biUnion childrenC_714) ∪ commonEnvelope childrenD_714).erase (3, 3) := by
  exact required_eq_combination childrenC_714 childrenD_714 (3, 3) required_714
    (by decide +kernel) child_required_sub_714 common_sub_714 required_origin_714
theorem envelope_origin_714 : ∀ x ∈ envelope_714,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_714 j := by decide +kernel
theorem envelope_exact_714 : envelope_714 =
    insert (3, 3) (Finset.univ.biUnion childrenD_714) := by
  exact envelope_eq_combination childrenD_714 (3, 3) envelope_714
    pivot_mem_714 child_envelope_sub_714 envelope_origin_714
def checked_714 : CheckedCard where
  required := required_714
  envelope := envelope_714
  height := height_714
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_714
end SnakyPrototype.Certificate21

end OAI
