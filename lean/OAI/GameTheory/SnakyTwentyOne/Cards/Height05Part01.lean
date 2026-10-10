import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_19 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_19 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_19 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 0 (0, 1) required_18)]
def childrenD_19 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 0 (0, 1) envelope_18)]
theorem common_sub_19 : commonEnvelope childrenD_19 ⊆ insert (0, 1) required_19 := by decide +kernel
theorem child_required_sub_19 : ∀ j, childrenC_19 j ⊆ insert (0, 1) required_19 := by decide +kernel
theorem child_envelope_sub_19 : ∀ j, childrenD_19 j ⊆ envelope_19 := by decide +kernel
theorem pivot_mem_19 : (0, 1) ∈ envelope_19 := by decide +kernel
theorem children_work_19 : ∀ j, Template HasSnaky 4 (childrenC_19 j) (childrenD_19 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_18 0 (0, 1)).mono (by decide +kernel)
theorem row_works_19 : Template HasSnaky 5 required_19 envelope_19 := by
  refine compose HasSnaky 4 childrenC_19 childrenD_19 children_work_19 (0, 1)
    required_19 envelope_19 pivot_mem_19 child_required_sub_19 child_envelope_sub_19 ?_
  intro b hb
  exact common_sub_19 (mem_commonEnvelope childrenD_19 b hb)
def required_47 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_47 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_47 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_7), (placed21 3 (0, 3) required_9), (placed21 0 (1, 0) required_46)]
def childrenD_47 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_7), (placed21 3 (0, 3) envelope_9), (placed21 0 (1, 0) envelope_46)]
theorem common_sub_47 : commonEnvelope childrenD_47 ⊆ insert (4, 2) required_47 := by decide +kernel
theorem child_required_sub_47 : ∀ j, childrenC_47 j ⊆ insert (4, 2) required_47 := by decide +kernel
theorem child_envelope_sub_47 : ∀ j, childrenD_47 j ⊆ envelope_47 := by decide +kernel
theorem pivot_mem_47 : (4, 2) ∈ envelope_47 := by decide +kernel
theorem children_work_47 : ∀ j, Template HasSnaky 4 (childrenC_47 j) (childrenD_47 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_46 0 (1, 0)).mono (by decide +kernel)
theorem row_works_47 : Template HasSnaky 5 required_47 envelope_47 := by
  refine compose HasSnaky 4 childrenC_47 childrenD_47 children_work_47 (4, 2)
    required_47 envelope_47 pivot_mem_47 child_required_sub_47 child_envelope_sub_47 ?_
  intro b hb
  exact common_sub_47 (mem_commonEnvelope childrenD_47 b hb)
def required_59 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_59 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_59 : Fin 3 → Finset Cell := ![(placed21 5 (4, 2) required_28), (placed21 0 (2, 0) required_31), (placed21 0 (0, 1) required_58)]
def childrenD_59 : Fin 3 → Finset Cell := ![(placed21 5 (4, 2) envelope_28), (placed21 0 (2, 0) envelope_31), (placed21 0 (0, 1) envelope_58)]
theorem common_sub_59 : commonEnvelope childrenD_59 ⊆ insert (3, 2) required_59 := by decide +kernel
theorem child_required_sub_59 : ∀ j, childrenC_59 j ⊆ insert (3, 2) required_59 := by decide +kernel
theorem child_envelope_sub_59 : ∀ j, childrenD_59 j ⊆ envelope_59 := by decide +kernel
theorem pivot_mem_59 : (3, 2) ∈ envelope_59 := by decide +kernel
theorem children_work_59 : ∀ j, Template HasSnaky 4 (childrenC_59 j) (childrenD_59 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 5 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 0 (0, 1)).mono (by decide +kernel)
theorem row_works_59 : Template HasSnaky 5 required_59 envelope_59 := by
  refine compose HasSnaky 4 childrenC_59 childrenD_59 children_work_59 (3, 2)
    required_59 envelope_59 pivot_mem_59 child_required_sub_59 child_envelope_sub_59 ?_
  intro b hb
  exact common_sub_59 (mem_commonEnvelope childrenD_59 b hb)
def required_71 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_71 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_71 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), (placed21 2 (2, 0) required_10)]
def childrenD_71 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), (placed21 2 (2, 0) envelope_10)]
theorem common_sub_71 : commonEnvelope childrenD_71 ⊆ insert (2, 1) required_71 := by decide +kernel
theorem child_required_sub_71 : ∀ j, childrenC_71 j ⊆ insert (2, 1) required_71 := by decide +kernel
theorem child_envelope_sub_71 : ∀ j, childrenD_71 j ⊆ envelope_71 := by decide +kernel
theorem pivot_mem_71 : (2, 1) ∈ envelope_71 := by decide +kernel
theorem children_work_71 : ∀ j, Template HasSnaky 4 (childrenC_71 j) (childrenD_71 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_10 2 (2, 0)).mono (by decide +kernel)
theorem row_works_71 : Template HasSnaky 5 required_71 envelope_71 := by
  refine compose HasSnaky 4 childrenC_71 childrenD_71 children_work_71 (2, 1)
    required_71 envelope_71 pivot_mem_71 child_required_sub_71 child_envelope_sub_71 ?_
  intro b hb
  exact common_sub_71 (mem_commonEnvelope childrenD_71 b hb)
def required_72 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_72 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_72 : Fin 3 → Finset Cell := ![(placed21 1 (0, 1) required_20), (placed21 3 (0, 2) required_29), required_46]
def childrenD_72 : Fin 3 → Finset Cell := ![(placed21 1 (0, 1) envelope_20), (placed21 3 (0, 2) envelope_29), envelope_46]
theorem common_sub_72 : commonEnvelope childrenD_72 ⊆ insert (3, 2) required_72 := by decide +kernel
theorem child_required_sub_72 : ∀ j, childrenC_72 j ⊆ insert (3, 2) required_72 := by decide +kernel
theorem child_envelope_sub_72 : ∀ j, childrenD_72 j ⊆ envelope_72 := by decide +kernel
theorem pivot_mem_72 : (3, 2) ∈ envelope_72 := by decide +kernel
theorem children_work_72 : ∀ j, Template HasSnaky 4 (childrenC_72 j) (childrenD_72 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 3 (0, 2)).mono (by decide +kernel)
  · exact row_works_46.mono (by decide +kernel)
theorem row_works_72 : Template HasSnaky 5 required_72 envelope_72 := by
  refine compose HasSnaky 4 childrenC_72 childrenD_72 children_work_72 (3, 2)
    required_72 envelope_72 pivot_mem_72 child_required_sub_72 child_envelope_sub_72 ?_
  intro b hb
  exact common_sub_72 (mem_commonEnvelope childrenD_72 b hb)
def required_81 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_81 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_81 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 0 (2, 0) required_42)]
def childrenD_81 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 0 (2, 0) envelope_42)]
theorem common_sub_81 : commonEnvelope childrenD_81 ⊆ insert (3, 2) required_81 := by decide +kernel
theorem child_required_sub_81 : ∀ j, childrenC_81 j ⊆ insert (3, 2) required_81 := by decide +kernel
theorem child_envelope_sub_81 : ∀ j, childrenD_81 j ⊆ envelope_81 := by decide +kernel
theorem pivot_mem_81 : (3, 2) ∈ envelope_81 := by decide +kernel
theorem children_work_81 : ∀ j, Template HasSnaky 4 (childrenC_81 j) (childrenD_81 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_42 0 (2, 0)).mono (by decide +kernel)
theorem row_works_81 : Template HasSnaky 5 required_81 envelope_81 := by
  refine compose HasSnaky 4 childrenC_81 childrenD_81 children_work_81 (3, 2)
    required_81 envelope_81 pivot_mem_81 child_required_sub_81 child_envelope_sub_81 ?_
  intro b hb
  exact common_sub_81 (mem_commonEnvelope childrenD_81 b hb)
def required_84 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_84 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_84 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) required_6), (placed21 0 (0, 2) required_17)]
def childrenD_84 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) envelope_6), (placed21 0 (0, 2) envelope_17)]
theorem common_sub_84 : commonEnvelope childrenD_84 ⊆ insert (1, 5) required_84 := by decide +kernel
theorem child_required_sub_84 : ∀ j, childrenC_84 j ⊆ insert (1, 5) required_84 := by decide +kernel
theorem child_envelope_sub_84 : ∀ j, childrenD_84 j ⊆ envelope_84 := by decide +kernel
theorem pivot_mem_84 : (1, 5) ∈ envelope_84 := by decide +kernel
theorem children_work_84 : ∀ j, Template HasSnaky 4 (childrenC_84 j) (childrenD_84 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 0 (0, 2)).mono (by decide +kernel)
theorem row_works_84 : Template HasSnaky 5 required_84 envelope_84 := by
  refine compose HasSnaky 4 childrenC_84 childrenD_84 children_work_84 (1, 5)
    required_84 envelope_84 pivot_mem_84 child_required_sub_84 child_envelope_sub_84 ?_
  intro b hb
  exact common_sub_84 (mem_commonEnvelope childrenD_84 b hb)
def required_100 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_100 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_100 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_2), (placed21 2 (4, 0) required_10)]
def childrenD_100 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_2), (placed21 2 (4, 0) envelope_10)]
theorem common_sub_100 : commonEnvelope childrenD_100 ⊆ insert (4, 1) required_100 := by decide +kernel
theorem child_required_sub_100 : ∀ j, childrenC_100 j ⊆ insert (4, 1) required_100 := by decide +kernel
theorem child_envelope_sub_100 : ∀ j, childrenD_100 j ⊆ envelope_100 := by decide +kernel
theorem pivot_mem_100 : (4, 1) ∈ envelope_100 := by decide +kernel
theorem children_work_100 : ∀ j, Template HasSnaky 4 (childrenC_100 j) (childrenD_100 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_10 2 (4, 0)).mono (by decide +kernel)
theorem row_works_100 : Template HasSnaky 5 required_100 envelope_100 := by
  refine compose HasSnaky 4 childrenC_100 childrenD_100 children_work_100 (4, 1)
    required_100 envelope_100 pivot_mem_100 child_required_sub_100 child_envelope_sub_100 ?_
  intro b hb
  exact common_sub_100 (mem_commonEnvelope childrenD_100 b hb)
def required_104 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_104 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_104 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) required_10), (placed21 4 (0, 6) required_10), (placed21 2 (1, 2) required_52), (placed21 6 (1, 6) required_52)]
def childrenD_104 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) envelope_10), (placed21 4 (0, 6) envelope_10), (placed21 2 (1, 2) envelope_52), (placed21 6 (1, 6) envelope_52)]
theorem common_sub_104 : commonEnvelope childrenD_104 ⊆ insert (1, 4) required_104 := by decide +kernel
theorem child_required_sub_104 : ∀ j, childrenC_104 j ⊆ insert (1, 4) required_104 := by decide +kernel
theorem child_envelope_sub_104 : ∀ j, childrenD_104 j ⊆ envelope_104 := by decide +kernel
theorem pivot_mem_104 : (1, 4) ∈ envelope_104 := by decide +kernel
theorem children_work_104 : ∀ j, Template HasSnaky 4 (childrenC_104 j) (childrenD_104 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (1, 6)).mono (by decide +kernel)
theorem row_works_104 : Template HasSnaky 5 required_104 envelope_104 := by
  refine compose HasSnaky 4 childrenC_104 childrenD_104 children_work_104 (1, 4)
    required_104 envelope_104 pivot_mem_104 child_required_sub_104 child_envelope_sub_104 ?_
  intro b hb
  exact common_sub_104 (mem_commonEnvelope childrenD_104 b hb)
def required_107 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_107 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_107 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_3), (placed21 0 (0, 1) required_18)]
def childrenD_107 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_3), (placed21 0 (0, 1) envelope_18)]
theorem common_sub_107 : commonEnvelope childrenD_107 ⊆ insert (1, 2) required_107 := by decide +kernel
theorem child_required_sub_107 : ∀ j, childrenC_107 j ⊆ insert (1, 2) required_107 := by decide +kernel
theorem child_envelope_sub_107 : ∀ j, childrenD_107 j ⊆ envelope_107 := by decide +kernel
theorem pivot_mem_107 : (1, 2) ∈ envelope_107 := by decide +kernel
theorem children_work_107 : ∀ j, Template HasSnaky 4 (childrenC_107 j) (childrenD_107 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_18 0 (0, 1)).mono (by decide +kernel)
theorem row_works_107 : Template HasSnaky 5 required_107 envelope_107 := by
  refine compose HasSnaky 4 childrenC_107 childrenD_107 children_work_107 (1, 2)
    required_107 envelope_107 pivot_mem_107 child_required_sub_107 child_envelope_sub_107 ?_
  intro b hb
  exact common_sub_107 (mem_commonEnvelope childrenD_107 b hb)
def required_111 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_111 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_111 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) required_17), (placed21 2 (4, 0) required_55)]
def childrenD_111 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) envelope_17), (placed21 2 (4, 0) envelope_55)]
theorem common_sub_111 : commonEnvelope childrenD_111 ⊆ insert (4, 3) required_111 := by decide +kernel
theorem child_required_sub_111 : ∀ j, childrenC_111 j ⊆ insert (4, 3) required_111 := by decide +kernel
theorem child_envelope_sub_111 : ∀ j, childrenD_111 j ⊆ envelope_111 := by decide +kernel
theorem pivot_mem_111 : (4, 3) ∈ envelope_111 := by decide +kernel
theorem children_work_111 : ∀ j, Template HasSnaky 4 (childrenC_111 j) (childrenD_111 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_55 2 (4, 0)).mono (by decide +kernel)
theorem row_works_111 : Template HasSnaky 5 required_111 envelope_111 := by
  refine compose HasSnaky 4 childrenC_111 childrenD_111 children_work_111 (4, 3)
    required_111 envelope_111 pivot_mem_111 child_required_sub_111 child_envelope_sub_111 ?_
  intro b hb
  exact common_sub_111 (mem_commonEnvelope childrenD_111 b hb)
def required_114 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_114 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_114 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_5), (placed21 0 (2, 0) required_14)]
def childrenD_114 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_5), (placed21 0 (2, 0) envelope_14)]
theorem common_sub_114 : commonEnvelope childrenD_114 ⊆ insert (3, 4) required_114 := by decide +kernel
theorem child_required_sub_114 : ∀ j, childrenC_114 j ⊆ insert (3, 4) required_114 := by decide +kernel
theorem child_envelope_sub_114 : ∀ j, childrenD_114 j ⊆ envelope_114 := by decide +kernel
theorem pivot_mem_114 : (3, 4) ∈ envelope_114 := by decide +kernel
theorem children_work_114 : ∀ j, Template HasSnaky 4 (childrenC_114 j) (childrenD_114 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 0 (2, 0)).mono (by decide +kernel)
theorem row_works_114 : Template HasSnaky 5 required_114 envelope_114 := by
  refine compose HasSnaky 4 childrenC_114 childrenD_114 children_work_114 (3, 4)
    required_114 envelope_114 pivot_mem_114 child_required_sub_114 child_envelope_sub_114 ?_
  intro b hb
  exact common_sub_114 (mem_commonEnvelope childrenD_114 b hb)
def required_122 : Finset Cell := ⟨(([(1, 2), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_122 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 4), (3, 5), (3, 6), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_122 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_8), (placed21 3 (0, 4) required_46)]
def childrenD_122 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_8), (placed21 3 (0, 4) envelope_46)]
theorem common_sub_122 : commonEnvelope childrenD_122 ⊆ insert (2, 4) required_122 := by decide +kernel
theorem child_required_sub_122 : ∀ j, childrenC_122 j ⊆ insert (2, 4) required_122 := by decide +kernel
theorem child_envelope_sub_122 : ∀ j, childrenD_122 j ⊆ envelope_122 := by decide +kernel
theorem pivot_mem_122 : (2, 4) ∈ envelope_122 := by decide +kernel
theorem children_work_122 : ∀ j, Template HasSnaky 4 (childrenC_122 j) (childrenD_122 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_46 3 (0, 4)).mono (by decide +kernel)
theorem row_works_122 : Template HasSnaky 5 required_122 envelope_122 := by
  refine compose HasSnaky 4 childrenC_122 childrenD_122 children_work_122 (2, 4)
    required_122 envelope_122 pivot_mem_122 child_required_sub_122 child_envelope_sub_122 ?_
  intro b hb
  exact common_sub_122 (mem_commonEnvelope childrenD_122 b hb)
def required_133 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_133 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_133 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), required_132]
def childrenD_133 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), envelope_132]
theorem common_sub_133 : commonEnvelope childrenD_133 ⊆ insert (1, 1) required_133 := by decide +kernel
theorem child_required_sub_133 : ∀ j, childrenC_133 j ⊆ insert (1, 1) required_133 := by decide +kernel
theorem child_envelope_sub_133 : ∀ j, childrenD_133 j ⊆ envelope_133 := by decide +kernel
theorem pivot_mem_133 : (1, 1) ∈ envelope_133 := by decide +kernel
theorem children_work_133 : ∀ j, Template HasSnaky 4 (childrenC_133 j) (childrenD_133 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact row_works_132.mono (by decide +kernel)
theorem row_works_133 : Template HasSnaky 5 required_133 envelope_133 := by
  refine compose HasSnaky 4 childrenC_133 childrenD_133 children_work_133 (1, 1)
    required_133 envelope_133 pivot_mem_133 child_required_sub_133 child_envelope_sub_133 ?_
  intro b hb
  exact common_sub_133 (mem_commonEnvelope childrenD_133 b hb)
def required_142 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_142 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_142 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_5), (placed21 0 (1, 0) required_141)]
def childrenD_142 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_5), (placed21 0 (1, 0) envelope_141)]
theorem common_sub_142 : commonEnvelope childrenD_142 ⊆ insert (1, 2) required_142 := by decide +kernel
theorem child_required_sub_142 : ∀ j, childrenC_142 j ⊆ insert (1, 2) required_142 := by decide +kernel
theorem child_envelope_sub_142 : ∀ j, childrenD_142 j ⊆ envelope_142 := by decide +kernel
theorem pivot_mem_142 : (1, 2) ∈ envelope_142 := by decide +kernel
theorem children_work_142 : ∀ j, Template HasSnaky 4 (childrenC_142 j) (childrenD_142 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_141 0 (1, 0)).mono (by decide +kernel)
theorem row_works_142 : Template HasSnaky 5 required_142 envelope_142 := by
  refine compose HasSnaky 4 childrenC_142 childrenD_142 children_work_142 (1, 2)
    required_142 envelope_142 pivot_mem_142 child_required_sub_142 child_envelope_sub_142 ?_
  intro b hb
  exact common_sub_142 (mem_commonEnvelope childrenD_142 b hb)
def required_144 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_144 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_144 : Fin 3 → Finset Cell := ![required_46, (placed21 3 (0, 2) required_103), (placed21 0 (0, 1) required_143)]
def childrenD_144 : Fin 3 → Finset Cell := ![envelope_46, (placed21 3 (0, 2) envelope_103), (placed21 0 (0, 1) envelope_143)]
theorem common_sub_144 : commonEnvelope childrenD_144 ⊆ insert (3, 2) required_144 := by decide +kernel
theorem child_required_sub_144 : ∀ j, childrenC_144 j ⊆ insert (3, 2) required_144 := by decide +kernel
theorem child_envelope_sub_144 : ∀ j, childrenD_144 j ⊆ envelope_144 := by decide +kernel
theorem pivot_mem_144 : (3, 2) ∈ envelope_144 := by decide +kernel
theorem children_work_144 : ∀ j, Template HasSnaky 4 (childrenC_144 j) (childrenD_144 j) := by
  intro j
  fin_cases j
  · exact row_works_46.mono (by decide +kernel)
  · exact (placed21_template row_works_103 3 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_143 0 (0, 1)).mono (by decide +kernel)
theorem row_works_144 : Template HasSnaky 5 required_144 envelope_144 := by
  refine compose HasSnaky 4 childrenC_144 childrenD_144 children_work_144 (3, 2)
    required_144 envelope_144 pivot_mem_144 child_required_sub_144 child_envelope_sub_144 ?_
  intro b hb
  exact common_sub_144 (mem_commonEnvelope childrenD_144 b hb)
def required_145 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_145 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_145 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 0 (2, 0) required_10)]
def childrenD_145 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 0 (2, 0) envelope_10)]
theorem common_sub_145 : commonEnvelope childrenD_145 ⊆ insert (3, 2) required_145 := by decide +kernel
theorem child_required_sub_145 : ∀ j, childrenC_145 j ⊆ insert (3, 2) required_145 := by decide +kernel
theorem child_envelope_sub_145 : ∀ j, childrenD_145 j ⊆ envelope_145 := by decide +kernel
theorem pivot_mem_145 : (3, 2) ∈ envelope_145 := by decide +kernel
theorem children_work_145 : ∀ j, Template HasSnaky 4 (childrenC_145 j) (childrenD_145 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_10 0 (2, 0)).mono (by decide +kernel)
theorem row_works_145 : Template HasSnaky 5 required_145 envelope_145 := by
  refine compose HasSnaky 4 childrenC_145 childrenD_145 children_work_145 (3, 2)
    required_145 envelope_145 pivot_mem_145 child_required_sub_145 child_envelope_sub_145 ?_
  intro b hb
  exact common_sub_145 (mem_commonEnvelope childrenD_145 b hb)
def required_147 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_147 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_147 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 0 (2, 0) required_39)]
def childrenD_147 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 0 (2, 0) envelope_39)]
theorem common_sub_147 : commonEnvelope childrenD_147 ⊆ insert (3, 2) required_147 := by decide +kernel
theorem child_required_sub_147 : ∀ j, childrenC_147 j ⊆ insert (3, 2) required_147 := by decide +kernel
theorem child_envelope_sub_147 : ∀ j, childrenD_147 j ⊆ envelope_147 := by decide +kernel
theorem pivot_mem_147 : (3, 2) ∈ envelope_147 := by decide +kernel
theorem children_work_147 : ∀ j, Template HasSnaky 4 (childrenC_147 j) (childrenD_147 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_39 0 (2, 0)).mono (by decide +kernel)
theorem row_works_147 : Template HasSnaky 5 required_147 envelope_147 := by
  refine compose HasSnaky 4 childrenC_147 childrenD_147 children_work_147 (3, 2)
    required_147 envelope_147 pivot_mem_147 child_required_sub_147 child_envelope_sub_147 ?_
  intro b hb
  exact common_sub_147 (mem_commonEnvelope childrenD_147 b hb)
def required_152 : Finset Cell := ⟨(([(1, 1), (1, 3), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_152 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (4, 2), (4, 3), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_152 : Fin 2 → Finset Cell := ![(placed21 4 (1, 3) required_5), (placed21 2 (4, 0) required_99)]
def childrenD_152 : Fin 2 → Finset Cell := ![(placed21 4 (1, 3) envelope_5), (placed21 2 (4, 0) envelope_99)]
theorem common_sub_152 : commonEnvelope childrenD_152 ⊆ insert (2, 3) required_152 := by decide +kernel
theorem child_required_sub_152 : ∀ j, childrenC_152 j ⊆ insert (2, 3) required_152 := by decide +kernel
theorem child_envelope_sub_152 : ∀ j, childrenD_152 j ⊆ envelope_152 := by decide +kernel
theorem pivot_mem_152 : (2, 3) ∈ envelope_152 := by decide +kernel
theorem children_work_152 : ∀ j, Template HasSnaky 4 (childrenC_152 j) (childrenD_152 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_99 2 (4, 0)).mono (by decide +kernel)
theorem row_works_152 : Template HasSnaky 5 required_152 envelope_152 := by
  refine compose HasSnaky 4 childrenC_152 childrenD_152 children_work_152 (2, 3)
    required_152 envelope_152 pivot_mem_152 child_required_sub_152 child_envelope_sub_152 ?_
  intro b hb
  exact common_sub_152 (mem_commonEnvelope childrenD_152 b hb)
def required_155 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_155 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_155 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) required_7), (placed21 1 (0, 1) required_9), (placed21 0 (1, 0) required_46)]
def childrenD_155 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) envelope_7), (placed21 1 (0, 1) envelope_9), (placed21 0 (1, 0) envelope_46)]
theorem common_sub_155 : commonEnvelope childrenD_155 ⊆ insert (4, 2) required_155 := by decide +kernel
theorem child_required_sub_155 : ∀ j, childrenC_155 j ⊆ insert (4, 2) required_155 := by decide +kernel
theorem child_envelope_sub_155 : ∀ j, childrenD_155 j ⊆ envelope_155 := by decide +kernel
theorem pivot_mem_155 : (4, 2) ∈ envelope_155 := by decide +kernel
theorem children_work_155 : ∀ j, Template HasSnaky 4 (childrenC_155 j) (childrenD_155 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_46 0 (1, 0)).mono (by decide +kernel)
theorem row_works_155 : Template HasSnaky 5 required_155 envelope_155 := by
  refine compose HasSnaky 4 childrenC_155 childrenD_155 children_work_155 (4, 2)
    required_155 envelope_155 pivot_mem_155 child_required_sub_155 child_envelope_sub_155 ?_
  intro b hb
  exact common_sub_155 (mem_commonEnvelope childrenD_155 b hb)
def required_164 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_164 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_164 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), required_55]
def childrenD_164 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), envelope_55]
theorem common_sub_164 : commonEnvelope childrenD_164 ⊆ insert (3, 3) required_164 := by decide +kernel
theorem child_required_sub_164 : ∀ j, childrenC_164 j ⊆ insert (3, 3) required_164 := by decide +kernel
theorem child_envelope_sub_164 : ∀ j, childrenD_164 j ⊆ envelope_164 := by decide +kernel
theorem pivot_mem_164 : (3, 3) ∈ envelope_164 := by decide +kernel
theorem children_work_164 : ∀ j, Template HasSnaky 4 (childrenC_164 j) (childrenD_164 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact row_works_55.mono (by decide +kernel)
theorem row_works_164 : Template HasSnaky 5 required_164 envelope_164 := by
  refine compose HasSnaky 4 childrenC_164 childrenD_164 children_work_164 (3, 3)
    required_164 envelope_164 pivot_mem_164 child_required_sub_164 child_envelope_sub_164 ?_
  intro b hb
  exact common_sub_164 (mem_commonEnvelope childrenD_164 b hb)
def required_175 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (2, 4), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_175 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_175 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) required_7), (placed21 1 (0, 2) required_32), (placed21 4 (0, 6) required_60)]
def childrenD_175 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) envelope_7), (placed21 1 (0, 2) envelope_32), (placed21 4 (0, 6) envelope_60)]
theorem common_sub_175 : commonEnvelope childrenD_175 ⊆ insert (1, 5) required_175 := by decide +kernel
theorem child_required_sub_175 : ∀ j, childrenC_175 j ⊆ insert (1, 5) required_175 := by decide +kernel
theorem child_envelope_sub_175 : ∀ j, childrenD_175 j ⊆ envelope_175 := by decide +kernel
theorem pivot_mem_175 : (1, 5) ∈ envelope_175 := by decide +kernel
theorem children_work_175 : ∀ j, Template HasSnaky 4 (childrenC_175 j) (childrenD_175 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_60 4 (0, 6)).mono (by decide +kernel)
theorem row_works_175 : Template HasSnaky 5 required_175 envelope_175 := by
  refine compose HasSnaky 4 childrenC_175 childrenD_175 children_work_175 (1, 5)
    required_175 envelope_175 pivot_mem_175 child_required_sub_175 child_envelope_sub_175 ?_
  intro b hb
  exact common_sub_175 (mem_commonEnvelope childrenD_175 b hb)
def required_176 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_176 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_176 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_0), (placed21 2 (4, 0) required_60)]
def childrenD_176 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_0), (placed21 2 (4, 0) envelope_60)]
theorem common_sub_176 : commonEnvelope childrenD_176 ⊆ insert (2, 2) required_176 := by decide +kernel
theorem child_required_sub_176 : ∀ j, childrenC_176 j ⊆ insert (2, 2) required_176 := by decide +kernel
theorem child_envelope_sub_176 : ∀ j, childrenD_176 j ⊆ envelope_176 := by decide +kernel
theorem pivot_mem_176 : (2, 2) ∈ envelope_176 := by decide +kernel
theorem children_work_176 : ∀ j, Template HasSnaky 4 (childrenC_176 j) (childrenD_176 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_60 2 (4, 0)).mono (by decide +kernel)
theorem row_works_176 : Template HasSnaky 5 required_176 envelope_176 := by
  refine compose HasSnaky 4 childrenC_176 childrenD_176 children_work_176 (2, 2)
    required_176 envelope_176 pivot_mem_176 child_required_sub_176 child_envelope_sub_176 ?_
  intro b hb
  exact common_sub_176 (mem_commonEnvelope childrenD_176 b hb)
def required_179 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_179 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_179 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_5), required_178]
def childrenD_179 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_5), envelope_178]
theorem common_sub_179 : commonEnvelope childrenD_179 ⊆ insert (1, 3) required_179 := by decide +kernel
theorem child_required_sub_179 : ∀ j, childrenC_179 j ⊆ insert (1, 3) required_179 := by decide +kernel
theorem child_envelope_sub_179 : ∀ j, childrenD_179 j ⊆ envelope_179 := by decide +kernel
theorem pivot_mem_179 : (1, 3) ∈ envelope_179 := by decide +kernel
theorem children_work_179 : ∀ j, Template HasSnaky 4 (childrenC_179 j) (childrenD_179 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact row_works_178.mono (by decide +kernel)
theorem row_works_179 : Template HasSnaky 5 required_179 envelope_179 := by
  refine compose HasSnaky 4 childrenC_179 childrenD_179 children_work_179 (1, 3)
    required_179 envelope_179 pivot_mem_179 child_required_sub_179 child_envelope_sub_179 ?_
  intro b hb
  exact common_sub_179 (mem_commonEnvelope childrenD_179 b hb)
def height_19 : ℕ := 5
def childrenH_19 : Fin 2 → ℕ := ![height_5, height_18]
theorem height_exact_19 : height_19 = 1 + Finset.univ.sup childrenH_19 := by decide +kernel
theorem required_origin_19 : ∀ x ∈ required_19,
    (∃ j, x ∈ childrenC_19 j) ∨ ∀ j, x ∈ childrenD_19 j := by decide +kernel
theorem required_exact_19 : required_19 =
    ((Finset.univ.biUnion childrenC_19) ∪ commonEnvelope childrenD_19).erase (0, 1) := by
  exact required_eq_combination childrenC_19 childrenD_19 (0, 1) required_19
    (by decide +kernel) child_required_sub_19 common_sub_19 required_origin_19
theorem envelope_origin_19 : ∀ x ∈ envelope_19,
    x = (0, 1) ∨ ∃ j, x ∈ childrenD_19 j := by decide +kernel
theorem envelope_exact_19 : envelope_19 =
    insert (0, 1) (Finset.univ.biUnion childrenD_19) := by
  exact envelope_eq_combination childrenD_19 (0, 1) envelope_19
    pivot_mem_19 child_envelope_sub_19 envelope_origin_19
def checked_19 : CheckedCard where
  required := required_19
  envelope := envelope_19
  height := height_19
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_19
def height_47 : ℕ := 5
def childrenH_47 : Fin 3 → ℕ := ![height_7, height_9, height_46]
theorem height_exact_47 : height_47 = 1 + Finset.univ.sup childrenH_47 := by decide +kernel
theorem required_origin_47 : ∀ x ∈ required_47,
    (∃ j, x ∈ childrenC_47 j) ∨ ∀ j, x ∈ childrenD_47 j := by decide +kernel
theorem required_exact_47 : required_47 =
    ((Finset.univ.biUnion childrenC_47) ∪ commonEnvelope childrenD_47).erase (4, 2) := by
  exact required_eq_combination childrenC_47 childrenD_47 (4, 2) required_47
    (by decide +kernel) child_required_sub_47 common_sub_47 required_origin_47
theorem envelope_origin_47 : ∀ x ∈ envelope_47,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_47 j := by decide +kernel
theorem envelope_exact_47 : envelope_47 =
    insert (4, 2) (Finset.univ.biUnion childrenD_47) := by
  exact envelope_eq_combination childrenD_47 (4, 2) envelope_47
    pivot_mem_47 child_envelope_sub_47 envelope_origin_47
def checked_47 : CheckedCard where
  required := required_47
  envelope := envelope_47
  height := height_47
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_47
def height_59 : ℕ := 5
def childrenH_59 : Fin 3 → ℕ := ![height_28, height_31, height_58]
theorem height_exact_59 : height_59 = 1 + Finset.univ.sup childrenH_59 := by decide +kernel
theorem required_origin_59 : ∀ x ∈ required_59,
    (∃ j, x ∈ childrenC_59 j) ∨ ∀ j, x ∈ childrenD_59 j := by decide +kernel
theorem required_exact_59 : required_59 =
    ((Finset.univ.biUnion childrenC_59) ∪ commonEnvelope childrenD_59).erase (3, 2) := by
  exact required_eq_combination childrenC_59 childrenD_59 (3, 2) required_59
    (by decide +kernel) child_required_sub_59 common_sub_59 required_origin_59
theorem envelope_origin_59 : ∀ x ∈ envelope_59,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_59 j := by decide +kernel
theorem envelope_exact_59 : envelope_59 =
    insert (3, 2) (Finset.univ.biUnion childrenD_59) := by
  exact envelope_eq_combination childrenD_59 (3, 2) envelope_59
    pivot_mem_59 child_envelope_sub_59 envelope_origin_59
def checked_59 : CheckedCard where
  required := required_59
  envelope := envelope_59
  height := height_59
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_59
def height_71 : ℕ := 5
def childrenH_71 : Fin 2 → ℕ := ![height_0, height_10]
theorem height_exact_71 : height_71 = 1 + Finset.univ.sup childrenH_71 := by decide +kernel
theorem required_origin_71 : ∀ x ∈ required_71,
    (∃ j, x ∈ childrenC_71 j) ∨ ∀ j, x ∈ childrenD_71 j := by decide +kernel
theorem required_exact_71 : required_71 =
    ((Finset.univ.biUnion childrenC_71) ∪ commonEnvelope childrenD_71).erase (2, 1) := by
  exact required_eq_combination childrenC_71 childrenD_71 (2, 1) required_71
    (by decide +kernel) child_required_sub_71 common_sub_71 required_origin_71
theorem envelope_origin_71 : ∀ x ∈ envelope_71,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_71 j := by decide +kernel
theorem envelope_exact_71 : envelope_71 =
    insert (2, 1) (Finset.univ.biUnion childrenD_71) := by
  exact envelope_eq_combination childrenD_71 (2, 1) envelope_71
    pivot_mem_71 child_envelope_sub_71 envelope_origin_71
def checked_71 : CheckedCard where
  required := required_71
  envelope := envelope_71
  height := height_71
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_71
def height_72 : ℕ := 5
def childrenH_72 : Fin 3 → ℕ := ![height_20, height_29, height_46]
theorem height_exact_72 : height_72 = 1 + Finset.univ.sup childrenH_72 := by decide +kernel
theorem required_origin_72 : ∀ x ∈ required_72,
    (∃ j, x ∈ childrenC_72 j) ∨ ∀ j, x ∈ childrenD_72 j := by decide +kernel
theorem required_exact_72 : required_72 =
    ((Finset.univ.biUnion childrenC_72) ∪ commonEnvelope childrenD_72).erase (3, 2) := by
  exact required_eq_combination childrenC_72 childrenD_72 (3, 2) required_72
    (by decide +kernel) child_required_sub_72 common_sub_72 required_origin_72
theorem envelope_origin_72 : ∀ x ∈ envelope_72,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_72 j := by decide +kernel
theorem envelope_exact_72 : envelope_72 =
    insert (3, 2) (Finset.univ.biUnion childrenD_72) := by
  exact envelope_eq_combination childrenD_72 (3, 2) envelope_72
    pivot_mem_72 child_envelope_sub_72 envelope_origin_72
def checked_72 : CheckedCard where
  required := required_72
  envelope := envelope_72
  height := height_72
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_72
def height_81 : ℕ := 5
def childrenH_81 : Fin 2 → ℕ := ![height_5, height_42]
theorem height_exact_81 : height_81 = 1 + Finset.univ.sup childrenH_81 := by decide +kernel
theorem required_origin_81 : ∀ x ∈ required_81,
    (∃ j, x ∈ childrenC_81 j) ∨ ∀ j, x ∈ childrenD_81 j := by decide +kernel
theorem required_exact_81 : required_81 =
    ((Finset.univ.biUnion childrenC_81) ∪ commonEnvelope childrenD_81).erase (3, 2) := by
  exact required_eq_combination childrenC_81 childrenD_81 (3, 2) required_81
    (by decide +kernel) child_required_sub_81 common_sub_81 required_origin_81
theorem envelope_origin_81 : ∀ x ∈ envelope_81,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_81 j := by decide +kernel
theorem envelope_exact_81 : envelope_81 =
    insert (3, 2) (Finset.univ.biUnion childrenD_81) := by
  exact envelope_eq_combination childrenD_81 (3, 2) envelope_81
    pivot_mem_81 child_envelope_sub_81 envelope_origin_81
def checked_81 : CheckedCard where
  required := required_81
  envelope := envelope_81
  height := height_81
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_81
def height_84 : ℕ := 5
def childrenH_84 : Fin 2 → ℕ := ![height_6, height_17]
theorem height_exact_84 : height_84 = 1 + Finset.univ.sup childrenH_84 := by decide +kernel
theorem required_origin_84 : ∀ x ∈ required_84,
    (∃ j, x ∈ childrenC_84 j) ∨ ∀ j, x ∈ childrenD_84 j := by decide +kernel
theorem required_exact_84 : required_84 =
    ((Finset.univ.biUnion childrenC_84) ∪ commonEnvelope childrenD_84).erase (1, 5) := by
  exact required_eq_combination childrenC_84 childrenD_84 (1, 5) required_84
    (by decide +kernel) child_required_sub_84 common_sub_84 required_origin_84
theorem envelope_origin_84 : ∀ x ∈ envelope_84,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_84 j := by decide +kernel
theorem envelope_exact_84 : envelope_84 =
    insert (1, 5) (Finset.univ.biUnion childrenD_84) := by
  exact envelope_eq_combination childrenD_84 (1, 5) envelope_84
    pivot_mem_84 child_envelope_sub_84 envelope_origin_84
def checked_84 : CheckedCard where
  required := required_84
  envelope := envelope_84
  height := height_84
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_84
def height_100 : ℕ := 5
def childrenH_100 : Fin 2 → ℕ := ![height_2, height_10]
theorem height_exact_100 : height_100 = 1 + Finset.univ.sup childrenH_100 := by decide +kernel
theorem required_origin_100 : ∀ x ∈ required_100,
    (∃ j, x ∈ childrenC_100 j) ∨ ∀ j, x ∈ childrenD_100 j := by decide +kernel
theorem required_exact_100 : required_100 =
    ((Finset.univ.biUnion childrenC_100) ∪ commonEnvelope childrenD_100).erase (4, 1) := by
  exact required_eq_combination childrenC_100 childrenD_100 (4, 1) required_100
    (by decide +kernel) child_required_sub_100 common_sub_100 required_origin_100
theorem envelope_origin_100 : ∀ x ∈ envelope_100,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_100 j := by decide +kernel
theorem envelope_exact_100 : envelope_100 =
    insert (4, 1) (Finset.univ.biUnion childrenD_100) := by
  exact envelope_eq_combination childrenD_100 (4, 1) envelope_100
    pivot_mem_100 child_envelope_sub_100 envelope_origin_100
def checked_100 : CheckedCard where
  required := required_100
  envelope := envelope_100
  height := height_100
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_100
def height_104 : ℕ := 5
def childrenH_104 : Fin 4 → ℕ := ![height_10, height_10, height_52, height_52]
theorem height_exact_104 : height_104 = 1 + Finset.univ.sup childrenH_104 := by decide +kernel
theorem required_origin_104 : ∀ x ∈ required_104,
    (∃ j, x ∈ childrenC_104 j) ∨ ∀ j, x ∈ childrenD_104 j := by decide +kernel
theorem required_exact_104 : required_104 =
    ((Finset.univ.biUnion childrenC_104) ∪ commonEnvelope childrenD_104).erase (1, 4) := by
  exact required_eq_combination childrenC_104 childrenD_104 (1, 4) required_104
    (by decide +kernel) child_required_sub_104 common_sub_104 required_origin_104
theorem envelope_origin_104 : ∀ x ∈ envelope_104,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_104 j := by decide +kernel
theorem envelope_exact_104 : envelope_104 =
    insert (1, 4) (Finset.univ.biUnion childrenD_104) := by
  exact envelope_eq_combination childrenD_104 (1, 4) envelope_104
    pivot_mem_104 child_envelope_sub_104 envelope_origin_104
def checked_104 : CheckedCard where
  required := required_104
  envelope := envelope_104
  height := height_104
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_104
def height_107 : ℕ := 5
def childrenH_107 : Fin 2 → ℕ := ![height_3, height_18]
theorem height_exact_107 : height_107 = 1 + Finset.univ.sup childrenH_107 := by decide +kernel
theorem required_origin_107 : ∀ x ∈ required_107,
    (∃ j, x ∈ childrenC_107 j) ∨ ∀ j, x ∈ childrenD_107 j := by decide +kernel
theorem required_exact_107 : required_107 =
    ((Finset.univ.biUnion childrenC_107) ∪ commonEnvelope childrenD_107).erase (1, 2) := by
  exact required_eq_combination childrenC_107 childrenD_107 (1, 2) required_107
    (by decide +kernel) child_required_sub_107 common_sub_107 required_origin_107
theorem envelope_origin_107 : ∀ x ∈ envelope_107,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_107 j := by decide +kernel
theorem envelope_exact_107 : envelope_107 =
    insert (1, 2) (Finset.univ.biUnion childrenD_107) := by
  exact envelope_eq_combination childrenD_107 (1, 2) envelope_107
    pivot_mem_107 child_envelope_sub_107 envelope_origin_107
def checked_107 : CheckedCard where
  required := required_107
  envelope := envelope_107
  height := height_107
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_107
def height_111 : ℕ := 5
def childrenH_111 : Fin 2 → ℕ := ![height_17, height_55]
theorem height_exact_111 : height_111 = 1 + Finset.univ.sup childrenH_111 := by decide +kernel
theorem required_origin_111 : ∀ x ∈ required_111,
    (∃ j, x ∈ childrenC_111 j) ∨ ∀ j, x ∈ childrenD_111 j := by decide +kernel
theorem required_exact_111 : required_111 =
    ((Finset.univ.biUnion childrenC_111) ∪ commonEnvelope childrenD_111).erase (4, 3) := by
  exact required_eq_combination childrenC_111 childrenD_111 (4, 3) required_111
    (by decide +kernel) child_required_sub_111 common_sub_111 required_origin_111
theorem envelope_origin_111 : ∀ x ∈ envelope_111,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_111 j := by decide +kernel
theorem envelope_exact_111 : envelope_111 =
    insert (4, 3) (Finset.univ.biUnion childrenD_111) := by
  exact envelope_eq_combination childrenD_111 (4, 3) envelope_111
    pivot_mem_111 child_envelope_sub_111 envelope_origin_111
def checked_111 : CheckedCard where
  required := required_111
  envelope := envelope_111
  height := height_111
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_111
def height_114 : ℕ := 5
def childrenH_114 : Fin 2 → ℕ := ![height_5, height_14]
theorem height_exact_114 : height_114 = 1 + Finset.univ.sup childrenH_114 := by decide +kernel
theorem required_origin_114 : ∀ x ∈ required_114,
    (∃ j, x ∈ childrenC_114 j) ∨ ∀ j, x ∈ childrenD_114 j := by decide +kernel
theorem required_exact_114 : required_114 =
    ((Finset.univ.biUnion childrenC_114) ∪ commonEnvelope childrenD_114).erase (3, 4) := by
  exact required_eq_combination childrenC_114 childrenD_114 (3, 4) required_114
    (by decide +kernel) child_required_sub_114 common_sub_114 required_origin_114
theorem envelope_origin_114 : ∀ x ∈ envelope_114,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_114 j := by decide +kernel
theorem envelope_exact_114 : envelope_114 =
    insert (3, 4) (Finset.univ.biUnion childrenD_114) := by
  exact envelope_eq_combination childrenD_114 (3, 4) envelope_114
    pivot_mem_114 child_envelope_sub_114 envelope_origin_114
def checked_114 : CheckedCard where
  required := required_114
  envelope := envelope_114
  height := height_114
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_114
def height_122 : ℕ := 5
def childrenH_122 : Fin 2 → ℕ := ![height_8, height_46]
theorem height_exact_122 : height_122 = 1 + Finset.univ.sup childrenH_122 := by decide +kernel
theorem required_origin_122 : ∀ x ∈ required_122,
    (∃ j, x ∈ childrenC_122 j) ∨ ∀ j, x ∈ childrenD_122 j := by decide +kernel
theorem required_exact_122 : required_122 =
    ((Finset.univ.biUnion childrenC_122) ∪ commonEnvelope childrenD_122).erase (2, 4) := by
  exact required_eq_combination childrenC_122 childrenD_122 (2, 4) required_122
    (by decide +kernel) child_required_sub_122 common_sub_122 required_origin_122
theorem envelope_origin_122 : ∀ x ∈ envelope_122,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_122 j := by decide +kernel
theorem envelope_exact_122 : envelope_122 =
    insert (2, 4) (Finset.univ.biUnion childrenD_122) := by
  exact envelope_eq_combination childrenD_122 (2, 4) envelope_122
    pivot_mem_122 child_envelope_sub_122 envelope_origin_122
def checked_122 : CheckedCard where
  required := required_122
  envelope := envelope_122
  height := height_122
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_122
def height_133 : ℕ := 5
def childrenH_133 : Fin 2 → ℕ := ![height_5, height_132]
theorem height_exact_133 : height_133 = 1 + Finset.univ.sup childrenH_133 := by decide +kernel
theorem required_origin_133 : ∀ x ∈ required_133,
    (∃ j, x ∈ childrenC_133 j) ∨ ∀ j, x ∈ childrenD_133 j := by decide +kernel
theorem required_exact_133 : required_133 =
    ((Finset.univ.biUnion childrenC_133) ∪ commonEnvelope childrenD_133).erase (1, 1) := by
  exact required_eq_combination childrenC_133 childrenD_133 (1, 1) required_133
    (by decide +kernel) child_required_sub_133 common_sub_133 required_origin_133
theorem envelope_origin_133 : ∀ x ∈ envelope_133,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_133 j := by decide +kernel
theorem envelope_exact_133 : envelope_133 =
    insert (1, 1) (Finset.univ.biUnion childrenD_133) := by
  exact envelope_eq_combination childrenD_133 (1, 1) envelope_133
    pivot_mem_133 child_envelope_sub_133 envelope_origin_133
def checked_133 : CheckedCard where
  required := required_133
  envelope := envelope_133
  height := height_133
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_133
def height_142 : ℕ := 5
def childrenH_142 : Fin 2 → ℕ := ![height_5, height_141]
theorem height_exact_142 : height_142 = 1 + Finset.univ.sup childrenH_142 := by decide +kernel
theorem required_origin_142 : ∀ x ∈ required_142,
    (∃ j, x ∈ childrenC_142 j) ∨ ∀ j, x ∈ childrenD_142 j := by decide +kernel
theorem required_exact_142 : required_142 =
    ((Finset.univ.biUnion childrenC_142) ∪ commonEnvelope childrenD_142).erase (1, 2) := by
  exact required_eq_combination childrenC_142 childrenD_142 (1, 2) required_142
    (by decide +kernel) child_required_sub_142 common_sub_142 required_origin_142
theorem envelope_origin_142 : ∀ x ∈ envelope_142,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_142 j := by decide +kernel
theorem envelope_exact_142 : envelope_142 =
    insert (1, 2) (Finset.univ.biUnion childrenD_142) := by
  exact envelope_eq_combination childrenD_142 (1, 2) envelope_142
    pivot_mem_142 child_envelope_sub_142 envelope_origin_142
def checked_142 : CheckedCard where
  required := required_142
  envelope := envelope_142
  height := height_142
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_142
def height_144 : ℕ := 5
def childrenH_144 : Fin 3 → ℕ := ![height_46, height_103, height_143]
theorem height_exact_144 : height_144 = 1 + Finset.univ.sup childrenH_144 := by decide +kernel
theorem required_origin_144 : ∀ x ∈ required_144,
    (∃ j, x ∈ childrenC_144 j) ∨ ∀ j, x ∈ childrenD_144 j := by decide +kernel
theorem required_exact_144 : required_144 =
    ((Finset.univ.biUnion childrenC_144) ∪ commonEnvelope childrenD_144).erase (3, 2) := by
  exact required_eq_combination childrenC_144 childrenD_144 (3, 2) required_144
    (by decide +kernel) child_required_sub_144 common_sub_144 required_origin_144
theorem envelope_origin_144 : ∀ x ∈ envelope_144,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_144 j := by decide +kernel
theorem envelope_exact_144 : envelope_144 =
    insert (3, 2) (Finset.univ.biUnion childrenD_144) := by
  exact envelope_eq_combination childrenD_144 (3, 2) envelope_144
    pivot_mem_144 child_envelope_sub_144 envelope_origin_144
def checked_144 : CheckedCard where
  required := required_144
  envelope := envelope_144
  height := height_144
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_144
def height_145 : ℕ := 5
def childrenH_145 : Fin 2 → ℕ := ![height_5, height_10]
theorem height_exact_145 : height_145 = 1 + Finset.univ.sup childrenH_145 := by decide +kernel
theorem required_origin_145 : ∀ x ∈ required_145,
    (∃ j, x ∈ childrenC_145 j) ∨ ∀ j, x ∈ childrenD_145 j := by decide +kernel
theorem required_exact_145 : required_145 =
    ((Finset.univ.biUnion childrenC_145) ∪ commonEnvelope childrenD_145).erase (3, 2) := by
  exact required_eq_combination childrenC_145 childrenD_145 (3, 2) required_145
    (by decide +kernel) child_required_sub_145 common_sub_145 required_origin_145
theorem envelope_origin_145 : ∀ x ∈ envelope_145,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_145 j := by decide +kernel
theorem envelope_exact_145 : envelope_145 =
    insert (3, 2) (Finset.univ.biUnion childrenD_145) := by
  exact envelope_eq_combination childrenD_145 (3, 2) envelope_145
    pivot_mem_145 child_envelope_sub_145 envelope_origin_145
def checked_145 : CheckedCard where
  required := required_145
  envelope := envelope_145
  height := height_145
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_145
def height_147 : ℕ := 5
def childrenH_147 : Fin 2 → ℕ := ![height_5, height_39]
theorem height_exact_147 : height_147 = 1 + Finset.univ.sup childrenH_147 := by decide +kernel
theorem required_origin_147 : ∀ x ∈ required_147,
    (∃ j, x ∈ childrenC_147 j) ∨ ∀ j, x ∈ childrenD_147 j := by decide +kernel
theorem required_exact_147 : required_147 =
    ((Finset.univ.biUnion childrenC_147) ∪ commonEnvelope childrenD_147).erase (3, 2) := by
  exact required_eq_combination childrenC_147 childrenD_147 (3, 2) required_147
    (by decide +kernel) child_required_sub_147 common_sub_147 required_origin_147
theorem envelope_origin_147 : ∀ x ∈ envelope_147,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_147 j := by decide +kernel
theorem envelope_exact_147 : envelope_147 =
    insert (3, 2) (Finset.univ.biUnion childrenD_147) := by
  exact envelope_eq_combination childrenD_147 (3, 2) envelope_147
    pivot_mem_147 child_envelope_sub_147 envelope_origin_147
def checked_147 : CheckedCard where
  required := required_147
  envelope := envelope_147
  height := height_147
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_147
def height_152 : ℕ := 5
def childrenH_152 : Fin 2 → ℕ := ![height_5, height_99]
theorem height_exact_152 : height_152 = 1 + Finset.univ.sup childrenH_152 := by decide +kernel
theorem required_origin_152 : ∀ x ∈ required_152,
    (∃ j, x ∈ childrenC_152 j) ∨ ∀ j, x ∈ childrenD_152 j := by decide +kernel
theorem required_exact_152 : required_152 =
    ((Finset.univ.biUnion childrenC_152) ∪ commonEnvelope childrenD_152).erase (2, 3) := by
  exact required_eq_combination childrenC_152 childrenD_152 (2, 3) required_152
    (by decide +kernel) child_required_sub_152 common_sub_152 required_origin_152
theorem envelope_origin_152 : ∀ x ∈ envelope_152,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_152 j := by decide +kernel
theorem envelope_exact_152 : envelope_152 =
    insert (2, 3) (Finset.univ.biUnion childrenD_152) := by
  exact envelope_eq_combination childrenD_152 (2, 3) envelope_152
    pivot_mem_152 child_envelope_sub_152 envelope_origin_152
def checked_152 : CheckedCard where
  required := required_152
  envelope := envelope_152
  height := height_152
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_152
def height_155 : ℕ := 5
def childrenH_155 : Fin 3 → ℕ := ![height_7, height_9, height_46]
theorem height_exact_155 : height_155 = 1 + Finset.univ.sup childrenH_155 := by decide +kernel
theorem required_origin_155 : ∀ x ∈ required_155,
    (∃ j, x ∈ childrenC_155 j) ∨ ∀ j, x ∈ childrenD_155 j := by decide +kernel
theorem required_exact_155 : required_155 =
    ((Finset.univ.biUnion childrenC_155) ∪ commonEnvelope childrenD_155).erase (4, 2) := by
  exact required_eq_combination childrenC_155 childrenD_155 (4, 2) required_155
    (by decide +kernel) child_required_sub_155 common_sub_155 required_origin_155
theorem envelope_origin_155 : ∀ x ∈ envelope_155,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_155 j := by decide +kernel
theorem envelope_exact_155 : envelope_155 =
    insert (4, 2) (Finset.univ.biUnion childrenD_155) := by
  exact envelope_eq_combination childrenD_155 (4, 2) envelope_155
    pivot_mem_155 child_envelope_sub_155 envelope_origin_155
def checked_155 : CheckedCard where
  required := required_155
  envelope := envelope_155
  height := height_155
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_155
def height_164 : ℕ := 5
def childrenH_164 : Fin 2 → ℕ := ![height_0, height_55]
theorem height_exact_164 : height_164 = 1 + Finset.univ.sup childrenH_164 := by decide +kernel
theorem required_origin_164 : ∀ x ∈ required_164,
    (∃ j, x ∈ childrenC_164 j) ∨ ∀ j, x ∈ childrenD_164 j := by decide +kernel
theorem required_exact_164 : required_164 =
    ((Finset.univ.biUnion childrenC_164) ∪ commonEnvelope childrenD_164).erase (3, 3) := by
  exact required_eq_combination childrenC_164 childrenD_164 (3, 3) required_164
    (by decide +kernel) child_required_sub_164 common_sub_164 required_origin_164
theorem envelope_origin_164 : ∀ x ∈ envelope_164,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_164 j := by decide +kernel
theorem envelope_exact_164 : envelope_164 =
    insert (3, 3) (Finset.univ.biUnion childrenD_164) := by
  exact envelope_eq_combination childrenD_164 (3, 3) envelope_164
    pivot_mem_164 child_envelope_sub_164 envelope_origin_164
def checked_164 : CheckedCard where
  required := required_164
  envelope := envelope_164
  height := height_164
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_164
def height_175 : ℕ := 5
def childrenH_175 : Fin 3 → ℕ := ![height_7, height_32, height_60]
theorem height_exact_175 : height_175 = 1 + Finset.univ.sup childrenH_175 := by decide +kernel
theorem required_origin_175 : ∀ x ∈ required_175,
    (∃ j, x ∈ childrenC_175 j) ∨ ∀ j, x ∈ childrenD_175 j := by decide +kernel
theorem required_exact_175 : required_175 =
    ((Finset.univ.biUnion childrenC_175) ∪ commonEnvelope childrenD_175).erase (1, 5) := by
  exact required_eq_combination childrenC_175 childrenD_175 (1, 5) required_175
    (by decide +kernel) child_required_sub_175 common_sub_175 required_origin_175
theorem envelope_origin_175 : ∀ x ∈ envelope_175,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_175 j := by decide +kernel
theorem envelope_exact_175 : envelope_175 =
    insert (1, 5) (Finset.univ.biUnion childrenD_175) := by
  exact envelope_eq_combination childrenD_175 (1, 5) envelope_175
    pivot_mem_175 child_envelope_sub_175 envelope_origin_175
def checked_175 : CheckedCard where
  required := required_175
  envelope := envelope_175
  height := height_175
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_175
def height_176 : ℕ := 5
def childrenH_176 : Fin 2 → ℕ := ![height_0, height_60]
theorem height_exact_176 : height_176 = 1 + Finset.univ.sup childrenH_176 := by decide +kernel
theorem required_origin_176 : ∀ x ∈ required_176,
    (∃ j, x ∈ childrenC_176 j) ∨ ∀ j, x ∈ childrenD_176 j := by decide +kernel
theorem required_exact_176 : required_176 =
    ((Finset.univ.biUnion childrenC_176) ∪ commonEnvelope childrenD_176).erase (2, 2) := by
  exact required_eq_combination childrenC_176 childrenD_176 (2, 2) required_176
    (by decide +kernel) child_required_sub_176 common_sub_176 required_origin_176
theorem envelope_origin_176 : ∀ x ∈ envelope_176,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_176 j := by decide +kernel
theorem envelope_exact_176 : envelope_176 =
    insert (2, 2) (Finset.univ.biUnion childrenD_176) := by
  exact envelope_eq_combination childrenD_176 (2, 2) envelope_176
    pivot_mem_176 child_envelope_sub_176 envelope_origin_176
def checked_176 : CheckedCard where
  required := required_176
  envelope := envelope_176
  height := height_176
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_176
def height_179 : ℕ := 5
def childrenH_179 : Fin 2 → ℕ := ![height_5, height_178]
theorem height_exact_179 : height_179 = 1 + Finset.univ.sup childrenH_179 := by decide +kernel
theorem required_origin_179 : ∀ x ∈ required_179,
    (∃ j, x ∈ childrenC_179 j) ∨ ∀ j, x ∈ childrenD_179 j := by decide +kernel
theorem required_exact_179 : required_179 =
    ((Finset.univ.biUnion childrenC_179) ∪ commonEnvelope childrenD_179).erase (1, 3) := by
  exact required_eq_combination childrenC_179 childrenD_179 (1, 3) required_179
    (by decide +kernel) child_required_sub_179 common_sub_179 required_origin_179
theorem envelope_origin_179 : ∀ x ∈ envelope_179,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_179 j := by decide +kernel
theorem envelope_exact_179 : envelope_179 =
    insert (1, 3) (Finset.univ.biUnion childrenD_179) := by
  exact envelope_eq_combination childrenD_179 (1, 3) envelope_179
    pivot_mem_179 child_envelope_sub_179 envelope_origin_179
def checked_179 : CheckedCard where
  required := required_179
  envelope := envelope_179
  height := height_179
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_179
end SnakyPrototype.Certificate21

end OAI
