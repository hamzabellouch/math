import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_67 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_67 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_67 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_8), (placed21 3 (0, 4) required_32)]
def childrenD_67 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_8), (placed21 3 (0, 4) envelope_32)]
theorem common_sub_67 : commonEnvelope childrenD_67 ⊆ insert (1, 1) required_67 := by decide +kernel
theorem child_required_sub_67 : ∀ j, childrenC_67 j ⊆ insert (1, 1) required_67 := by decide +kernel
theorem child_envelope_sub_67 : ∀ j, childrenD_67 j ⊆ envelope_67 := by decide +kernel
theorem pivot_mem_67 : (1, 1) ∈ envelope_67 := by decide +kernel
theorem children_work_67 : ∀ j, Template HasSnaky 3 (childrenC_67 j) (childrenD_67 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 3 (0, 4)).mono (by decide +kernel)
theorem row_works_67 : Template HasSnaky 4 required_67 envelope_67 := by
  refine compose HasSnaky 3 childrenC_67 childrenD_67 children_work_67 (1, 1)
    required_67 envelope_67 pivot_mem_67 child_required_sub_67 child_envelope_sub_67 ?_
  intro b hb
  exact common_sub_67 (mem_commonEnvelope childrenD_67 b hb)
def required_73 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_73 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_73 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), (placed21 0 (1, 0) required_52)]
def childrenD_73 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), (placed21 0 (1, 0) envelope_52)]
theorem common_sub_73 : commonEnvelope childrenD_73 ⊆ insert (2, 3) required_73 := by decide +kernel
theorem child_required_sub_73 : ∀ j, childrenC_73 j ⊆ insert (2, 3) required_73 := by decide +kernel
theorem child_envelope_sub_73 : ∀ j, childrenD_73 j ⊆ envelope_73 := by decide +kernel
theorem pivot_mem_73 : (2, 3) ∈ envelope_73 := by decide +kernel
theorem children_work_73 : ∀ j, Template HasSnaky 3 (childrenC_73 j) (childrenD_73 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (1, 0)).mono (by decide +kernel)
theorem row_works_73 : Template HasSnaky 4 required_73 envelope_73 := by
  refine compose HasSnaky 3 childrenC_73 childrenD_73 children_work_73 (2, 3)
    required_73 envelope_73 pivot_mem_73 child_required_sub_73 child_envelope_sub_73 ?_
  intro b hb
  exact common_sub_73 (mem_commonEnvelope childrenD_73 b hb)
def required_75 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_75 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_75 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_20), (placed21 6 (1, 5) required_23)]
def childrenD_75 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_20), (placed21 6 (1, 5) envelope_23)]
theorem common_sub_75 : commonEnvelope childrenD_75 ⊆ insert (0, 4) required_75 := by decide +kernel
theorem child_required_sub_75 : ∀ j, childrenC_75 j ⊆ insert (0, 4) required_75 := by decide +kernel
theorem child_envelope_sub_75 : ∀ j, childrenD_75 j ⊆ envelope_75 := by decide +kernel
theorem pivot_mem_75 : (0, 4) ∈ envelope_75 := by decide +kernel
theorem children_work_75 : ∀ j, Template HasSnaky 3 (childrenC_75 j) (childrenD_75 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_23 6 (1, 5)).mono (by decide +kernel)
theorem row_works_75 : Template HasSnaky 4 required_75 envelope_75 := by
  refine compose HasSnaky 3 childrenC_75 childrenD_75 children_work_75 (0, 4)
    required_75 envelope_75 pivot_mem_75 child_required_sub_75 child_envelope_sub_75 ?_
  intro b hb
  exact common_sub_75 (mem_commonEnvelope childrenD_75 b hb)
def required_79 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_79 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_79 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) required_8), (placed21 7 (4, 4) required_78)]
def childrenD_79 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) envelope_8), (placed21 7 (4, 4) envelope_78)]
theorem common_sub_79 : commonEnvelope childrenD_79 ⊆ insert (3, 4) required_79 := by decide +kernel
theorem child_required_sub_79 : ∀ j, childrenC_79 j ⊆ insert (3, 4) required_79 := by decide +kernel
theorem child_envelope_sub_79 : ∀ j, childrenD_79 j ⊆ envelope_79 := by decide +kernel
theorem pivot_mem_79 : (3, 4) ∈ envelope_79 := by decide +kernel
theorem children_work_79 : ∀ j, Template HasSnaky 3 (childrenC_79 j) (childrenD_79 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 7 (4, 4)).mono (by decide +kernel)
theorem row_works_79 : Template HasSnaky 4 required_79 envelope_79 := by
  refine compose HasSnaky 3 childrenC_79 childrenD_79 children_work_79 (3, 4)
    required_79 envelope_79 pivot_mem_79 child_required_sub_79 child_envelope_sub_79 ?_
  intro b hb
  exact common_sub_79 (mem_commonEnvelope childrenD_79 b hb)
def required_82 : Finset Cell := ⟨(([(1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_82 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_82 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) required_52), (placed21 1 (0, 2) required_64)]
def childrenD_82 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) envelope_52), (placed21 1 (0, 2) envelope_64)]
theorem common_sub_82 : commonEnvelope childrenD_82 ⊆ insert (4, 3) required_82 := by decide +kernel
theorem child_required_sub_82 : ∀ j, childrenC_82 j ⊆ insert (4, 3) required_82 := by decide +kernel
theorem child_envelope_sub_82 : ∀ j, childrenD_82 j ⊆ envelope_82 := by decide +kernel
theorem pivot_mem_82 : (4, 3) ∈ envelope_82 := by decide +kernel
theorem children_work_82 : ∀ j, Template HasSnaky 3 (childrenC_82 j) (childrenD_82 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_64 1 (0, 2)).mono (by decide +kernel)
theorem row_works_82 : Template HasSnaky 4 required_82 envelope_82 := by
  refine compose HasSnaky 3 childrenC_82 childrenD_82 children_work_82 (4, 3)
    required_82 envelope_82 pivot_mem_82 child_required_sub_82 child_envelope_sub_82 ?_
  intro b hb
  exact common_sub_82 (mem_commonEnvelope childrenD_82 b hb)
def required_86 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_86 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_86 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_2), (placed21 7 (4, 4) required_78)]
def childrenD_86 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_2), (placed21 7 (4, 4) envelope_78)]
theorem common_sub_86 : commonEnvelope childrenD_86 ⊆ insert (1, 2) required_86 := by decide +kernel
theorem child_required_sub_86 : ∀ j, childrenC_86 j ⊆ insert (1, 2) required_86 := by decide +kernel
theorem child_envelope_sub_86 : ∀ j, childrenD_86 j ⊆ envelope_86 := by decide +kernel
theorem pivot_mem_86 : (1, 2) ∈ envelope_86 := by decide +kernel
theorem children_work_86 : ∀ j, Template HasSnaky 3 (childrenC_86 j) (childrenD_86 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 7 (4, 4)).mono (by decide +kernel)
theorem row_works_86 : Template HasSnaky 4 required_86 envelope_86 := by
  refine compose HasSnaky 3 childrenC_86 childrenD_86 children_work_86 (1, 2)
    required_86 envelope_86 pivot_mem_86 child_required_sub_86 child_envelope_sub_86 ?_
  intro b hb
  exact common_sub_86 (mem_commonEnvelope childrenD_86 b hb)
def required_88 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_88 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_88 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) required_52), (placed21 0 (2, 0) required_53)]
def childrenD_88 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) envelope_52), (placed21 0 (2, 0) envelope_53)]
theorem common_sub_88 : commonEnvelope childrenD_88 ⊆ insert (3, 4) required_88 := by decide +kernel
theorem child_required_sub_88 : ∀ j, childrenC_88 j ⊆ insert (3, 4) required_88 := by decide +kernel
theorem child_envelope_sub_88 : ∀ j, childrenD_88 j ⊆ envelope_88 := by decide +kernel
theorem pivot_mem_88 : (3, 4) ∈ envelope_88 := by decide +kernel
theorem children_work_88 : ∀ j, Template HasSnaky 3 (childrenC_88 j) (childrenD_88 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 0 (2, 0)).mono (by decide +kernel)
theorem row_works_88 : Template HasSnaky 4 required_88 envelope_88 := by
  refine compose HasSnaky 3 childrenC_88 childrenD_88 children_work_88 (3, 4)
    required_88 envelope_88 pivot_mem_88 child_required_sub_88 child_envelope_sub_88 ?_
  intro b hb
  exact common_sub_88 (mem_commonEnvelope childrenD_88 b hb)
def required_89 : Finset Cell := ⟨(([(0, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_89 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_89 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 0 (1, 0) required_7)]
def childrenD_89 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 0 (1, 0) envelope_7)]
theorem common_sub_89 : commonEnvelope childrenD_89 ⊆ insert (1, 4) required_89 := by decide +kernel
theorem child_required_sub_89 : ∀ j, childrenC_89 j ⊆ insert (1, 4) required_89 := by decide +kernel
theorem child_envelope_sub_89 : ∀ j, childrenD_89 j ⊆ envelope_89 := by decide +kernel
theorem pivot_mem_89 : (1, 4) ∈ envelope_89 := by decide +kernel
theorem children_work_89 : ∀ j, Template HasSnaky 3 (childrenC_89 j) (childrenD_89 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
theorem row_works_89 : Template HasSnaky 4 required_89 envelope_89 := by
  refine compose HasSnaky 3 childrenC_89 childrenD_89 children_work_89 (1, 4)
    required_89 envelope_89 pivot_mem_89 child_required_sub_89 child_envelope_sub_89 ?_
  intro b hb
  exact common_sub_89 (mem_commonEnvelope childrenD_89 b hb)
def required_90 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_90 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_90 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) required_6), (placed21 1 (1, 0) required_37)]
def childrenD_90 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) envelope_6), (placed21 1 (1, 0) envelope_37)]
theorem common_sub_90 : commonEnvelope childrenD_90 ⊆ insert (4, 1) required_90 := by decide +kernel
theorem child_required_sub_90 : ∀ j, childrenC_90 j ⊆ insert (4, 1) required_90 := by decide +kernel
theorem child_envelope_sub_90 : ∀ j, childrenD_90 j ⊆ envelope_90 := by decide +kernel
theorem pivot_mem_90 : (4, 1) ∈ envelope_90 := by decide +kernel
theorem children_work_90 : ∀ j, Template HasSnaky 3 (childrenC_90 j) (childrenD_90 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 1 (1, 0)).mono (by decide +kernel)
theorem row_works_90 : Template HasSnaky 4 required_90 envelope_90 := by
  refine compose HasSnaky 3 childrenC_90 childrenD_90 children_work_90 (4, 1)
    required_90 envelope_90 pivot_mem_90 child_required_sub_90 child_envelope_sub_90 ?_
  intro b hb
  exact common_sub_90 (mem_commonEnvelope childrenD_90 b hb)
def required_91 : Finset Cell := ⟨(([(0, 0), (1, 1), (1, 2), (1, 3), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_91 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_91 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 0 (1, 1) required_16)]
def childrenD_91 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 0 (1, 1) envelope_16)]
theorem common_sub_91 : commonEnvelope childrenD_91 ⊆ insert (1, 4) required_91 := by decide +kernel
theorem child_required_sub_91 : ∀ j, childrenC_91 j ⊆ insert (1, 4) required_91 := by decide +kernel
theorem child_envelope_sub_91 : ∀ j, childrenD_91 j ⊆ envelope_91 := by decide +kernel
theorem pivot_mem_91 : (1, 4) ∈ envelope_91 := by decide +kernel
theorem children_work_91 : ∀ j, Template HasSnaky 3 (childrenC_91 j) (childrenD_91 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 0 (1, 1)).mono (by decide +kernel)
theorem row_works_91 : Template HasSnaky 4 required_91 envelope_91 := by
  refine compose HasSnaky 3 childrenC_91 childrenD_91 children_work_91 (1, 4)
    required_91 envelope_91 pivot_mem_91 child_required_sub_91 child_envelope_sub_91 ?_
  intro b hb
  exact common_sub_91 (mem_commonEnvelope childrenD_91 b hb)
def required_92 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_92 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_92 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), required_69]
def childrenD_92 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), envelope_69]
theorem common_sub_92 : commonEnvelope childrenD_92 ⊆ insert (3, 3) required_92 := by decide +kernel
theorem child_required_sub_92 : ∀ j, childrenC_92 j ⊆ insert (3, 3) required_92 := by decide +kernel
theorem child_envelope_sub_92 : ∀ j, childrenD_92 j ⊆ envelope_92 := by decide +kernel
theorem pivot_mem_92 : (3, 3) ∈ envelope_92 := by decide +kernel
theorem children_work_92 : ∀ j, Template HasSnaky 3 (childrenC_92 j) (childrenD_92 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_69.mono (by decide +kernel)
theorem row_works_92 : Template HasSnaky 4 required_92 envelope_92 := by
  refine compose HasSnaky 3 childrenC_92 childrenD_92 children_work_92 (3, 3)
    required_92 envelope_92 pivot_mem_92 child_required_sub_92 child_envelope_sub_92 ?_
  intro b hb
  exact common_sub_92 (mem_commonEnvelope childrenD_92 b hb)
def required_93 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_93 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_93 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_6), (placed21 3 (1, 1) required_21)]
def childrenD_93 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_6), (placed21 3 (1, 1) envelope_21)]
theorem common_sub_93 : commonEnvelope childrenD_93 ⊆ insert (4, 1) required_93 := by decide +kernel
theorem child_required_sub_93 : ∀ j, childrenC_93 j ⊆ insert (4, 1) required_93 := by decide +kernel
theorem child_envelope_sub_93 : ∀ j, childrenD_93 j ⊆ envelope_93 := by decide +kernel
theorem pivot_mem_93 : (4, 1) ∈ envelope_93 := by decide +kernel
theorem children_work_93 : ∀ j, Template HasSnaky 3 (childrenC_93 j) (childrenD_93 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_21 3 (1, 1)).mono (by decide +kernel)
theorem row_works_93 : Template HasSnaky 4 required_93 envelope_93 := by
  refine compose HasSnaky 3 childrenC_93 childrenD_93 children_work_93 (4, 1)
    required_93 envelope_93 pivot_mem_93 child_required_sub_93 child_envelope_sub_93 ?_
  intro b hb
  exact common_sub_93 (mem_commonEnvelope childrenD_93 b hb)
def required_97 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_97 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_97 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_24)]
def childrenD_97 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_24)]
theorem common_sub_97 : commonEnvelope childrenD_97 ⊆ insert (1, 2) required_97 := by decide +kernel
theorem child_required_sub_97 : ∀ j, childrenC_97 j ⊆ insert (1, 2) required_97 := by decide +kernel
theorem child_envelope_sub_97 : ∀ j, childrenD_97 j ⊆ envelope_97 := by decide +kernel
theorem pivot_mem_97 : (1, 2) ∈ envelope_97 := by decide +kernel
theorem children_work_97 : ∀ j, Template HasSnaky 3 (childrenC_97 j) (childrenD_97 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 1 (0, 1)).mono (by decide +kernel)
theorem row_works_97 : Template HasSnaky 4 required_97 envelope_97 := by
  refine compose HasSnaky 3 childrenC_97 childrenD_97 children_work_97 (1, 2)
    required_97 envelope_97 pivot_mem_97 child_required_sub_97 child_envelope_sub_97 ?_
  intro b hb
  exact common_sub_97 (mem_commonEnvelope childrenD_97 b hb)
def required_98 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (1, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_98 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_98 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_5), (placed21 0 (0, 1) required_16)]
def childrenD_98 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_5), (placed21 0 (0, 1) envelope_16)]
theorem common_sub_98 : commonEnvelope childrenD_98 ⊆ insert (0, 2) required_98 := by decide +kernel
theorem child_required_sub_98 : ∀ j, childrenC_98 j ⊆ insert (0, 2) required_98 := by decide +kernel
theorem child_envelope_sub_98 : ∀ j, childrenD_98 j ⊆ envelope_98 := by decide +kernel
theorem pivot_mem_98 : (0, 2) ∈ envelope_98 := by decide +kernel
theorem children_work_98 : ∀ j, Template HasSnaky 3 (childrenC_98 j) (childrenD_98 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 0 (0, 1)).mono (by decide +kernel)
theorem row_works_98 : Template HasSnaky 4 required_98 envelope_98 := by
  refine compose HasSnaky 3 childrenC_98 childrenD_98 children_work_98 (0, 2)
    required_98 envelope_98 pivot_mem_98 child_required_sub_98 child_envelope_sub_98 ?_
  intro b hb
  exact common_sub_98 (mem_commonEnvelope childrenD_98 b hb)
def required_99 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 1), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_99 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_99 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), (placed21 2 (3, 0) required_44)]
def childrenD_99 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), (placed21 2 (3, 0) envelope_44)]
theorem common_sub_99 : commonEnvelope childrenD_99 ⊆ insert (3, 2) required_99 := by decide +kernel
theorem child_required_sub_99 : ∀ j, childrenC_99 j ⊆ insert (3, 2) required_99 := by decide +kernel
theorem child_envelope_sub_99 : ∀ j, childrenD_99 j ⊆ envelope_99 := by decide +kernel
theorem pivot_mem_99 : (3, 2) ∈ envelope_99 := by decide +kernel
theorem children_work_99 : ∀ j, Template HasSnaky 3 (childrenC_99 j) (childrenD_99 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 2 (3, 0)).mono (by decide +kernel)
theorem row_works_99 : Template HasSnaky 4 required_99 envelope_99 := by
  refine compose HasSnaky 3 childrenC_99 childrenD_99 children_work_99 (3, 2)
    required_99 envelope_99 pivot_mem_99 child_required_sub_99 child_envelope_sub_99 ?_
  intro b hb
  exact common_sub_99 (mem_commonEnvelope childrenD_99 b hb)
def required_106 : Finset Cell := ⟨(([(0, 0), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_106 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_106 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 0 (1, 0) required_7)]
def childrenD_106 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 0 (1, 0) envelope_7)]
theorem common_sub_106 : commonEnvelope childrenD_106 ⊆ insert (1, 1) required_106 := by decide +kernel
theorem child_required_sub_106 : ∀ j, childrenC_106 j ⊆ insert (1, 1) required_106 := by decide +kernel
theorem child_envelope_sub_106 : ∀ j, childrenD_106 j ⊆ envelope_106 := by decide +kernel
theorem pivot_mem_106 : (1, 1) ∈ envelope_106 := by decide +kernel
theorem children_work_106 : ∀ j, Template HasSnaky 3 (childrenC_106 j) (childrenD_106 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
theorem row_works_106 : Template HasSnaky 4 required_106 envelope_106 := by
  refine compose HasSnaky 3 childrenC_106 childrenD_106 children_work_106 (1, 1)
    required_106 envelope_106 pivot_mem_106 child_required_sub_106 child_envelope_sub_106 ?_
  intro b hb
  exact common_sub_106 (mem_commonEnvelope childrenD_106 b hb)
def required_109 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_109 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_109 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), (placed21 2 (3, 0) required_44)]
def childrenD_109 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), (placed21 2 (3, 0) envelope_44)]
theorem common_sub_109 : commonEnvelope childrenD_109 ⊆ insert (2, 3) required_109 := by decide +kernel
theorem child_required_sub_109 : ∀ j, childrenC_109 j ⊆ insert (2, 3) required_109 := by decide +kernel
theorem child_envelope_sub_109 : ∀ j, childrenD_109 j ⊆ envelope_109 := by decide +kernel
theorem pivot_mem_109 : (2, 3) ∈ envelope_109 := by decide +kernel
theorem children_work_109 : ∀ j, Template HasSnaky 3 (childrenC_109 j) (childrenD_109 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 2 (3, 0)).mono (by decide +kernel)
theorem row_works_109 : Template HasSnaky 4 required_109 envelope_109 := by
  refine compose HasSnaky 3 childrenC_109 childrenD_109 children_work_109 (2, 3)
    required_109 envelope_109 pivot_mem_109 child_required_sub_109 child_envelope_sub_109 ?_
  intro b hb
  exact common_sub_109 (mem_commonEnvelope childrenD_109 b hb)
def required_112 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_112 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (4, 2), (4, 3), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_112 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) required_34), (placed21 0 (1, 0) required_44)]
def childrenD_112 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) envelope_34), (placed21 0 (1, 0) envelope_44)]
theorem common_sub_112 : commonEnvelope childrenD_112 ⊆ insert (2, 3) required_112 := by decide +kernel
theorem child_required_sub_112 : ∀ j, childrenC_112 j ⊆ insert (2, 3) required_112 := by decide +kernel
theorem child_envelope_sub_112 : ∀ j, childrenD_112 j ⊆ envelope_112 := by decide +kernel
theorem pivot_mem_112 : (2, 3) ∈ envelope_112 := by decide +kernel
theorem children_work_112 : ∀ j, Template HasSnaky 3 (childrenC_112 j) (childrenD_112 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 0 (1, 0)).mono (by decide +kernel)
theorem row_works_112 : Template HasSnaky 4 required_112 envelope_112 := by
  refine compose HasSnaky 3 childrenC_112 childrenD_112 children_work_112 (2, 3)
    required_112 envelope_112 pivot_mem_112 child_required_sub_112 child_envelope_sub_112 ?_
  intro b hb
  exact common_sub_112 (mem_commonEnvelope childrenD_112 b hb)
def required_125 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_125 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_125 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), required_124]
def childrenD_125 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), envelope_124]
theorem common_sub_125 : commonEnvelope childrenD_125 ⊆ insert (1, 2) required_125 := by decide +kernel
theorem child_required_sub_125 : ∀ j, childrenC_125 j ⊆ insert (1, 2) required_125 := by decide +kernel
theorem child_envelope_sub_125 : ∀ j, childrenD_125 j ⊆ envelope_125 := by decide +kernel
theorem pivot_mem_125 : (1, 2) ∈ envelope_125 := by decide +kernel
theorem children_work_125 : ∀ j, Template HasSnaky 3 (childrenC_125 j) (childrenD_125 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact row_works_124.mono (by decide +kernel)
theorem row_works_125 : Template HasSnaky 4 required_125 envelope_125 := by
  refine compose HasSnaky 3 childrenC_125 childrenD_125 children_work_125 (1, 2)
    required_125 envelope_125 pivot_mem_125 child_required_sub_125 child_envelope_sub_125 ?_
  intro b hb
  exact common_sub_125 (mem_commonEnvelope childrenD_125 b hb)
def required_127 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_127 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_127 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) required_7), (placed21 1 (0, 2) required_24), (placed21 0 (0, 1) required_124)]
def childrenD_127 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) envelope_7), (placed21 1 (0, 2) envelope_24), (placed21 0 (0, 1) envelope_124)]
theorem common_sub_127 : commonEnvelope childrenD_127 ⊆ insert (1, 5) required_127 := by decide +kernel
theorem child_required_sub_127 : ∀ j, childrenC_127 j ⊆ insert (1, 5) required_127 := by decide +kernel
theorem child_envelope_sub_127 : ∀ j, childrenD_127 j ⊆ envelope_127 := by decide +kernel
theorem pivot_mem_127 : (1, 5) ∈ envelope_127 := by decide +kernel
theorem children_work_127 : ∀ j, Template HasSnaky 3 (childrenC_127 j) (childrenD_127 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_124 0 (0, 1)).mono (by decide +kernel)
theorem row_works_127 : Template HasSnaky 4 required_127 envelope_127 := by
  refine compose HasSnaky 3 childrenC_127 childrenD_127 children_work_127 (1, 5)
    required_127 envelope_127 pivot_mem_127 child_required_sub_127 child_envelope_sub_127 ?_
  intro b hb
  exact common_sub_127 (mem_commonEnvelope childrenD_127 b hb)
def required_128 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_128 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_128 : Fin 3 → Finset Cell := ![(placed21 4 (0, 6) required_9), (placed21 2 (1, 2) required_16), (placed21 0 (0, 1) required_124)]
def childrenD_128 : Fin 3 → Finset Cell := ![(placed21 4 (0, 6) envelope_9), (placed21 2 (1, 2) envelope_16), (placed21 0 (0, 1) envelope_124)]
theorem common_sub_128 : commonEnvelope childrenD_128 ⊆ insert (1, 5) required_128 := by decide +kernel
theorem child_required_sub_128 : ∀ j, childrenC_128 j ⊆ insert (1, 5) required_128 := by decide +kernel
theorem child_envelope_sub_128 : ∀ j, childrenD_128 j ⊆ envelope_128 := by decide +kernel
theorem pivot_mem_128 : (1, 5) ∈ envelope_128 := by decide +kernel
theorem children_work_128 : ∀ j, Template HasSnaky 3 (childrenC_128 j) (childrenD_128 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 2 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_124 0 (0, 1)).mono (by decide +kernel)
theorem row_works_128 : Template HasSnaky 4 required_128 envelope_128 := by
  refine compose HasSnaky 3 childrenC_128 childrenD_128 children_work_128 (1, 5)
    required_128 envelope_128 pivot_mem_128 child_required_sub_128 child_envelope_sub_128 ?_
  intro b hb
  exact common_sub_128 (mem_commonEnvelope childrenD_128 b hb)
def required_132 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_132 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_132 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_5), (placed21 0 (1, 0) required_131)]
def childrenD_132 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_131)]
theorem common_sub_132 : commonEnvelope childrenD_132 ⊆ insert (1, 3) required_132 := by decide +kernel
theorem child_required_sub_132 : ∀ j, childrenC_132 j ⊆ insert (1, 3) required_132 := by decide +kernel
theorem child_envelope_sub_132 : ∀ j, childrenD_132 j ⊆ envelope_132 := by decide +kernel
theorem pivot_mem_132 : (1, 3) ∈ envelope_132 := by decide +kernel
theorem children_work_132 : ∀ j, Template HasSnaky 3 (childrenC_132 j) (childrenD_132 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_131 0 (1, 0)).mono (by decide +kernel)
theorem row_works_132 : Template HasSnaky 4 required_132 envelope_132 := by
  refine compose HasSnaky 3 childrenC_132 childrenD_132 children_work_132 (1, 3)
    required_132 envelope_132 pivot_mem_132 child_required_sub_132 child_envelope_sub_132 ?_
  intro b hb
  exact common_sub_132 (mem_commonEnvelope childrenD_132 b hb)
def required_141 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_141 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_141 : Fin 3 → Finset Cell := ![required_53, (placed21 6 (1, 6) required_53), (placed21 1 (0, 2) required_76)]
def childrenD_141 : Fin 3 → Finset Cell := ![envelope_53, (placed21 6 (1, 6) envelope_53), (placed21 1 (0, 2) envelope_76)]
theorem common_sub_141 : commonEnvelope childrenD_141 ⊆ insert (1, 4) required_141 := by decide +kernel
theorem child_required_sub_141 : ∀ j, childrenC_141 j ⊆ insert (1, 4) required_141 := by decide +kernel
theorem child_envelope_sub_141 : ∀ j, childrenD_141 j ⊆ envelope_141 := by decide +kernel
theorem pivot_mem_141 : (1, 4) ∈ envelope_141 := by decide +kernel
theorem children_work_141 : ∀ j, Template HasSnaky 3 (childrenC_141 j) (childrenD_141 j) := by
  intro j
  fin_cases j
  · exact row_works_53.mono (by decide +kernel)
  · exact (placed21_template row_works_53 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_76 1 (0, 2)).mono (by decide +kernel)
theorem row_works_141 : Template HasSnaky 4 required_141 envelope_141 := by
  refine compose HasSnaky 3 childrenC_141 childrenD_141 children_work_141 (1, 4)
    required_141 envelope_141 pivot_mem_141 child_required_sub_141 child_envelope_sub_141 ?_
  intro b hb
  exact common_sub_141 (mem_commonEnvelope childrenD_141 b hb)
def required_148 : Finset Cell := ⟨(([(0, 0), (1, 1), (1, 2), (1, 3), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_148 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_148 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 0 (1, 1) required_21)]
def childrenD_148 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 0 (1, 1) envelope_21)]
theorem common_sub_148 : commonEnvelope childrenD_148 ⊆ insert (1, 4) required_148 := by decide +kernel
theorem child_required_sub_148 : ∀ j, childrenC_148 j ⊆ insert (1, 4) required_148 := by decide +kernel
theorem child_envelope_sub_148 : ∀ j, childrenD_148 j ⊆ envelope_148 := by decide +kernel
theorem pivot_mem_148 : (1, 4) ∈ envelope_148 := by decide +kernel
theorem children_work_148 : ∀ j, Template HasSnaky 3 (childrenC_148 j) (childrenD_148 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_21 0 (1, 1)).mono (by decide +kernel)
theorem row_works_148 : Template HasSnaky 4 required_148 envelope_148 := by
  refine compose HasSnaky 3 childrenC_148 childrenD_148 children_work_148 (1, 4)
    required_148 envelope_148 pivot_mem_148 child_required_sub_148 child_envelope_sub_148 ?_
  intro b hb
  exact common_sub_148 (mem_commonEnvelope childrenD_148 b hb)
def height_67 : ℕ := 4
def childrenH_67 : Fin 2 → ℕ := ![height_8, height_32]
theorem height_exact_67 : height_67 = 1 + Finset.univ.sup childrenH_67 := by decide +kernel
theorem required_origin_67 : ∀ x ∈ required_67,
    (∃ j, x ∈ childrenC_67 j) ∨ ∀ j, x ∈ childrenD_67 j := by decide +kernel
theorem required_exact_67 : required_67 =
    ((Finset.univ.biUnion childrenC_67) ∪ commonEnvelope childrenD_67).erase (1, 1) := by
  exact required_eq_combination childrenC_67 childrenD_67 (1, 1) required_67
    (by decide +kernel) child_required_sub_67 common_sub_67 required_origin_67
theorem envelope_origin_67 : ∀ x ∈ envelope_67,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_67 j := by decide +kernel
theorem envelope_exact_67 : envelope_67 =
    insert (1, 1) (Finset.univ.biUnion childrenD_67) := by
  exact envelope_eq_combination childrenD_67 (1, 1) envelope_67
    pivot_mem_67 child_envelope_sub_67 envelope_origin_67
def checked_67 : CheckedCard where
  required := required_67
  envelope := envelope_67
  height := height_67
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_67
def height_73 : ℕ := 4
def childrenH_73 : Fin 2 → ℕ := ![height_0, height_52]
theorem height_exact_73 : height_73 = 1 + Finset.univ.sup childrenH_73 := by decide +kernel
theorem required_origin_73 : ∀ x ∈ required_73,
    (∃ j, x ∈ childrenC_73 j) ∨ ∀ j, x ∈ childrenD_73 j := by decide +kernel
theorem required_exact_73 : required_73 =
    ((Finset.univ.biUnion childrenC_73) ∪ commonEnvelope childrenD_73).erase (2, 3) := by
  exact required_eq_combination childrenC_73 childrenD_73 (2, 3) required_73
    (by decide +kernel) child_required_sub_73 common_sub_73 required_origin_73
theorem envelope_origin_73 : ∀ x ∈ envelope_73,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_73 j := by decide +kernel
theorem envelope_exact_73 : envelope_73 =
    insert (2, 3) (Finset.univ.biUnion childrenD_73) := by
  exact envelope_eq_combination childrenD_73 (2, 3) envelope_73
    pivot_mem_73 child_envelope_sub_73 envelope_origin_73
def checked_73 : CheckedCard where
  required := required_73
  envelope := envelope_73
  height := height_73
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_73
def height_75 : ℕ := 4
def childrenH_75 : Fin 2 → ℕ := ![height_20, height_23]
theorem height_exact_75 : height_75 = 1 + Finset.univ.sup childrenH_75 := by decide +kernel
theorem required_origin_75 : ∀ x ∈ required_75,
    (∃ j, x ∈ childrenC_75 j) ∨ ∀ j, x ∈ childrenD_75 j := by decide +kernel
theorem required_exact_75 : required_75 =
    ((Finset.univ.biUnion childrenC_75) ∪ commonEnvelope childrenD_75).erase (0, 4) := by
  exact required_eq_combination childrenC_75 childrenD_75 (0, 4) required_75
    (by decide +kernel) child_required_sub_75 common_sub_75 required_origin_75
theorem envelope_origin_75 : ∀ x ∈ envelope_75,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_75 j := by decide +kernel
theorem envelope_exact_75 : envelope_75 =
    insert (0, 4) (Finset.univ.biUnion childrenD_75) := by
  exact envelope_eq_combination childrenD_75 (0, 4) envelope_75
    pivot_mem_75 child_envelope_sub_75 envelope_origin_75
def checked_75 : CheckedCard where
  required := required_75
  envelope := envelope_75
  height := height_75
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_75
def height_79 : ℕ := 4
def childrenH_79 : Fin 2 → ℕ := ![height_8, height_78]
theorem height_exact_79 : height_79 = 1 + Finset.univ.sup childrenH_79 := by decide +kernel
theorem required_origin_79 : ∀ x ∈ required_79,
    (∃ j, x ∈ childrenC_79 j) ∨ ∀ j, x ∈ childrenD_79 j := by decide +kernel
theorem required_exact_79 : required_79 =
    ((Finset.univ.biUnion childrenC_79) ∪ commonEnvelope childrenD_79).erase (3, 4) := by
  exact required_eq_combination childrenC_79 childrenD_79 (3, 4) required_79
    (by decide +kernel) child_required_sub_79 common_sub_79 required_origin_79
theorem envelope_origin_79 : ∀ x ∈ envelope_79,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_79 j := by decide +kernel
theorem envelope_exact_79 : envelope_79 =
    insert (3, 4) (Finset.univ.biUnion childrenD_79) := by
  exact envelope_eq_combination childrenD_79 (3, 4) envelope_79
    pivot_mem_79 child_envelope_sub_79 envelope_origin_79
def checked_79 : CheckedCard where
  required := required_79
  envelope := envelope_79
  height := height_79
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_79
def height_82 : ℕ := 4
def childrenH_82 : Fin 2 → ℕ := ![height_52, height_64]
theorem height_exact_82 : height_82 = 1 + Finset.univ.sup childrenH_82 := by decide +kernel
theorem required_origin_82 : ∀ x ∈ required_82,
    (∃ j, x ∈ childrenC_82 j) ∨ ∀ j, x ∈ childrenD_82 j := by decide +kernel
theorem required_exact_82 : required_82 =
    ((Finset.univ.biUnion childrenC_82) ∪ commonEnvelope childrenD_82).erase (4, 3) := by
  exact required_eq_combination childrenC_82 childrenD_82 (4, 3) required_82
    (by decide +kernel) child_required_sub_82 common_sub_82 required_origin_82
theorem envelope_origin_82 : ∀ x ∈ envelope_82,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_82 j := by decide +kernel
theorem envelope_exact_82 : envelope_82 =
    insert (4, 3) (Finset.univ.biUnion childrenD_82) := by
  exact envelope_eq_combination childrenD_82 (4, 3) envelope_82
    pivot_mem_82 child_envelope_sub_82 envelope_origin_82
def checked_82 : CheckedCard where
  required := required_82
  envelope := envelope_82
  height := height_82
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_82
def height_86 : ℕ := 4
def childrenH_86 : Fin 2 → ℕ := ![height_2, height_78]
theorem height_exact_86 : height_86 = 1 + Finset.univ.sup childrenH_86 := by decide +kernel
theorem required_origin_86 : ∀ x ∈ required_86,
    (∃ j, x ∈ childrenC_86 j) ∨ ∀ j, x ∈ childrenD_86 j := by decide +kernel
theorem required_exact_86 : required_86 =
    ((Finset.univ.biUnion childrenC_86) ∪ commonEnvelope childrenD_86).erase (1, 2) := by
  exact required_eq_combination childrenC_86 childrenD_86 (1, 2) required_86
    (by decide +kernel) child_required_sub_86 common_sub_86 required_origin_86
theorem envelope_origin_86 : ∀ x ∈ envelope_86,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_86 j := by decide +kernel
theorem envelope_exact_86 : envelope_86 =
    insert (1, 2) (Finset.univ.biUnion childrenD_86) := by
  exact envelope_eq_combination childrenD_86 (1, 2) envelope_86
    pivot_mem_86 child_envelope_sub_86 envelope_origin_86
def checked_86 : CheckedCard where
  required := required_86
  envelope := envelope_86
  height := height_86
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_86
def height_88 : ℕ := 4
def childrenH_88 : Fin 2 → ℕ := ![height_52, height_53]
theorem height_exact_88 : height_88 = 1 + Finset.univ.sup childrenH_88 := by decide +kernel
theorem required_origin_88 : ∀ x ∈ required_88,
    (∃ j, x ∈ childrenC_88 j) ∨ ∀ j, x ∈ childrenD_88 j := by decide +kernel
theorem required_exact_88 : required_88 =
    ((Finset.univ.biUnion childrenC_88) ∪ commonEnvelope childrenD_88).erase (3, 4) := by
  exact required_eq_combination childrenC_88 childrenD_88 (3, 4) required_88
    (by decide +kernel) child_required_sub_88 common_sub_88 required_origin_88
theorem envelope_origin_88 : ∀ x ∈ envelope_88,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_88 j := by decide +kernel
theorem envelope_exact_88 : envelope_88 =
    insert (3, 4) (Finset.univ.biUnion childrenD_88) := by
  exact envelope_eq_combination childrenD_88 (3, 4) envelope_88
    pivot_mem_88 child_envelope_sub_88 envelope_origin_88
def checked_88 : CheckedCard where
  required := required_88
  envelope := envelope_88
  height := height_88
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_88
def height_89 : ℕ := 4
def childrenH_89 : Fin 2 → ℕ := ![height_4, height_7]
theorem height_exact_89 : height_89 = 1 + Finset.univ.sup childrenH_89 := by decide +kernel
theorem required_origin_89 : ∀ x ∈ required_89,
    (∃ j, x ∈ childrenC_89 j) ∨ ∀ j, x ∈ childrenD_89 j := by decide +kernel
theorem required_exact_89 : required_89 =
    ((Finset.univ.biUnion childrenC_89) ∪ commonEnvelope childrenD_89).erase (1, 4) := by
  exact required_eq_combination childrenC_89 childrenD_89 (1, 4) required_89
    (by decide +kernel) child_required_sub_89 common_sub_89 required_origin_89
theorem envelope_origin_89 : ∀ x ∈ envelope_89,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_89 j := by decide +kernel
theorem envelope_exact_89 : envelope_89 =
    insert (1, 4) (Finset.univ.biUnion childrenD_89) := by
  exact envelope_eq_combination childrenD_89 (1, 4) envelope_89
    pivot_mem_89 child_envelope_sub_89 envelope_origin_89
def checked_89 : CheckedCard where
  required := required_89
  envelope := envelope_89
  height := height_89
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_89
def height_90 : ℕ := 4
def childrenH_90 : Fin 2 → ℕ := ![height_6, height_37]
theorem height_exact_90 : height_90 = 1 + Finset.univ.sup childrenH_90 := by decide +kernel
theorem required_origin_90 : ∀ x ∈ required_90,
    (∃ j, x ∈ childrenC_90 j) ∨ ∀ j, x ∈ childrenD_90 j := by decide +kernel
theorem required_exact_90 : required_90 =
    ((Finset.univ.biUnion childrenC_90) ∪ commonEnvelope childrenD_90).erase (4, 1) := by
  exact required_eq_combination childrenC_90 childrenD_90 (4, 1) required_90
    (by decide +kernel) child_required_sub_90 common_sub_90 required_origin_90
theorem envelope_origin_90 : ∀ x ∈ envelope_90,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_90 j := by decide +kernel
theorem envelope_exact_90 : envelope_90 =
    insert (4, 1) (Finset.univ.biUnion childrenD_90) := by
  exact envelope_eq_combination childrenD_90 (4, 1) envelope_90
    pivot_mem_90 child_envelope_sub_90 envelope_origin_90
def checked_90 : CheckedCard where
  required := required_90
  envelope := envelope_90
  height := height_90
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_90
def height_91 : ℕ := 4
def childrenH_91 : Fin 2 → ℕ := ![height_4, height_16]
theorem height_exact_91 : height_91 = 1 + Finset.univ.sup childrenH_91 := by decide +kernel
theorem required_origin_91 : ∀ x ∈ required_91,
    (∃ j, x ∈ childrenC_91 j) ∨ ∀ j, x ∈ childrenD_91 j := by decide +kernel
theorem required_exact_91 : required_91 =
    ((Finset.univ.biUnion childrenC_91) ∪ commonEnvelope childrenD_91).erase (1, 4) := by
  exact required_eq_combination childrenC_91 childrenD_91 (1, 4) required_91
    (by decide +kernel) child_required_sub_91 common_sub_91 required_origin_91
theorem envelope_origin_91 : ∀ x ∈ envelope_91,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_91 j := by decide +kernel
theorem envelope_exact_91 : envelope_91 =
    insert (1, 4) (Finset.univ.biUnion childrenD_91) := by
  exact envelope_eq_combination childrenD_91 (1, 4) envelope_91
    pivot_mem_91 child_envelope_sub_91 envelope_origin_91
def checked_91 : CheckedCard where
  required := required_91
  envelope := envelope_91
  height := height_91
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_91
def height_92 : ℕ := 4
def childrenH_92 : Fin 2 → ℕ := ![height_5, height_69]
theorem height_exact_92 : height_92 = 1 + Finset.univ.sup childrenH_92 := by decide +kernel
theorem required_origin_92 : ∀ x ∈ required_92,
    (∃ j, x ∈ childrenC_92 j) ∨ ∀ j, x ∈ childrenD_92 j := by decide +kernel
theorem required_exact_92 : required_92 =
    ((Finset.univ.biUnion childrenC_92) ∪ commonEnvelope childrenD_92).erase (3, 3) := by
  exact required_eq_combination childrenC_92 childrenD_92 (3, 3) required_92
    (by decide +kernel) child_required_sub_92 common_sub_92 required_origin_92
theorem envelope_origin_92 : ∀ x ∈ envelope_92,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_92 j := by decide +kernel
theorem envelope_exact_92 : envelope_92 =
    insert (3, 3) (Finset.univ.biUnion childrenD_92) := by
  exact envelope_eq_combination childrenD_92 (3, 3) envelope_92
    pivot_mem_92 child_envelope_sub_92 envelope_origin_92
def checked_92 : CheckedCard where
  required := required_92
  envelope := envelope_92
  height := height_92
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_92
def height_93 : ℕ := 4
def childrenH_93 : Fin 2 → ℕ := ![height_6, height_21]
theorem height_exact_93 : height_93 = 1 + Finset.univ.sup childrenH_93 := by decide +kernel
theorem required_origin_93 : ∀ x ∈ required_93,
    (∃ j, x ∈ childrenC_93 j) ∨ ∀ j, x ∈ childrenD_93 j := by decide +kernel
theorem required_exact_93 : required_93 =
    ((Finset.univ.biUnion childrenC_93) ∪ commonEnvelope childrenD_93).erase (4, 1) := by
  exact required_eq_combination childrenC_93 childrenD_93 (4, 1) required_93
    (by decide +kernel) child_required_sub_93 common_sub_93 required_origin_93
theorem envelope_origin_93 : ∀ x ∈ envelope_93,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_93 j := by decide +kernel
theorem envelope_exact_93 : envelope_93 =
    insert (4, 1) (Finset.univ.biUnion childrenD_93) := by
  exact envelope_eq_combination childrenD_93 (4, 1) envelope_93
    pivot_mem_93 child_envelope_sub_93 envelope_origin_93
def checked_93 : CheckedCard where
  required := required_93
  envelope := envelope_93
  height := height_93
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_93
def height_97 : ℕ := 4
def childrenH_97 : Fin 2 → ℕ := ![height_5, height_24]
theorem height_exact_97 : height_97 = 1 + Finset.univ.sup childrenH_97 := by decide +kernel
theorem required_origin_97 : ∀ x ∈ required_97,
    (∃ j, x ∈ childrenC_97 j) ∨ ∀ j, x ∈ childrenD_97 j := by decide +kernel
theorem required_exact_97 : required_97 =
    ((Finset.univ.biUnion childrenC_97) ∪ commonEnvelope childrenD_97).erase (1, 2) := by
  exact required_eq_combination childrenC_97 childrenD_97 (1, 2) required_97
    (by decide +kernel) child_required_sub_97 common_sub_97 required_origin_97
theorem envelope_origin_97 : ∀ x ∈ envelope_97,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_97 j := by decide +kernel
theorem envelope_exact_97 : envelope_97 =
    insert (1, 2) (Finset.univ.biUnion childrenD_97) := by
  exact envelope_eq_combination childrenD_97 (1, 2) envelope_97
    pivot_mem_97 child_envelope_sub_97 envelope_origin_97
def checked_97 : CheckedCard where
  required := required_97
  envelope := envelope_97
  height := height_97
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_97
def height_98 : ℕ := 4
def childrenH_98 : Fin 2 → ℕ := ![height_5, height_16]
theorem height_exact_98 : height_98 = 1 + Finset.univ.sup childrenH_98 := by decide +kernel
theorem required_origin_98 : ∀ x ∈ required_98,
    (∃ j, x ∈ childrenC_98 j) ∨ ∀ j, x ∈ childrenD_98 j := by decide +kernel
theorem required_exact_98 : required_98 =
    ((Finset.univ.biUnion childrenC_98) ∪ commonEnvelope childrenD_98).erase (0, 2) := by
  exact required_eq_combination childrenC_98 childrenD_98 (0, 2) required_98
    (by decide +kernel) child_required_sub_98 common_sub_98 required_origin_98
theorem envelope_origin_98 : ∀ x ∈ envelope_98,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_98 j := by decide +kernel
theorem envelope_exact_98 : envelope_98 =
    insert (0, 2) (Finset.univ.biUnion childrenD_98) := by
  exact envelope_eq_combination childrenD_98 (0, 2) envelope_98
    pivot_mem_98 child_envelope_sub_98 envelope_origin_98
def checked_98 : CheckedCard where
  required := required_98
  envelope := envelope_98
  height := height_98
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_98
def height_99 : ℕ := 4
def childrenH_99 : Fin 2 → ℕ := ![height_5, height_44]
theorem height_exact_99 : height_99 = 1 + Finset.univ.sup childrenH_99 := by decide +kernel
theorem required_origin_99 : ∀ x ∈ required_99,
    (∃ j, x ∈ childrenC_99 j) ∨ ∀ j, x ∈ childrenD_99 j := by decide +kernel
theorem required_exact_99 : required_99 =
    ((Finset.univ.biUnion childrenC_99) ∪ commonEnvelope childrenD_99).erase (3, 2) := by
  exact required_eq_combination childrenC_99 childrenD_99 (3, 2) required_99
    (by decide +kernel) child_required_sub_99 common_sub_99 required_origin_99
theorem envelope_origin_99 : ∀ x ∈ envelope_99,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_99 j := by decide +kernel
theorem envelope_exact_99 : envelope_99 =
    insert (3, 2) (Finset.univ.biUnion childrenD_99) := by
  exact envelope_eq_combination childrenD_99 (3, 2) envelope_99
    pivot_mem_99 child_envelope_sub_99 envelope_origin_99
def checked_99 : CheckedCard where
  required := required_99
  envelope := envelope_99
  height := height_99
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_99
def height_106 : ℕ := 4
def childrenH_106 : Fin 2 → ℕ := ![height_4, height_7]
theorem height_exact_106 : height_106 = 1 + Finset.univ.sup childrenH_106 := by decide +kernel
theorem required_origin_106 : ∀ x ∈ required_106,
    (∃ j, x ∈ childrenC_106 j) ∨ ∀ j, x ∈ childrenD_106 j := by decide +kernel
theorem required_exact_106 : required_106 =
    ((Finset.univ.biUnion childrenC_106) ∪ commonEnvelope childrenD_106).erase (1, 1) := by
  exact required_eq_combination childrenC_106 childrenD_106 (1, 1) required_106
    (by decide +kernel) child_required_sub_106 common_sub_106 required_origin_106
theorem envelope_origin_106 : ∀ x ∈ envelope_106,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_106 j := by decide +kernel
theorem envelope_exact_106 : envelope_106 =
    insert (1, 1) (Finset.univ.biUnion childrenD_106) := by
  exact envelope_eq_combination childrenD_106 (1, 1) envelope_106
    pivot_mem_106 child_envelope_sub_106 envelope_origin_106
def checked_106 : CheckedCard where
  required := required_106
  envelope := envelope_106
  height := height_106
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_106
def height_109 : ℕ := 4
def childrenH_109 : Fin 2 → ℕ := ![height_5, height_44]
theorem height_exact_109 : height_109 = 1 + Finset.univ.sup childrenH_109 := by decide +kernel
theorem required_origin_109 : ∀ x ∈ required_109,
    (∃ j, x ∈ childrenC_109 j) ∨ ∀ j, x ∈ childrenD_109 j := by decide +kernel
theorem required_exact_109 : required_109 =
    ((Finset.univ.biUnion childrenC_109) ∪ commonEnvelope childrenD_109).erase (2, 3) := by
  exact required_eq_combination childrenC_109 childrenD_109 (2, 3) required_109
    (by decide +kernel) child_required_sub_109 common_sub_109 required_origin_109
theorem envelope_origin_109 : ∀ x ∈ envelope_109,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_109 j := by decide +kernel
theorem envelope_exact_109 : envelope_109 =
    insert (2, 3) (Finset.univ.biUnion childrenD_109) := by
  exact envelope_eq_combination childrenD_109 (2, 3) envelope_109
    pivot_mem_109 child_envelope_sub_109 envelope_origin_109
def checked_109 : CheckedCard where
  required := required_109
  envelope := envelope_109
  height := height_109
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_109
def height_112 : ℕ := 4
def childrenH_112 : Fin 2 → ℕ := ![height_34, height_44]
theorem height_exact_112 : height_112 = 1 + Finset.univ.sup childrenH_112 := by decide +kernel
theorem required_origin_112 : ∀ x ∈ required_112,
    (∃ j, x ∈ childrenC_112 j) ∨ ∀ j, x ∈ childrenD_112 j := by decide +kernel
theorem required_exact_112 : required_112 =
    ((Finset.univ.biUnion childrenC_112) ∪ commonEnvelope childrenD_112).erase (2, 3) := by
  exact required_eq_combination childrenC_112 childrenD_112 (2, 3) required_112
    (by decide +kernel) child_required_sub_112 common_sub_112 required_origin_112
theorem envelope_origin_112 : ∀ x ∈ envelope_112,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_112 j := by decide +kernel
theorem envelope_exact_112 : envelope_112 =
    insert (2, 3) (Finset.univ.biUnion childrenD_112) := by
  exact envelope_eq_combination childrenD_112 (2, 3) envelope_112
    pivot_mem_112 child_envelope_sub_112 envelope_origin_112
def checked_112 : CheckedCard where
  required := required_112
  envelope := envelope_112
  height := height_112
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_112
def height_125 : ℕ := 4
def childrenH_125 : Fin 2 → ℕ := ![height_5, height_124]
theorem height_exact_125 : height_125 = 1 + Finset.univ.sup childrenH_125 := by decide +kernel
theorem required_origin_125 : ∀ x ∈ required_125,
    (∃ j, x ∈ childrenC_125 j) ∨ ∀ j, x ∈ childrenD_125 j := by decide +kernel
theorem required_exact_125 : required_125 =
    ((Finset.univ.biUnion childrenC_125) ∪ commonEnvelope childrenD_125).erase (1, 2) := by
  exact required_eq_combination childrenC_125 childrenD_125 (1, 2) required_125
    (by decide +kernel) child_required_sub_125 common_sub_125 required_origin_125
theorem envelope_origin_125 : ∀ x ∈ envelope_125,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_125 j := by decide +kernel
theorem envelope_exact_125 : envelope_125 =
    insert (1, 2) (Finset.univ.biUnion childrenD_125) := by
  exact envelope_eq_combination childrenD_125 (1, 2) envelope_125
    pivot_mem_125 child_envelope_sub_125 envelope_origin_125
def checked_125 : CheckedCard where
  required := required_125
  envelope := envelope_125
  height := height_125
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_125
def height_127 : ℕ := 4
def childrenH_127 : Fin 3 → ℕ := ![height_7, height_24, height_124]
theorem height_exact_127 : height_127 = 1 + Finset.univ.sup childrenH_127 := by decide +kernel
theorem required_origin_127 : ∀ x ∈ required_127,
    (∃ j, x ∈ childrenC_127 j) ∨ ∀ j, x ∈ childrenD_127 j := by decide +kernel
theorem required_exact_127 : required_127 =
    ((Finset.univ.biUnion childrenC_127) ∪ commonEnvelope childrenD_127).erase (1, 5) := by
  exact required_eq_combination childrenC_127 childrenD_127 (1, 5) required_127
    (by decide +kernel) child_required_sub_127 common_sub_127 required_origin_127
theorem envelope_origin_127 : ∀ x ∈ envelope_127,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_127 j := by decide +kernel
theorem envelope_exact_127 : envelope_127 =
    insert (1, 5) (Finset.univ.biUnion childrenD_127) := by
  exact envelope_eq_combination childrenD_127 (1, 5) envelope_127
    pivot_mem_127 child_envelope_sub_127 envelope_origin_127
def checked_127 : CheckedCard where
  required := required_127
  envelope := envelope_127
  height := height_127
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_127
def height_128 : ℕ := 4
def childrenH_128 : Fin 3 → ℕ := ![height_9, height_16, height_124]
theorem height_exact_128 : height_128 = 1 + Finset.univ.sup childrenH_128 := by decide +kernel
theorem required_origin_128 : ∀ x ∈ required_128,
    (∃ j, x ∈ childrenC_128 j) ∨ ∀ j, x ∈ childrenD_128 j := by decide +kernel
theorem required_exact_128 : required_128 =
    ((Finset.univ.biUnion childrenC_128) ∪ commonEnvelope childrenD_128).erase (1, 5) := by
  exact required_eq_combination childrenC_128 childrenD_128 (1, 5) required_128
    (by decide +kernel) child_required_sub_128 common_sub_128 required_origin_128
theorem envelope_origin_128 : ∀ x ∈ envelope_128,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_128 j := by decide +kernel
theorem envelope_exact_128 : envelope_128 =
    insert (1, 5) (Finset.univ.biUnion childrenD_128) := by
  exact envelope_eq_combination childrenD_128 (1, 5) envelope_128
    pivot_mem_128 child_envelope_sub_128 envelope_origin_128
def checked_128 : CheckedCard where
  required := required_128
  envelope := envelope_128
  height := height_128
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_128
def height_132 : ℕ := 4
def childrenH_132 : Fin 2 → ℕ := ![height_5, height_131]
theorem height_exact_132 : height_132 = 1 + Finset.univ.sup childrenH_132 := by decide +kernel
theorem required_origin_132 : ∀ x ∈ required_132,
    (∃ j, x ∈ childrenC_132 j) ∨ ∀ j, x ∈ childrenD_132 j := by decide +kernel
theorem required_exact_132 : required_132 =
    ((Finset.univ.biUnion childrenC_132) ∪ commonEnvelope childrenD_132).erase (1, 3) := by
  exact required_eq_combination childrenC_132 childrenD_132 (1, 3) required_132
    (by decide +kernel) child_required_sub_132 common_sub_132 required_origin_132
theorem envelope_origin_132 : ∀ x ∈ envelope_132,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_132 j := by decide +kernel
theorem envelope_exact_132 : envelope_132 =
    insert (1, 3) (Finset.univ.biUnion childrenD_132) := by
  exact envelope_eq_combination childrenD_132 (1, 3) envelope_132
    pivot_mem_132 child_envelope_sub_132 envelope_origin_132
def checked_132 : CheckedCard where
  required := required_132
  envelope := envelope_132
  height := height_132
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_132
def height_141 : ℕ := 4
def childrenH_141 : Fin 3 → ℕ := ![height_53, height_53, height_76]
theorem height_exact_141 : height_141 = 1 + Finset.univ.sup childrenH_141 := by decide +kernel
theorem required_origin_141 : ∀ x ∈ required_141,
    (∃ j, x ∈ childrenC_141 j) ∨ ∀ j, x ∈ childrenD_141 j := by decide +kernel
theorem required_exact_141 : required_141 =
    ((Finset.univ.biUnion childrenC_141) ∪ commonEnvelope childrenD_141).erase (1, 4) := by
  exact required_eq_combination childrenC_141 childrenD_141 (1, 4) required_141
    (by decide +kernel) child_required_sub_141 common_sub_141 required_origin_141
theorem envelope_origin_141 : ∀ x ∈ envelope_141,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_141 j := by decide +kernel
theorem envelope_exact_141 : envelope_141 =
    insert (1, 4) (Finset.univ.biUnion childrenD_141) := by
  exact envelope_eq_combination childrenD_141 (1, 4) envelope_141
    pivot_mem_141 child_envelope_sub_141 envelope_origin_141
def checked_141 : CheckedCard where
  required := required_141
  envelope := envelope_141
  height := height_141
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_141
def height_148 : ℕ := 4
def childrenH_148 : Fin 2 → ℕ := ![height_4, height_21]
theorem height_exact_148 : height_148 = 1 + Finset.univ.sup childrenH_148 := by decide +kernel
theorem required_origin_148 : ∀ x ∈ required_148,
    (∃ j, x ∈ childrenC_148 j) ∨ ∀ j, x ∈ childrenD_148 j := by decide +kernel
theorem required_exact_148 : required_148 =
    ((Finset.univ.biUnion childrenC_148) ∪ commonEnvelope childrenD_148).erase (1, 4) := by
  exact required_eq_combination childrenC_148 childrenD_148 (1, 4) required_148
    (by decide +kernel) child_required_sub_148 common_sub_148 required_origin_148
theorem envelope_origin_148 : ∀ x ∈ envelope_148,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_148 j := by decide +kernel
theorem envelope_exact_148 : envelope_148 =
    insert (1, 4) (Finset.univ.biUnion childrenD_148) := by
  exact envelope_eq_combination childrenD_148 (1, 4) envelope_148
    pivot_mem_148 child_envelope_sub_148 envelope_origin_148
def checked_148 : CheckedCard where
  required := required_148
  envelope := envelope_148
  height := height_148
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_148
end SnakyPrototype.Certificate21

end OAI
