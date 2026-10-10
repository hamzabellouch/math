import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_7 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_7 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_6), (placed21 4 (0, 5) required_6)]
def childrenD_7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_6), (placed21 4 (0, 5) envelope_6)]
theorem common_sub_7 : commonEnvelope childrenD_7 ⊆ insert (0, 5) required_7 := by decide +kernel
theorem child_required_sub_7 : ∀ j, childrenC_7 j ⊆ insert (0, 5) required_7 := by decide +kernel
theorem child_envelope_sub_7 : ∀ j, childrenD_7 j ⊆ envelope_7 := by decide +kernel
theorem pivot_mem_7 : (0, 5) ∈ envelope_7 := by decide +kernel
theorem children_work_7 : ∀ j, Template HasSnaky 2 (childrenC_7 j) (childrenD_7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 4 (0, 5)).mono (by decide +kernel)
theorem row_works_7 : Template HasSnaky 3 required_7 envelope_7 := by
  refine compose HasSnaky 2 childrenC_7 childrenD_7 children_work_7 (0, 5)
    required_7 envelope_7 pivot_mem_7 child_required_sub_7 child_envelope_sub_7 ?_
  intro b hb
  exact common_sub_7 (mem_commonEnvelope childrenD_7 b hb)
def required_8 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_8 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_8 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_6), (placed21 3 (0, 1) required_6)]
def childrenD_8 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_6), (placed21 3 (0, 1) envelope_6)]
theorem common_sub_8 : commonEnvelope childrenD_8 ⊆ insert (4, 1) required_8 := by decide +kernel
theorem child_required_sub_8 : ∀ j, childrenC_8 j ⊆ insert (4, 1) required_8 := by decide +kernel
theorem child_envelope_sub_8 : ∀ j, childrenD_8 j ⊆ envelope_8 := by decide +kernel
theorem pivot_mem_8 : (4, 1) ∈ envelope_8 := by decide +kernel
theorem children_work_8 : ∀ j, Template HasSnaky 2 (childrenC_8 j) (childrenD_8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 3 (0, 1)).mono (by decide +kernel)
theorem row_works_8 : Template HasSnaky 3 required_8 envelope_8 := by
  refine compose HasSnaky 2 childrenC_8 childrenD_8 children_work_8 (4, 1)
    required_8 envelope_8 pivot_mem_8 child_required_sub_8 child_envelope_sub_8 ?_
  intro b hb
  exact common_sub_8 (mem_commonEnvelope childrenD_8 b hb)
def required_9 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_9 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_9 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) required_6), (placed21 6 (1, 5) required_6)]
def childrenD_9 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) envelope_6), (placed21 6 (1, 5) envelope_6)]
theorem common_sub_9 : commonEnvelope childrenD_9 ⊆ insert (1, 5) required_9 := by decide +kernel
theorem child_required_sub_9 : ∀ j, childrenC_9 j ⊆ insert (1, 5) required_9 := by decide +kernel
theorem child_envelope_sub_9 : ∀ j, childrenD_9 j ⊆ envelope_9 := by decide +kernel
theorem pivot_mem_9 : (1, 5) ∈ envelope_9 := by decide +kernel
theorem children_work_9 : ∀ j, Template HasSnaky 2 (childrenC_9 j) (childrenD_9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
theorem row_works_9 : Template HasSnaky 3 required_9 envelope_9 := by
  refine compose HasSnaky 2 childrenC_9 childrenD_9 children_work_9 (1, 5)
    required_9 envelope_9 pivot_mem_9 child_required_sub_9 child_envelope_sub_9 ?_
  intro b hb
  exact common_sub_9 (mem_commonEnvelope childrenD_9 b hb)
def required_16 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_16 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_16 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_4), required_6]
def childrenD_16 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_4), envelope_6]
theorem common_sub_16 : commonEnvelope childrenD_16 ⊆ insert (0, 4) required_16 := by decide +kernel
theorem child_required_sub_16 : ∀ j, childrenC_16 j ⊆ insert (0, 4) required_16 := by decide +kernel
theorem child_envelope_sub_16 : ∀ j, childrenD_16 j ⊆ envelope_16 := by decide +kernel
theorem pivot_mem_16 : (0, 4) ∈ envelope_16 := by decide +kernel
theorem children_work_16 : ∀ j, Template HasSnaky 2 (childrenC_16 j) (childrenD_16 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_6.mono (by decide +kernel)
theorem row_works_16 : Template HasSnaky 3 required_16 envelope_16 := by
  refine compose HasSnaky 2 childrenC_16 childrenD_16 children_work_16 (0, 4)
    required_16 envelope_16 pivot_mem_16 child_required_sub_16 child_envelope_sub_16 ?_
  intro b hb
  exact common_sub_16 (mem_commonEnvelope childrenD_16 b hb)
def required_20 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_20 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_20 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 0 (1, 0) required_6)]
def childrenD_20 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 0 (1, 0) envelope_6)]
theorem common_sub_20 : commonEnvelope childrenD_20 ⊆ insert (1, 4) required_20 := by decide +kernel
theorem child_required_sub_20 : ∀ j, childrenC_20 j ⊆ insert (1, 4) required_20 := by decide +kernel
theorem child_envelope_sub_20 : ∀ j, childrenD_20 j ⊆ envelope_20 := by decide +kernel
theorem pivot_mem_20 : (1, 4) ∈ envelope_20 := by decide +kernel
theorem children_work_20 : ∀ j, Template HasSnaky 2 (childrenC_20 j) (childrenD_20 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 0 (1, 0)).mono (by decide +kernel)
theorem row_works_20 : Template HasSnaky 3 required_20 envelope_20 := by
  refine compose HasSnaky 2 childrenC_20 childrenD_20 children_work_20 (1, 4)
    required_20 envelope_20 pivot_mem_20 child_required_sub_20 child_envelope_sub_20 ?_
  intro b hb
  exact common_sub_20 (mem_commonEnvelope childrenD_20 b hb)
def required_21 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_21 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_21 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_5), required_6]
def childrenD_21 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_5), envelope_6]
theorem common_sub_21 : commonEnvelope childrenD_21 ⊆ insert (0, 4) required_21 := by decide +kernel
theorem child_required_sub_21 : ∀ j, childrenC_21 j ⊆ insert (0, 4) required_21 := by decide +kernel
theorem child_envelope_sub_21 : ∀ j, childrenD_21 j ⊆ envelope_21 := by decide +kernel
theorem pivot_mem_21 : (0, 4) ∈ envelope_21 := by decide +kernel
theorem children_work_21 : ∀ j, Template HasSnaky 2 (childrenC_21 j) (childrenD_21 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_6.mono (by decide +kernel)
theorem row_works_21 : Template HasSnaky 3 required_21 envelope_21 := by
  refine compose HasSnaky 2 childrenC_21 childrenD_21 children_work_21 (0, 4)
    required_21 envelope_21 pivot_mem_21 child_required_sub_21 child_envelope_sub_21 ?_
  intro b hb
  exact common_sub_21 (mem_commonEnvelope childrenD_21 b hb)
def required_24 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_24 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_24 : Fin 2 → Finset Cell := ![(placed21 6 (4, 1) required_4), (placed21 1 (0, 1) required_6)]
def childrenD_24 : Fin 2 → Finset Cell := ![(placed21 6 (4, 1) envelope_4), (placed21 1 (0, 1) envelope_6)]
theorem common_sub_24 : commonEnvelope childrenD_24 ⊆ insert (4, 1) required_24 := by decide +kernel
theorem child_required_sub_24 : ∀ j, childrenC_24 j ⊆ insert (4, 1) required_24 := by decide +kernel
theorem child_envelope_sub_24 : ∀ j, childrenD_24 j ⊆ envelope_24 := by decide +kernel
theorem pivot_mem_24 : (4, 1) ∈ envelope_24 := by decide +kernel
theorem children_work_24 : ∀ j, Template HasSnaky 2 (childrenC_24 j) (childrenD_24 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 6 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
theorem row_works_24 : Template HasSnaky 3 required_24 envelope_24 := by
  refine compose HasSnaky 2 childrenC_24 childrenD_24 children_work_24 (4, 1)
    required_24 envelope_24 pivot_mem_24 child_required_sub_24 child_envelope_sub_24 ?_
  intro b hb
  exact common_sub_24 (mem_commonEnvelope childrenD_24 b hb)
def required_29 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_29 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_29 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_0), required_6]
def childrenD_29 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_0), envelope_6]
theorem common_sub_29 : commonEnvelope childrenD_29 ⊆ insert (0, 4) required_29 := by decide +kernel
theorem child_required_sub_29 : ∀ j, childrenC_29 j ⊆ insert (0, 4) required_29 := by decide +kernel
theorem child_envelope_sub_29 : ∀ j, childrenD_29 j ⊆ envelope_29 := by decide +kernel
theorem pivot_mem_29 : (0, 4) ∈ envelope_29 := by decide +kernel
theorem children_work_29 : ∀ j, Template HasSnaky 2 (childrenC_29 j) (childrenD_29 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact row_works_6.mono (by decide +kernel)
theorem row_works_29 : Template HasSnaky 3 required_29 envelope_29 := by
  refine compose HasSnaky 2 childrenC_29 childrenD_29 children_work_29 (0, 4)
    required_29 envelope_29 pivot_mem_29 child_required_sub_29 child_envelope_sub_29 ?_
  intro b hb
  exact common_sub_29 (mem_commonEnvelope childrenD_29 b hb)
def required_37 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_37 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_37 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 0 (1, 0) required_6)]
def childrenD_37 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 0 (1, 0) envelope_6)]
theorem common_sub_37 : commonEnvelope childrenD_37 ⊆ insert (1, 4) required_37 := by decide +kernel
theorem child_required_sub_37 : ∀ j, childrenC_37 j ⊆ insert (1, 4) required_37 := by decide +kernel
theorem child_envelope_sub_37 : ∀ j, childrenD_37 j ⊆ envelope_37 := by decide +kernel
theorem pivot_mem_37 : (1, 4) ∈ envelope_37 := by decide +kernel
theorem children_work_37 : ∀ j, Template HasSnaky 2 (childrenC_37 j) (childrenD_37 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 0 (1, 0)).mono (by decide +kernel)
theorem row_works_37 : Template HasSnaky 3 required_37 envelope_37 := by
  refine compose HasSnaky 2 childrenC_37 childrenD_37 children_work_37 (1, 4)
    required_37 envelope_37 pivot_mem_37 child_required_sub_37 child_envelope_sub_37 ?_
  intro b hb
  exact common_sub_37 (mem_commonEnvelope childrenD_37 b hb)
def required_44 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_44 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_44 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_43)]
def childrenD_44 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_43)]
theorem common_sub_44 : commonEnvelope childrenD_44 ⊆ insert (1, 4) required_44 := by decide +kernel
theorem child_required_sub_44 : ∀ j, childrenC_44 j ⊆ insert (1, 4) required_44 := by decide +kernel
theorem child_envelope_sub_44 : ∀ j, childrenD_44 j ⊆ envelope_44 := by decide +kernel
theorem pivot_mem_44 : (1, 4) ∈ envelope_44 := by decide +kernel
theorem children_work_44 : ∀ j, Template HasSnaky 2 (childrenC_44 j) (childrenD_44 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_43 0 (0, 1)).mono (by decide +kernel)
theorem row_works_44 : Template HasSnaky 3 required_44 envelope_44 := by
  refine compose HasSnaky 2 childrenC_44 childrenD_44 children_work_44 (1, 4)
    required_44 envelope_44 pivot_mem_44 child_required_sub_44 child_envelope_sub_44 ?_
  intro b hb
  exact common_sub_44 (mem_commonEnvelope childrenD_44 b hb)
def required_45 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_45 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_45 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), (placed21 2 (3, 0) required_23)]
def childrenD_45 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), (placed21 2 (3, 0) envelope_23)]
theorem common_sub_45 : commonEnvelope childrenD_45 ⊆ insert (3, 3) required_45 := by decide +kernel
theorem child_required_sub_45 : ∀ j, childrenC_45 j ⊆ insert (3, 3) required_45 := by decide +kernel
theorem child_envelope_sub_45 : ∀ j, childrenD_45 j ⊆ envelope_45 := by decide +kernel
theorem pivot_mem_45 : (3, 3) ∈ envelope_45 := by decide +kernel
theorem children_work_45 : ∀ j, Template HasSnaky 2 (childrenC_45 j) (childrenD_45 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_23 2 (3, 0)).mono (by decide +kernel)
theorem row_works_45 : Template HasSnaky 3 required_45 envelope_45 := by
  refine compose HasSnaky 2 childrenC_45 childrenD_45 children_work_45 (3, 3)
    required_45 envelope_45 pivot_mem_45 child_required_sub_45 child_envelope_sub_45 ?_
  intro b hb
  exact common_sub_45 (mem_commonEnvelope childrenD_45 b hb)
def required_52 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_52 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_52 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_51)]
def childrenD_52 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_51)]
theorem common_sub_52 : commonEnvelope childrenD_52 ⊆ insert (1, 4) required_52 := by decide +kernel
theorem child_required_sub_52 : ∀ j, childrenC_52 j ⊆ insert (1, 4) required_52 := by decide +kernel
theorem child_envelope_sub_52 : ∀ j, childrenD_52 j ⊆ envelope_52 := by decide +kernel
theorem pivot_mem_52 : (1, 4) ∈ envelope_52 := by decide +kernel
theorem children_work_52 : ∀ j, Template HasSnaky 2 (childrenC_52 j) (childrenD_52 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_51 0 (0, 1)).mono (by decide +kernel)
theorem row_works_52 : Template HasSnaky 3 required_52 envelope_52 := by
  refine compose HasSnaky 2 childrenC_52 childrenD_52 children_work_52 (1, 4)
    required_52 envelope_52 pivot_mem_52 child_required_sub_52 child_envelope_sub_52 ?_
  intro b hb
  exact common_sub_52 (mem_commonEnvelope childrenD_52 b hb)
def required_53 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_53 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_53 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_51)]
def childrenD_53 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_51)]
theorem common_sub_53 : commonEnvelope childrenD_53 ⊆ insert (0, 1) required_53 := by decide +kernel
theorem child_required_sub_53 : ∀ j, childrenC_53 j ⊆ insert (0, 1) required_53 := by decide +kernel
theorem child_envelope_sub_53 : ∀ j, childrenD_53 j ⊆ envelope_53 := by decide +kernel
theorem pivot_mem_53 : (0, 1) ∈ envelope_53 := by decide +kernel
theorem children_work_53 : ∀ j, Template HasSnaky 2 (childrenC_53 j) (childrenD_53 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_51 0 (0, 1)).mono (by decide +kernel)
theorem row_works_53 : Template HasSnaky 3 required_53 envelope_53 := by
  refine compose HasSnaky 2 childrenC_53 childrenD_53 children_work_53 (0, 1)
    required_53 envelope_53 pivot_mem_53 child_required_sub_53 child_envelope_sub_53 ?_
  intro b hb
  exact common_sub_53 (mem_commonEnvelope childrenD_53 b hb)
def required_54 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_54 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_54 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_51)]
def childrenD_54 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_51)]
theorem common_sub_54 : commonEnvelope childrenD_54 ⊆ insert (0, 2) required_54 := by decide +kernel
theorem child_required_sub_54 : ∀ j, childrenC_54 j ⊆ insert (0, 2) required_54 := by decide +kernel
theorem child_envelope_sub_54 : ∀ j, childrenD_54 j ⊆ envelope_54 := by decide +kernel
theorem pivot_mem_54 : (0, 2) ∈ envelope_54 := by decide +kernel
theorem children_work_54 : ∀ j, Template HasSnaky 2 (childrenC_54 j) (childrenD_54 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_51 0 (0, 1)).mono (by decide +kernel)
theorem row_works_54 : Template HasSnaky 3 required_54 envelope_54 := by
  refine compose HasSnaky 2 childrenC_54 childrenD_54 children_work_54 (0, 2)
    required_54 envelope_54 pivot_mem_54 child_required_sub_54 child_envelope_sub_54 ?_
  intro b hb
  exact common_sub_54 (mem_commonEnvelope childrenD_54 b hb)
def required_61 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_61 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_61 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_51)]
def childrenD_61 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_51)]
theorem common_sub_61 : commonEnvelope childrenD_61 ⊆ insert (1, 3) required_61 := by decide +kernel
theorem child_required_sub_61 : ∀ j, childrenC_61 j ⊆ insert (1, 3) required_61 := by decide +kernel
theorem child_envelope_sub_61 : ∀ j, childrenD_61 j ⊆ envelope_61 := by decide +kernel
theorem pivot_mem_61 : (1, 3) ∈ envelope_61 := by decide +kernel
theorem children_work_61 : ∀ j, Template HasSnaky 2 (childrenC_61 j) (childrenD_61 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_51 0 (0, 1)).mono (by decide +kernel)
theorem row_works_61 : Template HasSnaky 3 required_61 envelope_61 := by
  refine compose HasSnaky 2 childrenC_61 childrenD_61 children_work_61 (1, 3)
    required_61 envelope_61 pivot_mem_61 child_required_sub_61 child_envelope_sub_61 ?_
  intro b hb
  exact common_sub_61 (mem_commonEnvelope childrenD_61 b hb)
def required_62 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_62 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_62 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) required_6), (placed21 6 (1, 5) required_6)]
def childrenD_62 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) envelope_6), (placed21 6 (1, 5) envelope_6)]
theorem common_sub_62 : commonEnvelope childrenD_62 ⊆ insert (1, 5) required_62 := by decide +kernel
theorem child_required_sub_62 : ∀ j, childrenC_62 j ⊆ insert (1, 5) required_62 := by decide +kernel
theorem child_envelope_sub_62 : ∀ j, childrenD_62 j ⊆ envelope_62 := by decide +kernel
theorem pivot_mem_62 : (1, 5) ∈ envelope_62 := by decide +kernel
theorem children_work_62 : ∀ j, Template HasSnaky 2 (childrenC_62 j) (childrenD_62 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 4 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 6 (1, 5)).mono (by decide +kernel)
theorem row_works_62 : Template HasSnaky 3 required_62 envelope_62 := by
  refine compose HasSnaky 2 childrenC_62 childrenD_62 children_work_62 (1, 5)
    required_62 envelope_62 pivot_mem_62 child_required_sub_62 child_envelope_sub_62 ?_
  intro b hb
  exact common_sub_62 (mem_commonEnvelope childrenD_62 b hb)
def required_64 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_64 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_64 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_43)]
def childrenD_64 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_43)]
theorem common_sub_64 : commonEnvelope childrenD_64 ⊆ insert (0, 2) required_64 := by decide +kernel
theorem child_required_sub_64 : ∀ j, childrenC_64 j ⊆ insert (0, 2) required_64 := by decide +kernel
theorem child_envelope_sub_64 : ∀ j, childrenD_64 j ⊆ envelope_64 := by decide +kernel
theorem pivot_mem_64 : (0, 2) ∈ envelope_64 := by decide +kernel
theorem children_work_64 : ∀ j, Template HasSnaky 2 (childrenC_64 j) (childrenD_64 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_43 0 (0, 1)).mono (by decide +kernel)
theorem row_works_64 : Template HasSnaky 3 required_64 envelope_64 := by
  refine compose HasSnaky 2 childrenC_64 childrenD_64 children_work_64 (0, 2)
    required_64 envelope_64 pivot_mem_64 child_required_sub_64 child_envelope_sub_64 ?_
  intro b hb
  exact common_sub_64 (mem_commonEnvelope childrenD_64 b hb)
def required_69 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_69 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_69 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), (placed21 2 (3, 0) required_15)]
def childrenD_69 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), (placed21 2 (3, 0) envelope_15)]
theorem common_sub_69 : commonEnvelope childrenD_69 ⊆ insert (3, 1) required_69 := by decide +kernel
theorem child_required_sub_69 : ∀ j, childrenC_69 j ⊆ insert (3, 1) required_69 := by decide +kernel
theorem child_envelope_sub_69 : ∀ j, childrenD_69 j ⊆ envelope_69 := by decide +kernel
theorem pivot_mem_69 : (3, 1) ∈ envelope_69 := by decide +kernel
theorem children_work_69 : ∀ j, Template HasSnaky 2 (childrenC_69 j) (childrenD_69 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_15 2 (3, 0)).mono (by decide +kernel)
theorem row_works_69 : Template HasSnaky 3 required_69 envelope_69 := by
  refine compose HasSnaky 2 childrenC_69 childrenD_69 children_work_69 (3, 1)
    required_69 envelope_69 pivot_mem_69 child_required_sub_69 child_envelope_sub_69 ?_
  intro b hb
  exact common_sub_69 (mem_commonEnvelope childrenD_69 b hb)
def required_74 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_74 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_74 : Fin 4 → Finset Cell := ![required_30, (placed21 2 (1, 0) required_30), required_36, (placed21 2 (1, 0) required_36)]
def childrenD_74 : Fin 4 → Finset Cell := ![envelope_30, (placed21 2 (1, 0) envelope_30), envelope_36, (placed21 2 (1, 0) envelope_36)]
theorem common_sub_74 : commonEnvelope childrenD_74 ⊆ insert (1, 3) required_74 := by decide +kernel
theorem child_required_sub_74 : ∀ j, childrenC_74 j ⊆ insert (1, 3) required_74 := by decide +kernel
theorem child_envelope_sub_74 : ∀ j, childrenD_74 j ⊆ envelope_74 := by decide +kernel
theorem pivot_mem_74 : (1, 3) ∈ envelope_74 := by decide +kernel
theorem children_work_74 : ∀ j, Template HasSnaky 2 (childrenC_74 j) (childrenD_74 j) := by
  intro j
  fin_cases j
  · exact row_works_30.mono (by decide +kernel)
  · exact (placed21_template row_works_30 2 (1, 0)).mono (by decide +kernel)
  · exact row_works_36.mono (by decide +kernel)
  · exact (placed21_template row_works_36 2 (1, 0)).mono (by decide +kernel)
theorem row_works_74 : Template HasSnaky 3 required_74 envelope_74 := by
  refine compose HasSnaky 2 childrenC_74 childrenD_74 children_work_74 (1, 3)
    required_74 envelope_74 pivot_mem_74 child_required_sub_74 child_envelope_sub_74 ?_
  intro b hb
  exact common_sub_74 (mem_commonEnvelope childrenD_74 b hb)
def required_78 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_78 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_78 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 5 (4, 0) required_77)]
def childrenD_78 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 5 (4, 0) envelope_77)]
theorem common_sub_78 : commonEnvelope childrenD_78 ⊆ insert (3, 0) required_78 := by decide +kernel
theorem child_required_sub_78 : ∀ j, childrenC_78 j ⊆ insert (3, 0) required_78 := by decide +kernel
theorem child_envelope_sub_78 : ∀ j, childrenD_78 j ⊆ envelope_78 := by decide +kernel
theorem pivot_mem_78 : (3, 0) ∈ envelope_78 := by decide +kernel
theorem children_work_78 : ∀ j, Template HasSnaky 2 (childrenC_78 j) (childrenD_78 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_77 5 (4, 0)).mono (by decide +kernel)
theorem row_works_78 : Template HasSnaky 3 required_78 envelope_78 := by
  refine compose HasSnaky 2 childrenC_78 childrenD_78 children_work_78 (3, 0)
    required_78 envelope_78 pivot_mem_78 child_required_sub_78 child_envelope_sub_78 ?_
  intro b hb
  exact common_sub_78 (mem_commonEnvelope childrenD_78 b hb)
def required_87 : Finset Cell := ⟨(([(0, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_87 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_87 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) required_11), (placed21 7 (4, 4) required_35)]
def childrenD_87 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) envelope_11), (placed21 7 (4, 4) envelope_35)]
theorem common_sub_87 : commonEnvelope childrenD_87 ⊆ insert (4, 2) required_87 := by decide +kernel
theorem child_required_sub_87 : ∀ j, childrenC_87 j ⊆ insert (4, 2) required_87 := by decide +kernel
theorem child_envelope_sub_87 : ∀ j, childrenD_87 j ⊆ envelope_87 := by decide +kernel
theorem pivot_mem_87 : (4, 2) ∈ envelope_87 := by decide +kernel
theorem children_work_87 : ∀ j, Template HasSnaky 2 (childrenC_87 j) (childrenD_87 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 7 (4, 4)).mono (by decide +kernel)
theorem row_works_87 : Template HasSnaky 3 required_87 envelope_87 := by
  refine compose HasSnaky 2 childrenC_87 childrenD_87 children_work_87 (4, 2)
    required_87 envelope_87 pivot_mem_87 child_required_sub_87 child_envelope_sub_87 ?_
  intro b hb
  exact common_sub_87 (mem_commonEnvelope childrenD_87 b hb)
def required_101 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_101 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_101 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_51)]
def childrenD_101 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_51)]
theorem common_sub_101 : commonEnvelope childrenD_101 ⊆ insert (0, 3) required_101 := by decide +kernel
theorem child_required_sub_101 : ∀ j, childrenC_101 j ⊆ insert (0, 3) required_101 := by decide +kernel
theorem child_envelope_sub_101 : ∀ j, childrenD_101 j ⊆ envelope_101 := by decide +kernel
theorem pivot_mem_101 : (0, 3) ∈ envelope_101 := by decide +kernel
theorem children_work_101 : ∀ j, Template HasSnaky 2 (childrenC_101 j) (childrenD_101 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_51 0 (0, 1)).mono (by decide +kernel)
theorem row_works_101 : Template HasSnaky 3 required_101 envelope_101 := by
  refine compose HasSnaky 2 childrenC_101 childrenD_101 children_work_101 (0, 3)
    required_101 envelope_101 pivot_mem_101 child_required_sub_101 child_envelope_sub_101 ?_
  intro b hb
  exact common_sub_101 (mem_commonEnvelope childrenD_101 b hb)
def required_103 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_103 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_103 : Fin 2 → Finset Cell := ![required_6, required_11]
def childrenD_103 : Fin 2 → Finset Cell := ![envelope_6, envelope_11]
theorem common_sub_103 : commonEnvelope childrenD_103 ⊆ insert (0, 4) required_103 := by decide +kernel
theorem child_required_sub_103 : ∀ j, childrenC_103 j ⊆ insert (0, 4) required_103 := by decide +kernel
theorem child_envelope_sub_103 : ∀ j, childrenD_103 j ⊆ envelope_103 := by decide +kernel
theorem pivot_mem_103 : (0, 4) ∈ envelope_103 := by decide +kernel
theorem children_work_103 : ∀ j, Template HasSnaky 2 (childrenC_103 j) (childrenD_103 j) := by
  intro j
  fin_cases j
  · exact row_works_6.mono (by decide +kernel)
  · exact row_works_11.mono (by decide +kernel)
theorem row_works_103 : Template HasSnaky 3 required_103 envelope_103 := by
  refine compose HasSnaky 2 childrenC_103 childrenD_103 children_work_103 (0, 4)
    required_103 envelope_103 pivot_mem_103 child_required_sub_103 child_envelope_sub_103 ?_
  intro b hb
  exact common_sub_103 (mem_commonEnvelope childrenD_103 b hb)
def required_105 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_105 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_105 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_5), required_11]
def childrenD_105 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_5), envelope_11]
theorem common_sub_105 : commonEnvelope childrenD_105 ⊆ insert (0, 3) required_105 := by decide +kernel
theorem child_required_sub_105 : ∀ j, childrenC_105 j ⊆ insert (0, 3) required_105 := by decide +kernel
theorem child_envelope_sub_105 : ∀ j, childrenD_105 j ⊆ envelope_105 := by decide +kernel
theorem pivot_mem_105 : (0, 3) ∈ envelope_105 := by decide +kernel
theorem children_work_105 : ∀ j, Template HasSnaky 2 (childrenC_105 j) (childrenD_105 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_11.mono (by decide +kernel)
theorem row_works_105 : Template HasSnaky 3 required_105 envelope_105 := by
  refine compose HasSnaky 2 childrenC_105 childrenD_105 children_work_105 (0, 3)
    required_105 envelope_105 pivot_mem_105 child_required_sub_105 child_envelope_sub_105 ?_
  intro b hb
  exact common_sub_105 (mem_commonEnvelope childrenD_105 b hb)
def height_7 : ℕ := 3
def childrenH_7 : Fin 2 → ℕ := ![height_6, height_6]
theorem height_exact_7 : height_7 = 1 + Finset.univ.sup childrenH_7 := by decide +kernel
theorem required_origin_7 : ∀ x ∈ required_7,
    (∃ j, x ∈ childrenC_7 j) ∨ ∀ j, x ∈ childrenD_7 j := by decide +kernel
theorem required_exact_7 : required_7 =
    ((Finset.univ.biUnion childrenC_7) ∪ commonEnvelope childrenD_7).erase (0, 5) := by
  exact required_eq_combination childrenC_7 childrenD_7 (0, 5) required_7
    (by decide +kernel) child_required_sub_7 common_sub_7 required_origin_7
theorem envelope_origin_7 : ∀ x ∈ envelope_7,
    x = (0, 5) ∨ ∃ j, x ∈ childrenD_7 j := by decide +kernel
theorem envelope_exact_7 : envelope_7 =
    insert (0, 5) (Finset.univ.biUnion childrenD_7) := by
  exact envelope_eq_combination childrenD_7 (0, 5) envelope_7
    pivot_mem_7 child_envelope_sub_7 envelope_origin_7
def checked_7 : CheckedCard where
  required := required_7
  envelope := envelope_7
  height := height_7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_7
def height_8 : ℕ := 3
def childrenH_8 : Fin 2 → ℕ := ![height_6, height_6]
theorem height_exact_8 : height_8 = 1 + Finset.univ.sup childrenH_8 := by decide +kernel
theorem required_origin_8 : ∀ x ∈ required_8,
    (∃ j, x ∈ childrenC_8 j) ∨ ∀ j, x ∈ childrenD_8 j := by decide +kernel
theorem required_exact_8 : required_8 =
    ((Finset.univ.biUnion childrenC_8) ∪ commonEnvelope childrenD_8).erase (4, 1) := by
  exact required_eq_combination childrenC_8 childrenD_8 (4, 1) required_8
    (by decide +kernel) child_required_sub_8 common_sub_8 required_origin_8
theorem envelope_origin_8 : ∀ x ∈ envelope_8,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_8 j := by decide +kernel
theorem envelope_exact_8 : envelope_8 =
    insert (4, 1) (Finset.univ.biUnion childrenD_8) := by
  exact envelope_eq_combination childrenD_8 (4, 1) envelope_8
    pivot_mem_8 child_envelope_sub_8 envelope_origin_8
def checked_8 : CheckedCard where
  required := required_8
  envelope := envelope_8
  height := height_8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_8
def height_9 : ℕ := 3
def childrenH_9 : Fin 2 → ℕ := ![height_6, height_6]
theorem height_exact_9 : height_9 = 1 + Finset.univ.sup childrenH_9 := by decide +kernel
theorem required_origin_9 : ∀ x ∈ required_9,
    (∃ j, x ∈ childrenC_9 j) ∨ ∀ j, x ∈ childrenD_9 j := by decide +kernel
theorem required_exact_9 : required_9 =
    ((Finset.univ.biUnion childrenC_9) ∪ commonEnvelope childrenD_9).erase (1, 5) := by
  exact required_eq_combination childrenC_9 childrenD_9 (1, 5) required_9
    (by decide +kernel) child_required_sub_9 common_sub_9 required_origin_9
theorem envelope_origin_9 : ∀ x ∈ envelope_9,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_9 j := by decide +kernel
theorem envelope_exact_9 : envelope_9 =
    insert (1, 5) (Finset.univ.biUnion childrenD_9) := by
  exact envelope_eq_combination childrenD_9 (1, 5) envelope_9
    pivot_mem_9 child_envelope_sub_9 envelope_origin_9
def checked_9 : CheckedCard where
  required := required_9
  envelope := envelope_9
  height := height_9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_9
def height_16 : ℕ := 3
def childrenH_16 : Fin 2 → ℕ := ![height_4, height_6]
theorem height_exact_16 : height_16 = 1 + Finset.univ.sup childrenH_16 := by decide +kernel
theorem required_origin_16 : ∀ x ∈ required_16,
    (∃ j, x ∈ childrenC_16 j) ∨ ∀ j, x ∈ childrenD_16 j := by decide +kernel
theorem required_exact_16 : required_16 =
    ((Finset.univ.biUnion childrenC_16) ∪ commonEnvelope childrenD_16).erase (0, 4) := by
  exact required_eq_combination childrenC_16 childrenD_16 (0, 4) required_16
    (by decide +kernel) child_required_sub_16 common_sub_16 required_origin_16
theorem envelope_origin_16 : ∀ x ∈ envelope_16,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_16 j := by decide +kernel
theorem envelope_exact_16 : envelope_16 =
    insert (0, 4) (Finset.univ.biUnion childrenD_16) := by
  exact envelope_eq_combination childrenD_16 (0, 4) envelope_16
    pivot_mem_16 child_envelope_sub_16 envelope_origin_16
def checked_16 : CheckedCard where
  required := required_16
  envelope := envelope_16
  height := height_16
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_16
def height_20 : ℕ := 3
def childrenH_20 : Fin 2 → ℕ := ![height_0, height_6]
theorem height_exact_20 : height_20 = 1 + Finset.univ.sup childrenH_20 := by decide +kernel
theorem required_origin_20 : ∀ x ∈ required_20,
    (∃ j, x ∈ childrenC_20 j) ∨ ∀ j, x ∈ childrenD_20 j := by decide +kernel
theorem required_exact_20 : required_20 =
    ((Finset.univ.biUnion childrenC_20) ∪ commonEnvelope childrenD_20).erase (1, 4) := by
  exact required_eq_combination childrenC_20 childrenD_20 (1, 4) required_20
    (by decide +kernel) child_required_sub_20 common_sub_20 required_origin_20
theorem envelope_origin_20 : ∀ x ∈ envelope_20,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_20 j := by decide +kernel
theorem envelope_exact_20 : envelope_20 =
    insert (1, 4) (Finset.univ.biUnion childrenD_20) := by
  exact envelope_eq_combination childrenD_20 (1, 4) envelope_20
    pivot_mem_20 child_envelope_sub_20 envelope_origin_20
def checked_20 : CheckedCard where
  required := required_20
  envelope := envelope_20
  height := height_20
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_20
def height_21 : ℕ := 3
def childrenH_21 : Fin 2 → ℕ := ![height_5, height_6]
theorem height_exact_21 : height_21 = 1 + Finset.univ.sup childrenH_21 := by decide +kernel
theorem required_origin_21 : ∀ x ∈ required_21,
    (∃ j, x ∈ childrenC_21 j) ∨ ∀ j, x ∈ childrenD_21 j := by decide +kernel
theorem required_exact_21 : required_21 =
    ((Finset.univ.biUnion childrenC_21) ∪ commonEnvelope childrenD_21).erase (0, 4) := by
  exact required_eq_combination childrenC_21 childrenD_21 (0, 4) required_21
    (by decide +kernel) child_required_sub_21 common_sub_21 required_origin_21
theorem envelope_origin_21 : ∀ x ∈ envelope_21,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_21 j := by decide +kernel
theorem envelope_exact_21 : envelope_21 =
    insert (0, 4) (Finset.univ.biUnion childrenD_21) := by
  exact envelope_eq_combination childrenD_21 (0, 4) envelope_21
    pivot_mem_21 child_envelope_sub_21 envelope_origin_21
def checked_21 : CheckedCard where
  required := required_21
  envelope := envelope_21
  height := height_21
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_21
def height_24 : ℕ := 3
def childrenH_24 : Fin 2 → ℕ := ![height_4, height_6]
theorem height_exact_24 : height_24 = 1 + Finset.univ.sup childrenH_24 := by decide +kernel
theorem required_origin_24 : ∀ x ∈ required_24,
    (∃ j, x ∈ childrenC_24 j) ∨ ∀ j, x ∈ childrenD_24 j := by decide +kernel
theorem required_exact_24 : required_24 =
    ((Finset.univ.biUnion childrenC_24) ∪ commonEnvelope childrenD_24).erase (4, 1) := by
  exact required_eq_combination childrenC_24 childrenD_24 (4, 1) required_24
    (by decide +kernel) child_required_sub_24 common_sub_24 required_origin_24
theorem envelope_origin_24 : ∀ x ∈ envelope_24,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_24 j := by decide +kernel
theorem envelope_exact_24 : envelope_24 =
    insert (4, 1) (Finset.univ.biUnion childrenD_24) := by
  exact envelope_eq_combination childrenD_24 (4, 1) envelope_24
    pivot_mem_24 child_envelope_sub_24 envelope_origin_24
def checked_24 : CheckedCard where
  required := required_24
  envelope := envelope_24
  height := height_24
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_24
def height_29 : ℕ := 3
def childrenH_29 : Fin 2 → ℕ := ![height_0, height_6]
theorem height_exact_29 : height_29 = 1 + Finset.univ.sup childrenH_29 := by decide +kernel
theorem required_origin_29 : ∀ x ∈ required_29,
    (∃ j, x ∈ childrenC_29 j) ∨ ∀ j, x ∈ childrenD_29 j := by decide +kernel
theorem required_exact_29 : required_29 =
    ((Finset.univ.biUnion childrenC_29) ∪ commonEnvelope childrenD_29).erase (0, 4) := by
  exact required_eq_combination childrenC_29 childrenD_29 (0, 4) required_29
    (by decide +kernel) child_required_sub_29 common_sub_29 required_origin_29
theorem envelope_origin_29 : ∀ x ∈ envelope_29,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_29 j := by decide +kernel
theorem envelope_exact_29 : envelope_29 =
    insert (0, 4) (Finset.univ.biUnion childrenD_29) := by
  exact envelope_eq_combination childrenD_29 (0, 4) envelope_29
    pivot_mem_29 child_envelope_sub_29 envelope_origin_29
def checked_29 : CheckedCard where
  required := required_29
  envelope := envelope_29
  height := height_29
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_29
def height_37 : ℕ := 3
def childrenH_37 : Fin 2 → ℕ := ![height_5, height_6]
theorem height_exact_37 : height_37 = 1 + Finset.univ.sup childrenH_37 := by decide +kernel
theorem required_origin_37 : ∀ x ∈ required_37,
    (∃ j, x ∈ childrenC_37 j) ∨ ∀ j, x ∈ childrenD_37 j := by decide +kernel
theorem required_exact_37 : required_37 =
    ((Finset.univ.biUnion childrenC_37) ∪ commonEnvelope childrenD_37).erase (1, 4) := by
  exact required_eq_combination childrenC_37 childrenD_37 (1, 4) required_37
    (by decide +kernel) child_required_sub_37 common_sub_37 required_origin_37
theorem envelope_origin_37 : ∀ x ∈ envelope_37,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_37 j := by decide +kernel
theorem envelope_exact_37 : envelope_37 =
    insert (1, 4) (Finset.univ.biUnion childrenD_37) := by
  exact envelope_eq_combination childrenD_37 (1, 4) envelope_37
    pivot_mem_37 child_envelope_sub_37 envelope_origin_37
def checked_37 : CheckedCard where
  required := required_37
  envelope := envelope_37
  height := height_37
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_37
def height_44 : ℕ := 3
def childrenH_44 : Fin 2 → ℕ := ![height_0, height_43]
theorem height_exact_44 : height_44 = 1 + Finset.univ.sup childrenH_44 := by decide +kernel
theorem required_origin_44 : ∀ x ∈ required_44,
    (∃ j, x ∈ childrenC_44 j) ∨ ∀ j, x ∈ childrenD_44 j := by decide +kernel
theorem required_exact_44 : required_44 =
    ((Finset.univ.biUnion childrenC_44) ∪ commonEnvelope childrenD_44).erase (1, 4) := by
  exact required_eq_combination childrenC_44 childrenD_44 (1, 4) required_44
    (by decide +kernel) child_required_sub_44 common_sub_44 required_origin_44
theorem envelope_origin_44 : ∀ x ∈ envelope_44,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_44 j := by decide +kernel
theorem envelope_exact_44 : envelope_44 =
    insert (1, 4) (Finset.univ.biUnion childrenD_44) := by
  exact envelope_eq_combination childrenD_44 (1, 4) envelope_44
    pivot_mem_44 child_envelope_sub_44 envelope_origin_44
def checked_44 : CheckedCard where
  required := required_44
  envelope := envelope_44
  height := height_44
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_44
def height_45 : ℕ := 3
def childrenH_45 : Fin 2 → ℕ := ![height_5, height_23]
theorem height_exact_45 : height_45 = 1 + Finset.univ.sup childrenH_45 := by decide +kernel
theorem required_origin_45 : ∀ x ∈ required_45,
    (∃ j, x ∈ childrenC_45 j) ∨ ∀ j, x ∈ childrenD_45 j := by decide +kernel
theorem required_exact_45 : required_45 =
    ((Finset.univ.biUnion childrenC_45) ∪ commonEnvelope childrenD_45).erase (3, 3) := by
  exact required_eq_combination childrenC_45 childrenD_45 (3, 3) required_45
    (by decide +kernel) child_required_sub_45 common_sub_45 required_origin_45
theorem envelope_origin_45 : ∀ x ∈ envelope_45,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_45 j := by decide +kernel
theorem envelope_exact_45 : envelope_45 =
    insert (3, 3) (Finset.univ.biUnion childrenD_45) := by
  exact envelope_eq_combination childrenD_45 (3, 3) envelope_45
    pivot_mem_45 child_envelope_sub_45 envelope_origin_45
def checked_45 : CheckedCard where
  required := required_45
  envelope := envelope_45
  height := height_45
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_45
def height_52 : ℕ := 3
def childrenH_52 : Fin 2 → ℕ := ![height_0, height_51]
theorem height_exact_52 : height_52 = 1 + Finset.univ.sup childrenH_52 := by decide +kernel
theorem required_origin_52 : ∀ x ∈ required_52,
    (∃ j, x ∈ childrenC_52 j) ∨ ∀ j, x ∈ childrenD_52 j := by decide +kernel
theorem required_exact_52 : required_52 =
    ((Finset.univ.biUnion childrenC_52) ∪ commonEnvelope childrenD_52).erase (1, 4) := by
  exact required_eq_combination childrenC_52 childrenD_52 (1, 4) required_52
    (by decide +kernel) child_required_sub_52 common_sub_52 required_origin_52
theorem envelope_origin_52 : ∀ x ∈ envelope_52,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_52 j := by decide +kernel
theorem envelope_exact_52 : envelope_52 =
    insert (1, 4) (Finset.univ.biUnion childrenD_52) := by
  exact envelope_eq_combination childrenD_52 (1, 4) envelope_52
    pivot_mem_52 child_envelope_sub_52 envelope_origin_52
def checked_52 : CheckedCard where
  required := required_52
  envelope := envelope_52
  height := height_52
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_52
def height_53 : ℕ := 3
def childrenH_53 : Fin 2 → ℕ := ![height_0, height_51]
theorem height_exact_53 : height_53 = 1 + Finset.univ.sup childrenH_53 := by decide +kernel
theorem required_origin_53 : ∀ x ∈ required_53,
    (∃ j, x ∈ childrenC_53 j) ∨ ∀ j, x ∈ childrenD_53 j := by decide +kernel
theorem required_exact_53 : required_53 =
    ((Finset.univ.biUnion childrenC_53) ∪ commonEnvelope childrenD_53).erase (0, 1) := by
  exact required_eq_combination childrenC_53 childrenD_53 (0, 1) required_53
    (by decide +kernel) child_required_sub_53 common_sub_53 required_origin_53
theorem envelope_origin_53 : ∀ x ∈ envelope_53,
    x = (0, 1) ∨ ∃ j, x ∈ childrenD_53 j := by decide +kernel
theorem envelope_exact_53 : envelope_53 =
    insert (0, 1) (Finset.univ.biUnion childrenD_53) := by
  exact envelope_eq_combination childrenD_53 (0, 1) envelope_53
    pivot_mem_53 child_envelope_sub_53 envelope_origin_53
def checked_53 : CheckedCard where
  required := required_53
  envelope := envelope_53
  height := height_53
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_53
def height_54 : ℕ := 3
def childrenH_54 : Fin 2 → ℕ := ![height_0, height_51]
theorem height_exact_54 : height_54 = 1 + Finset.univ.sup childrenH_54 := by decide +kernel
theorem required_origin_54 : ∀ x ∈ required_54,
    (∃ j, x ∈ childrenC_54 j) ∨ ∀ j, x ∈ childrenD_54 j := by decide +kernel
theorem required_exact_54 : required_54 =
    ((Finset.univ.biUnion childrenC_54) ∪ commonEnvelope childrenD_54).erase (0, 2) := by
  exact required_eq_combination childrenC_54 childrenD_54 (0, 2) required_54
    (by decide +kernel) child_required_sub_54 common_sub_54 required_origin_54
theorem envelope_origin_54 : ∀ x ∈ envelope_54,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_54 j := by decide +kernel
theorem envelope_exact_54 : envelope_54 =
    insert (0, 2) (Finset.univ.biUnion childrenD_54) := by
  exact envelope_eq_combination childrenD_54 (0, 2) envelope_54
    pivot_mem_54 child_envelope_sub_54 envelope_origin_54
def checked_54 : CheckedCard where
  required := required_54
  envelope := envelope_54
  height := height_54
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_54
def height_61 : ℕ := 3
def childrenH_61 : Fin 2 → ℕ := ![height_0, height_51]
theorem height_exact_61 : height_61 = 1 + Finset.univ.sup childrenH_61 := by decide +kernel
theorem required_origin_61 : ∀ x ∈ required_61,
    (∃ j, x ∈ childrenC_61 j) ∨ ∀ j, x ∈ childrenD_61 j := by decide +kernel
theorem required_exact_61 : required_61 =
    ((Finset.univ.biUnion childrenC_61) ∪ commonEnvelope childrenD_61).erase (1, 3) := by
  exact required_eq_combination childrenC_61 childrenD_61 (1, 3) required_61
    (by decide +kernel) child_required_sub_61 common_sub_61 required_origin_61
theorem envelope_origin_61 : ∀ x ∈ envelope_61,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_61 j := by decide +kernel
theorem envelope_exact_61 : envelope_61 =
    insert (1, 3) (Finset.univ.biUnion childrenD_61) := by
  exact envelope_eq_combination childrenD_61 (1, 3) envelope_61
    pivot_mem_61 child_envelope_sub_61 envelope_origin_61
def checked_61 : CheckedCard where
  required := required_61
  envelope := envelope_61
  height := height_61
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_61
def height_62 : ℕ := 3
def childrenH_62 : Fin 2 → ℕ := ![height_6, height_6]
theorem height_exact_62 : height_62 = 1 + Finset.univ.sup childrenH_62 := by decide +kernel
theorem required_origin_62 : ∀ x ∈ required_62,
    (∃ j, x ∈ childrenC_62 j) ∨ ∀ j, x ∈ childrenD_62 j := by decide +kernel
theorem required_exact_62 : required_62 =
    ((Finset.univ.biUnion childrenC_62) ∪ commonEnvelope childrenD_62).erase (1, 5) := by
  exact required_eq_combination childrenC_62 childrenD_62 (1, 5) required_62
    (by decide +kernel) child_required_sub_62 common_sub_62 required_origin_62
theorem envelope_origin_62 : ∀ x ∈ envelope_62,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_62 j := by decide +kernel
theorem envelope_exact_62 : envelope_62 =
    insert (1, 5) (Finset.univ.biUnion childrenD_62) := by
  exact envelope_eq_combination childrenD_62 (1, 5) envelope_62
    pivot_mem_62 child_envelope_sub_62 envelope_origin_62
def checked_62 : CheckedCard where
  required := required_62
  envelope := envelope_62
  height := height_62
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_62
def height_64 : ℕ := 3
def childrenH_64 : Fin 2 → ℕ := ![height_0, height_43]
theorem height_exact_64 : height_64 = 1 + Finset.univ.sup childrenH_64 := by decide +kernel
theorem required_origin_64 : ∀ x ∈ required_64,
    (∃ j, x ∈ childrenC_64 j) ∨ ∀ j, x ∈ childrenD_64 j := by decide +kernel
theorem required_exact_64 : required_64 =
    ((Finset.univ.biUnion childrenC_64) ∪ commonEnvelope childrenD_64).erase (0, 2) := by
  exact required_eq_combination childrenC_64 childrenD_64 (0, 2) required_64
    (by decide +kernel) child_required_sub_64 common_sub_64 required_origin_64
theorem envelope_origin_64 : ∀ x ∈ envelope_64,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_64 j := by decide +kernel
theorem envelope_exact_64 : envelope_64 =
    insert (0, 2) (Finset.univ.biUnion childrenD_64) := by
  exact envelope_eq_combination childrenD_64 (0, 2) envelope_64
    pivot_mem_64 child_envelope_sub_64 envelope_origin_64
def checked_64 : CheckedCard where
  required := required_64
  envelope := envelope_64
  height := height_64
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_64
def height_69 : ℕ := 3
def childrenH_69 : Fin 2 → ℕ := ![height_5, height_15]
theorem height_exact_69 : height_69 = 1 + Finset.univ.sup childrenH_69 := by decide +kernel
theorem required_origin_69 : ∀ x ∈ required_69,
    (∃ j, x ∈ childrenC_69 j) ∨ ∀ j, x ∈ childrenD_69 j := by decide +kernel
theorem required_exact_69 : required_69 =
    ((Finset.univ.biUnion childrenC_69) ∪ commonEnvelope childrenD_69).erase (3, 1) := by
  exact required_eq_combination childrenC_69 childrenD_69 (3, 1) required_69
    (by decide +kernel) child_required_sub_69 common_sub_69 required_origin_69
theorem envelope_origin_69 : ∀ x ∈ envelope_69,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_69 j := by decide +kernel
theorem envelope_exact_69 : envelope_69 =
    insert (3, 1) (Finset.univ.biUnion childrenD_69) := by
  exact envelope_eq_combination childrenD_69 (3, 1) envelope_69
    pivot_mem_69 child_envelope_sub_69 envelope_origin_69
def checked_69 : CheckedCard where
  required := required_69
  envelope := envelope_69
  height := height_69
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_69
def height_74 : ℕ := 3
def childrenH_74 : Fin 4 → ℕ := ![height_30, height_30, height_36, height_36]
theorem height_exact_74 : height_74 = 1 + Finset.univ.sup childrenH_74 := by decide +kernel
theorem required_origin_74 : ∀ x ∈ required_74,
    (∃ j, x ∈ childrenC_74 j) ∨ ∀ j, x ∈ childrenD_74 j := by decide +kernel
theorem required_exact_74 : required_74 =
    ((Finset.univ.biUnion childrenC_74) ∪ commonEnvelope childrenD_74).erase (1, 3) := by
  exact required_eq_combination childrenC_74 childrenD_74 (1, 3) required_74
    (by decide +kernel) child_required_sub_74 common_sub_74 required_origin_74
theorem envelope_origin_74 : ∀ x ∈ envelope_74,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_74 j := by decide +kernel
theorem envelope_exact_74 : envelope_74 =
    insert (1, 3) (Finset.univ.biUnion childrenD_74) := by
  exact envelope_eq_combination childrenD_74 (1, 3) envelope_74
    pivot_mem_74 child_envelope_sub_74 envelope_origin_74
def checked_74 : CheckedCard where
  required := required_74
  envelope := envelope_74
  height := height_74
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_74
def height_78 : ℕ := 3
def childrenH_78 : Fin 2 → ℕ := ![height_5, height_77]
theorem height_exact_78 : height_78 = 1 + Finset.univ.sup childrenH_78 := by decide +kernel
theorem required_origin_78 : ∀ x ∈ required_78,
    (∃ j, x ∈ childrenC_78 j) ∨ ∀ j, x ∈ childrenD_78 j := by decide +kernel
theorem required_exact_78 : required_78 =
    ((Finset.univ.biUnion childrenC_78) ∪ commonEnvelope childrenD_78).erase (3, 0) := by
  exact required_eq_combination childrenC_78 childrenD_78 (3, 0) required_78
    (by decide +kernel) child_required_sub_78 common_sub_78 required_origin_78
theorem envelope_origin_78 : ∀ x ∈ envelope_78,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_78 j := by decide +kernel
theorem envelope_exact_78 : envelope_78 =
    insert (3, 0) (Finset.univ.biUnion childrenD_78) := by
  exact envelope_eq_combination childrenD_78 (3, 0) envelope_78
    pivot_mem_78 child_envelope_sub_78 envelope_origin_78
def checked_78 : CheckedCard where
  required := required_78
  envelope := envelope_78
  height := height_78
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_78
def height_87 : ℕ := 3
def childrenH_87 : Fin 2 → ℕ := ![height_11, height_35]
theorem height_exact_87 : height_87 = 1 + Finset.univ.sup childrenH_87 := by decide +kernel
theorem required_origin_87 : ∀ x ∈ required_87,
    (∃ j, x ∈ childrenC_87 j) ∨ ∀ j, x ∈ childrenD_87 j := by decide +kernel
theorem required_exact_87 : required_87 =
    ((Finset.univ.biUnion childrenC_87) ∪ commonEnvelope childrenD_87).erase (4, 2) := by
  exact required_eq_combination childrenC_87 childrenD_87 (4, 2) required_87
    (by decide +kernel) child_required_sub_87 common_sub_87 required_origin_87
theorem envelope_origin_87 : ∀ x ∈ envelope_87,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_87 j := by decide +kernel
theorem envelope_exact_87 : envelope_87 =
    insert (4, 2) (Finset.univ.biUnion childrenD_87) := by
  exact envelope_eq_combination childrenD_87 (4, 2) envelope_87
    pivot_mem_87 child_envelope_sub_87 envelope_origin_87
def checked_87 : CheckedCard where
  required := required_87
  envelope := envelope_87
  height := height_87
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_87
def height_101 : ℕ := 3
def childrenH_101 : Fin 2 → ℕ := ![height_0, height_51]
theorem height_exact_101 : height_101 = 1 + Finset.univ.sup childrenH_101 := by decide +kernel
theorem required_origin_101 : ∀ x ∈ required_101,
    (∃ j, x ∈ childrenC_101 j) ∨ ∀ j, x ∈ childrenD_101 j := by decide +kernel
theorem required_exact_101 : required_101 =
    ((Finset.univ.biUnion childrenC_101) ∪ commonEnvelope childrenD_101).erase (0, 3) := by
  exact required_eq_combination childrenC_101 childrenD_101 (0, 3) required_101
    (by decide +kernel) child_required_sub_101 common_sub_101 required_origin_101
theorem envelope_origin_101 : ∀ x ∈ envelope_101,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_101 j := by decide +kernel
theorem envelope_exact_101 : envelope_101 =
    insert (0, 3) (Finset.univ.biUnion childrenD_101) := by
  exact envelope_eq_combination childrenD_101 (0, 3) envelope_101
    pivot_mem_101 child_envelope_sub_101 envelope_origin_101
def checked_101 : CheckedCard where
  required := required_101
  envelope := envelope_101
  height := height_101
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_101
def height_103 : ℕ := 3
def childrenH_103 : Fin 2 → ℕ := ![height_6, height_11]
theorem height_exact_103 : height_103 = 1 + Finset.univ.sup childrenH_103 := by decide +kernel
theorem required_origin_103 : ∀ x ∈ required_103,
    (∃ j, x ∈ childrenC_103 j) ∨ ∀ j, x ∈ childrenD_103 j := by decide +kernel
theorem required_exact_103 : required_103 =
    ((Finset.univ.biUnion childrenC_103) ∪ commonEnvelope childrenD_103).erase (0, 4) := by
  exact required_eq_combination childrenC_103 childrenD_103 (0, 4) required_103
    (by decide +kernel) child_required_sub_103 common_sub_103 required_origin_103
theorem envelope_origin_103 : ∀ x ∈ envelope_103,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_103 j := by decide +kernel
theorem envelope_exact_103 : envelope_103 =
    insert (0, 4) (Finset.univ.biUnion childrenD_103) := by
  exact envelope_eq_combination childrenD_103 (0, 4) envelope_103
    pivot_mem_103 child_envelope_sub_103 envelope_origin_103
def checked_103 : CheckedCard where
  required := required_103
  envelope := envelope_103
  height := height_103
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_103
def height_105 : ℕ := 3
def childrenH_105 : Fin 2 → ℕ := ![height_5, height_11]
theorem height_exact_105 : height_105 = 1 + Finset.univ.sup childrenH_105 := by decide +kernel
theorem required_origin_105 : ∀ x ∈ required_105,
    (∃ j, x ∈ childrenC_105 j) ∨ ∀ j, x ∈ childrenD_105 j := by decide +kernel
theorem required_exact_105 : required_105 =
    ((Finset.univ.biUnion childrenC_105) ∪ commonEnvelope childrenD_105).erase (0, 3) := by
  exact required_eq_combination childrenC_105 childrenD_105 (0, 3) required_105
    (by decide +kernel) child_required_sub_105 common_sub_105 required_origin_105
theorem envelope_origin_105 : ∀ x ∈ envelope_105,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_105 j := by decide +kernel
theorem envelope_exact_105 : envelope_105 =
    insert (0, 3) (Finset.univ.biUnion childrenD_105) := by
  exact envelope_eq_combination childrenD_105 (0, 3) envelope_105
    pivot_mem_105 child_envelope_sub_105 envelope_origin_105
def checked_105 : CheckedCard where
  required := required_105
  envelope := envelope_105
  height := height_105
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_105
end SnakyPrototype.Certificate21

end OAI
