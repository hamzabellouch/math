import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_85 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_85 : Finset Cell := ⟨(([(0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 5), (3, 6), (3, 7), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_85 : Fin 3 → Finset Cell := ![(placed21 6 (2, 6) required_15), (placed21 4 (1, 7) required_65), (placed21 3 (0, 5) required_72)]
def childrenD_85 : Fin 3 → Finset Cell := ![(placed21 6 (2, 6) envelope_15), (placed21 4 (1, 7) envelope_65), (placed21 3 (0, 5) envelope_72)]
theorem common_sub_85 : commonEnvelope childrenD_85 ⊆ insert (2, 5) required_85 := by decide +kernel
theorem child_required_sub_85 : ∀ j, childrenC_85 j ⊆ insert (2, 5) required_85 := by decide +kernel
theorem child_envelope_sub_85 : ∀ j, childrenD_85 j ⊆ envelope_85 := by decide +kernel
theorem pivot_mem_85 : (2, 5) ∈ envelope_85 := by decide +kernel
theorem children_work_85 : ∀ j, Template HasSnaky 5 (childrenC_85 j) (childrenD_85 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_65 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_72 3 (0, 5)).mono (by decide +kernel)
theorem row_works_85 : Template HasSnaky 6 required_85 envelope_85 := by
  refine compose HasSnaky 5 childrenC_85 childrenD_85 children_work_85 (2, 5)
    required_85 envelope_85 pivot_mem_85 child_required_sub_85 child_envelope_sub_85 ?_
  intro b hb
  exact common_sub_85 (mem_commonEnvelope childrenD_85 b hb)
def required_95 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_95 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_95 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) required_19), (placed21 4 (0, 7) required_19), (placed21 1 (0, 3) required_49), (placed21 3 (0, 6) required_49)]
def childrenD_95 : Fin 4 → Finset Cell := ![(placed21 0 (0, 2) envelope_19), (placed21 4 (0, 7) envelope_19), (placed21 1 (0, 3) envelope_49), (placed21 3 (0, 6) envelope_49)]
theorem common_sub_95 : commonEnvelope childrenD_95 ⊆ insert (1, 5) required_95 := by decide +kernel
theorem child_required_sub_95 : ∀ j, childrenC_95 j ⊆ insert (1, 5) required_95 := by decide +kernel
theorem child_envelope_sub_95 : ∀ j, childrenD_95 j ⊆ envelope_95 := by decide +kernel
theorem pivot_mem_95 : (1, 5) ∈ envelope_95 := by decide +kernel
theorem children_work_95 : ∀ j, Template HasSnaky 5 (childrenC_95 j) (childrenD_95 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 3 (0, 6)).mono (by decide +kernel)
theorem row_works_95 : Template HasSnaky 6 required_95 envelope_95 := by
  refine compose HasSnaky 5 childrenC_95 childrenD_95 children_work_95 (1, 5)
    required_95 envelope_95 pivot_mem_95 child_required_sub_95 child_envelope_sub_95 ?_
  intro b hb
  exact common_sub_95 (mem_commonEnvelope childrenD_95 b hb)
def required_110 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_110 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_110 : Fin 4 → Finset Cell := ![(placed21 2 (4, 0) required_12), (placed21 5 (4, 2) required_28), (placed21 0 (0, 1) required_58), (placed21 0 (0, 1) required_100)]
def childrenD_110 : Fin 4 → Finset Cell := ![(placed21 2 (4, 0) envelope_12), (placed21 5 (4, 2) envelope_28), (placed21 0 (0, 1) envelope_58), (placed21 0 (0, 1) envelope_100)]
theorem common_sub_110 : commonEnvelope childrenD_110 ⊆ insert (3, 4) required_110 := by decide +kernel
theorem child_required_sub_110 : ∀ j, childrenC_110 j ⊆ insert (3, 4) required_110 := by decide +kernel
theorem child_envelope_sub_110 : ∀ j, childrenD_110 j ⊆ envelope_110 := by decide +kernel
theorem pivot_mem_110 : (3, 4) ∈ envelope_110 := by decide +kernel
theorem children_work_110 : ∀ j, Template HasSnaky 5 (childrenC_110 j) (childrenD_110 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_28 5 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_100 0 (0, 1)).mono (by decide +kernel)
theorem row_works_110 : Template HasSnaky 6 required_110 envelope_110 := by
  refine compose HasSnaky 5 childrenC_110 childrenD_110 children_work_110 (3, 4)
    required_110 envelope_110 pivot_mem_110 child_required_sub_110 child_envelope_sub_110 ?_
  intro b hb
  exact common_sub_110 (mem_commonEnvelope childrenD_110 b hb)
def required_115 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_115 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_115 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), required_114]
def childrenD_115 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), envelope_114]
theorem common_sub_115 : commonEnvelope childrenD_115 ⊆ insert (3, 2) required_115 := by decide +kernel
theorem child_required_sub_115 : ∀ j, childrenC_115 j ⊆ insert (3, 2) required_115 := by decide +kernel
theorem child_envelope_sub_115 : ∀ j, childrenD_115 j ⊆ envelope_115 := by decide +kernel
theorem pivot_mem_115 : (3, 2) ∈ envelope_115 := by decide +kernel
theorem children_work_115 : ∀ j, Template HasSnaky 5 (childrenC_115 j) (childrenD_115 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact row_works_114.mono (by decide +kernel)
theorem row_works_115 : Template HasSnaky 6 required_115 envelope_115 := by
  refine compose HasSnaky 5 childrenC_115 childrenD_115 children_work_115 (3, 2)
    required_115 envelope_115 pivot_mem_115 child_required_sub_115 child_envelope_sub_115 ?_
  intro b hb
  exact common_sub_115 (mem_commonEnvelope childrenD_115 b hb)
def required_119 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_119 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_119 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), required_114]
def childrenD_119 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), envelope_114]
theorem common_sub_119 : commonEnvelope childrenD_119 ⊆ insert (2, 3) required_119 := by decide +kernel
theorem child_required_sub_119 : ∀ j, childrenC_119 j ⊆ insert (2, 3) required_119 := by decide +kernel
theorem child_envelope_sub_119 : ∀ j, childrenD_119 j ⊆ envelope_119 := by decide +kernel
theorem pivot_mem_119 : (2, 3) ∈ envelope_119 := by decide +kernel
theorem children_work_119 : ∀ j, Template HasSnaky 5 (childrenC_119 j) (childrenD_119 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact row_works_114.mono (by decide +kernel)
theorem row_works_119 : Template HasSnaky 6 required_119 envelope_119 := by
  refine compose HasSnaky 5 childrenC_119 childrenD_119 children_work_119 (2, 3)
    required_119 envelope_119 pivot_mem_119 child_required_sub_119 child_envelope_sub_119 ?_
  intro b hb
  exact common_sub_119 (mem_commonEnvelope childrenD_119 b hb)
def required_134 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_134 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_134 : Fin 3 → Finset Cell := ![(placed21 1 (1, 2) required_16), (placed21 4 (1, 3) required_24), (placed21 2 (5, 0) required_133)]
def childrenD_134 : Fin 3 → Finset Cell := ![(placed21 1 (1, 2) envelope_16), (placed21 4 (1, 3) envelope_24), (placed21 2 (5, 0) envelope_133)]
theorem common_sub_134 : commonEnvelope childrenD_134 ⊆ insert (4, 2) required_134 := by decide +kernel
theorem child_required_sub_134 : ∀ j, childrenC_134 j ⊆ insert (4, 2) required_134 := by decide +kernel
theorem child_envelope_sub_134 : ∀ j, childrenD_134 j ⊆ envelope_134 := by decide +kernel
theorem pivot_mem_134 : (4, 2) ∈ envelope_134 := by decide +kernel
theorem children_work_134 : ∀ j, Template HasSnaky 5 (childrenC_134 j) (childrenD_134 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 4 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 2 (5, 0)).mono (by decide +kernel)
theorem row_works_134 : Template HasSnaky 6 required_134 envelope_134 := by
  refine compose HasSnaky 5 childrenC_134 childrenD_134 children_work_134 (4, 2)
    required_134 envelope_134 pivot_mem_134 child_required_sub_134 child_envelope_sub_134 ?_
  intro b hb
  exact common_sub_134 (mem_commonEnvelope childrenD_134 b hb)
def required_135 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_135 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_135 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) required_7), (placed21 6 (3, 6) required_9), (placed21 1 (0, 1) required_133)]
def childrenD_135 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) envelope_7), (placed21 6 (3, 6) envelope_9), (placed21 1 (0, 1) envelope_133)]
theorem common_sub_135 : commonEnvelope childrenD_135 ⊆ insert (2, 5) required_135 := by decide +kernel
theorem child_required_sub_135 : ∀ j, childrenC_135 j ⊆ insert (2, 5) required_135 := by decide +kernel
theorem child_envelope_sub_135 : ∀ j, childrenD_135 j ⊆ envelope_135 := by decide +kernel
theorem pivot_mem_135 : (2, 5) ∈ envelope_135 := by decide +kernel
theorem children_work_135 : ∀ j, Template HasSnaky 5 (childrenC_135 j) (childrenD_135 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 1 (0, 1)).mono (by decide +kernel)
theorem row_works_135 : Template HasSnaky 6 required_135 envelope_135 := by
  refine compose HasSnaky 5 childrenC_135 childrenD_135 children_work_135 (2, 5)
    required_135 envelope_135 pivot_mem_135 child_required_sub_135 child_envelope_sub_135 ?_
  intro b hb
  exact common_sub_135 (mem_commonEnvelope childrenD_135 b hb)
def required_136 : Finset Cell := ⟨(([(1, 2), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_136 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_136 : Fin 3 → Finset Cell := ![(placed21 2 (2, 1) required_21), (placed21 0 (1, 1) required_37), (placed21 3 (0, 5) required_133)]
def childrenD_136 : Fin 3 → Finset Cell := ![(placed21 2 (2, 1) envelope_21), (placed21 0 (1, 1) envelope_37), (placed21 3 (0, 5) envelope_133)]
theorem common_sub_136 : commonEnvelope childrenD_136 ⊆ insert (2, 4) required_136 := by decide +kernel
theorem child_required_sub_136 : ∀ j, childrenC_136 j ⊆ insert (2, 4) required_136 := by decide +kernel
theorem child_envelope_sub_136 : ∀ j, childrenD_136 j ⊆ envelope_136 := by decide +kernel
theorem pivot_mem_136 : (2, 4) ∈ envelope_136 := by decide +kernel
theorem children_work_136 : ∀ j, Template HasSnaky 5 (childrenC_136 j) (childrenD_136 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 3 (0, 5)).mono (by decide +kernel)
theorem row_works_136 : Template HasSnaky 6 required_136 envelope_136 := by
  refine compose HasSnaky 5 childrenC_136 childrenD_136 children_work_136 (2, 4)
    required_136 envelope_136 pivot_mem_136 child_required_sub_136 child_envelope_sub_136 ?_
  intro b hb
  exact common_sub_136 (mem_commonEnvelope childrenD_136 b hb)
def required_137 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_137 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_137 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_7), (placed21 3 (0, 3) required_9), (placed21 2 (5, 0) required_133)]
def childrenD_137 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_7), (placed21 3 (0, 3) envelope_9), (placed21 2 (5, 0) envelope_133)]
theorem common_sub_137 : commonEnvelope childrenD_137 ⊆ insert (4, 2) required_137 := by decide +kernel
theorem child_required_sub_137 : ∀ j, childrenC_137 j ⊆ insert (4, 2) required_137 := by decide +kernel
theorem child_envelope_sub_137 : ∀ j, childrenD_137 j ⊆ envelope_137 := by decide +kernel
theorem pivot_mem_137 : (4, 2) ∈ envelope_137 := by decide +kernel
theorem children_work_137 : ∀ j, Template HasSnaky 5 (childrenC_137 j) (childrenD_137 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 2 (5, 0)).mono (by decide +kernel)
theorem row_works_137 : Template HasSnaky 6 required_137 envelope_137 := by
  refine compose HasSnaky 5 childrenC_137 childrenD_137 children_work_137 (4, 2)
    required_137 envelope_137 pivot_mem_137 child_required_sub_137 child_envelope_sub_137 ?_
  intro b hb
  exact common_sub_137 (mem_commonEnvelope childrenD_137 b hb)
def required_161 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_161 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (4, 3), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_161 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) required_6), required_142]
def childrenD_161 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) envelope_6), envelope_142]
theorem common_sub_161 : commonEnvelope childrenD_161 ⊆ insert (4, 3) required_161 := by decide +kernel
theorem child_required_sub_161 : ∀ j, childrenC_161 j ⊆ insert (4, 3) required_161 := by decide +kernel
theorem child_envelope_sub_161 : ∀ j, childrenD_161 j ⊆ envelope_161 := by decide +kernel
theorem pivot_mem_161 : (4, 3) ∈ envelope_161 := by decide +kernel
theorem children_work_161 : ∀ j, Template HasSnaky 5 (childrenC_161 j) (childrenD_161 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 3)).mono (by decide +kernel)
  · exact row_works_142.mono (by decide +kernel)
theorem row_works_161 : Template HasSnaky 6 required_161 envelope_161 := by
  refine compose HasSnaky 5 childrenC_161 childrenD_161 children_work_161 (4, 3)
    required_161 envelope_161 pivot_mem_161 child_required_sub_161 child_envelope_sub_161 ?_
  intro b hb
  exact common_sub_161 (mem_commonEnvelope childrenD_161 b hb)
def required_162 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_162 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_162 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) required_6), required_142]
def childrenD_162 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) envelope_6), envelope_142]
theorem common_sub_162 : commonEnvelope childrenD_162 ⊆ insert (4, 3) required_162 := by decide +kernel
theorem child_required_sub_162 : ∀ j, childrenC_162 j ⊆ insert (4, 3) required_162 := by decide +kernel
theorem child_envelope_sub_162 : ∀ j, childrenD_162 j ⊆ envelope_162 := by decide +kernel
theorem pivot_mem_162 : (4, 3) ∈ envelope_162 := by decide +kernel
theorem children_work_162 : ∀ j, Template HasSnaky 5 (childrenC_162 j) (childrenD_162 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact row_works_142.mono (by decide +kernel)
theorem row_works_162 : Template HasSnaky 6 required_162 envelope_162 := by
  refine compose HasSnaky 5 childrenC_162 childrenD_162 children_work_162 (4, 3)
    required_162 envelope_162 pivot_mem_162 child_required_sub_162 child_envelope_sub_162 ?_
  intro b hb
  exact common_sub_162 (mem_commonEnvelope childrenD_162 b hb)
def required_166 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_166 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_166 : Fin 4 → Finset Cell := ![(placed21 2 (4, 0) required_14), (placed21 5 (4, 2) required_28), (placed21 0 (0, 1) required_58), (placed21 0 (0, 1) required_100)]
def childrenD_166 : Fin 4 → Finset Cell := ![(placed21 2 (4, 0) envelope_14), (placed21 5 (4, 2) envelope_28), (placed21 0 (0, 1) envelope_58), (placed21 0 (0, 1) envelope_100)]
theorem common_sub_166 : commonEnvelope childrenD_166 ⊆ insert (3, 3) required_166 := by decide +kernel
theorem child_required_sub_166 : ∀ j, childrenC_166 j ⊆ insert (3, 3) required_166 := by decide +kernel
theorem child_envelope_sub_166 : ∀ j, childrenD_166 j ⊆ envelope_166 := by decide +kernel
theorem pivot_mem_166 : (3, 3) ∈ envelope_166 := by decide +kernel
theorem children_work_166 : ∀ j, Template HasSnaky 5 (childrenC_166 j) (childrenD_166 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_28 5 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_100 0 (0, 1)).mono (by decide +kernel)
theorem row_works_166 : Template HasSnaky 6 required_166 envelope_166 := by
  refine compose HasSnaky 5 childrenC_166 childrenD_166 children_work_166 (3, 3)
    required_166 envelope_166 pivot_mem_166 child_required_sub_166 child_envelope_sub_166 ?_
  intro b hb
  exact common_sub_166 (mem_commonEnvelope childrenD_166 b hb)
def required_167 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 1), (3, 1), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_167 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_167 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 3 (0, 5) required_152)]
def childrenD_167 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 3 (0, 5) envelope_152)]
theorem common_sub_167 : commonEnvelope childrenD_167 ⊆ insert (3, 2) required_167 := by decide +kernel
theorem child_required_sub_167 : ∀ j, childrenC_167 j ⊆ insert (3, 2) required_167 := by decide +kernel
theorem child_envelope_sub_167 : ∀ j, childrenD_167 j ⊆ envelope_167 := by decide +kernel
theorem pivot_mem_167 : (3, 2) ∈ envelope_167 := by decide +kernel
theorem children_work_167 : ∀ j, Template HasSnaky 5 (childrenC_167 j) (childrenD_167 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_152 3 (0, 5)).mono (by decide +kernel)
theorem row_works_167 : Template HasSnaky 6 required_167 envelope_167 := by
  refine compose HasSnaky 5 childrenC_167 childrenD_167 children_work_167 (3, 2)
    required_167 envelope_167 pivot_mem_167 child_required_sub_167 child_envelope_sub_167 ?_
  intro b hb
  exact common_sub_167 (mem_commonEnvelope childrenD_167 b hb)
def required_172 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_172 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_172 : Fin 2 → Finset Cell := ![required_142, (placed21 6 (5, 6) required_142)]
def childrenD_172 : Fin 2 → Finset Cell := ![envelope_142, (placed21 6 (5, 6) envelope_142)]
theorem common_sub_172 : commonEnvelope childrenD_172 ⊆ insert (4, 3) required_172 := by decide +kernel
theorem child_required_sub_172 : ∀ j, childrenC_172 j ⊆ insert (4, 3) required_172 := by decide +kernel
theorem child_envelope_sub_172 : ∀ j, childrenD_172 j ⊆ envelope_172 := by decide +kernel
theorem pivot_mem_172 : (4, 3) ∈ envelope_172 := by decide +kernel
theorem children_work_172 : ∀ j, Template HasSnaky 5 (childrenC_172 j) (childrenD_172 j) := by
  intro j
  fin_cases j
  · exact row_works_142.mono (by decide +kernel)
  · exact (placed21_template row_works_142 6 (5, 6)).mono (by decide +kernel)
theorem row_works_172 : Template HasSnaky 6 required_172 envelope_172 := by
  refine compose HasSnaky 5 childrenC_172 childrenD_172 children_work_172 (4, 3)
    required_172 envelope_172 pivot_mem_172 child_required_sub_172 child_envelope_sub_172 ?_
  intro b hb
  exact common_sub_172 (mem_commonEnvelope childrenD_172 b hb)
def required_173 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_173 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_173 : Fin 2 → Finset Cell := ![required_142, (placed21 2 (5, 0) required_142)]
def childrenD_173 : Fin 2 → Finset Cell := ![envelope_142, (placed21 2 (5, 0) envelope_142)]
theorem common_sub_173 : commonEnvelope childrenD_173 ⊆ insert (4, 3) required_173 := by decide +kernel
theorem child_required_sub_173 : ∀ j, childrenC_173 j ⊆ insert (4, 3) required_173 := by decide +kernel
theorem child_envelope_sub_173 : ∀ j, childrenD_173 j ⊆ envelope_173 := by decide +kernel
theorem pivot_mem_173 : (4, 3) ∈ envelope_173 := by decide +kernel
theorem children_work_173 : ∀ j, Template HasSnaky 5 (childrenC_173 j) (childrenD_173 j) := by
  intro j
  fin_cases j
  · exact row_works_142.mono (by decide +kernel)
  · exact (placed21_template row_works_142 2 (5, 0)).mono (by decide +kernel)
theorem row_works_173 : Template HasSnaky 6 required_173 envelope_173 := by
  refine compose HasSnaky 5 childrenC_173 childrenD_173 children_work_173 (4, 3)
    required_173 envelope_173 pivot_mem_173 child_required_sub_173 child_envelope_sub_173 ?_
  intro b hb
  exact common_sub_173 (mem_commonEnvelope childrenD_173 b hb)
def required_180 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_180 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_180 : Fin 3 → Finset Cell := ![(placed21 1 (1, 2) required_16), (placed21 4 (1, 3) required_24), (placed21 2 (5, 0) required_179)]
def childrenD_180 : Fin 3 → Finset Cell := ![(placed21 1 (1, 2) envelope_16), (placed21 4 (1, 3) envelope_24), (placed21 2 (5, 0) envelope_179)]
theorem common_sub_180 : commonEnvelope childrenD_180 ⊆ insert (4, 2) required_180 := by decide +kernel
theorem child_required_sub_180 : ∀ j, childrenC_180 j ⊆ insert (4, 2) required_180 := by decide +kernel
theorem child_envelope_sub_180 : ∀ j, childrenD_180 j ⊆ envelope_180 := by decide +kernel
theorem pivot_mem_180 : (4, 2) ∈ envelope_180 := by decide +kernel
theorem children_work_180 : ∀ j, Template HasSnaky 5 (childrenC_180 j) (childrenD_180 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 4 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 2 (5, 0)).mono (by decide +kernel)
theorem row_works_180 : Template HasSnaky 6 required_180 envelope_180 := by
  refine compose HasSnaky 5 childrenC_180 childrenD_180 children_work_180 (4, 2)
    required_180 envelope_180 pivot_mem_180 child_required_sub_180 child_envelope_sub_180 ?_
  intro b hb
  exact common_sub_180 (mem_commonEnvelope childrenD_180 b hb)
def required_181 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_181 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_181 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) required_7), (placed21 3 (0, 3) required_9), (placed21 2 (5, 0) required_179)]
def childrenD_181 : Fin 3 → Finset Cell := ![(placed21 1 (0, 2) envelope_7), (placed21 3 (0, 3) envelope_9), (placed21 2 (5, 0) envelope_179)]
theorem common_sub_181 : commonEnvelope childrenD_181 ⊆ insert (4, 2) required_181 := by decide +kernel
theorem child_required_sub_181 : ∀ j, childrenC_181 j ⊆ insert (4, 2) required_181 := by decide +kernel
theorem child_envelope_sub_181 : ∀ j, childrenD_181 j ⊆ envelope_181 := by decide +kernel
theorem pivot_mem_181 : (4, 2) ∈ envelope_181 := by decide +kernel
theorem children_work_181 : ∀ j, Template HasSnaky 5 (childrenC_181 j) (childrenD_181 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 2 (5, 0)).mono (by decide +kernel)
theorem row_works_181 : Template HasSnaky 6 required_181 envelope_181 := by
  refine compose HasSnaky 5 childrenC_181 childrenD_181 children_work_181 (4, 2)
    required_181 envelope_181 pivot_mem_181 child_required_sub_181 child_envelope_sub_181 ?_
  intro b hb
  exact common_sub_181 (mem_commonEnvelope childrenD_181 b hb)
def required_182 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_182 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_182 : Fin 3 → Finset Cell := ![(placed21 4 (2, 6) required_7), (placed21 0 (1, 1) required_9), (placed21 1 (0, 1) required_179)]
def childrenD_182 : Fin 3 → Finset Cell := ![(placed21 4 (2, 6) envelope_7), (placed21 0 (1, 1) envelope_9), (placed21 1 (0, 1) envelope_179)]
theorem common_sub_182 : commonEnvelope childrenD_182 ⊆ insert (2, 5) required_182 := by decide +kernel
theorem child_required_sub_182 : ∀ j, childrenC_182 j ⊆ insert (2, 5) required_182 := by decide +kernel
theorem child_envelope_sub_182 : ∀ j, childrenD_182 j ⊆ envelope_182 := by decide +kernel
theorem pivot_mem_182 : (2, 5) ∈ envelope_182 := by decide +kernel
theorem children_work_182 : ∀ j, Template HasSnaky 5 (childrenC_182 j) (childrenD_182 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 1 (0, 1)).mono (by decide +kernel)
theorem row_works_182 : Template HasSnaky 6 required_182 envelope_182 := by
  refine compose HasSnaky 5 childrenC_182 childrenD_182 children_work_182 (2, 5)
    required_182 envelope_182 pivot_mem_182 child_required_sub_182 child_envelope_sub_182 ?_
  intro b hb
  exact common_sub_182 (mem_commonEnvelope childrenD_182 b hb)
def required_184 : Finset Cell := ⟨(([(1, 1), (1, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_184 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_184 : Fin 2 → Finset Cell := ![(placed21 2 (4, 0) required_99), (placed21 6 (5, 5) required_179)]
def childrenD_184 : Fin 2 → Finset Cell := ![(placed21 2 (4, 0) envelope_99), (placed21 6 (5, 5) envelope_179)]
theorem common_sub_184 : commonEnvelope childrenD_184 ⊆ insert (2, 3) required_184 := by decide +kernel
theorem child_required_sub_184 : ∀ j, childrenC_184 j ⊆ insert (2, 3) required_184 := by decide +kernel
theorem child_envelope_sub_184 : ∀ j, childrenD_184 j ⊆ envelope_184 := by decide +kernel
theorem pivot_mem_184 : (2, 3) ∈ envelope_184 := by decide +kernel
theorem children_work_184 : ∀ j, Template HasSnaky 5 (childrenC_184 j) (childrenD_184 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_99 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 6 (5, 5)).mono (by decide +kernel)
theorem row_works_184 : Template HasSnaky 6 required_184 envelope_184 := by
  refine compose HasSnaky 5 childrenC_184 childrenD_184 children_work_184 (2, 3)
    required_184 envelope_184 pivot_mem_184 child_required_sub_184 child_envelope_sub_184 ?_
  intro b hb
  exact common_sub_184 (mem_commonEnvelope childrenD_184 b hb)
def required_188 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_188 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_188 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) required_8), (placed21 5 (3, 2) required_26), (placed21 3 (0, 6) required_133), (placed21 4 (1, 7) required_186), (placed21 0 (2, 0) required_187)]
def childrenD_188 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) envelope_8), (placed21 5 (3, 2) envelope_26), (placed21 3 (0, 6) envelope_133), (placed21 4 (1, 7) envelope_186), (placed21 0 (2, 0) envelope_187)]
theorem common_sub_188 : commonEnvelope childrenD_188 ⊆ insert (2, 5) required_188 := by decide +kernel
theorem child_required_sub_188 : ∀ j, childrenC_188 j ⊆ insert (2, 5) required_188 := by decide +kernel
theorem child_envelope_sub_188 : ∀ j, childrenD_188 j ⊆ envelope_188 := by decide +kernel
theorem pivot_mem_188 : (2, 5) ∈ envelope_188 := by decide +kernel
theorem children_work_188 : ∀ j, Template HasSnaky 5 (childrenC_188 j) (childrenD_188 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 5 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_186 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_187 0 (2, 0)).mono (by decide +kernel)
theorem row_works_188 : Template HasSnaky 6 required_188 envelope_188 := by
  refine compose HasSnaky 5 childrenC_188 childrenD_188 children_work_188 (2, 5)
    required_188 envelope_188 pivot_mem_188 child_required_sub_188 child_envelope_sub_188 ?_
  intro b hb
  exact common_sub_188 (mem_commonEnvelope childrenD_188 b hb)
def required_189 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_189 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_189 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) required_8), (placed21 1 (0, 2) required_26), (placed21 4 (0, 6) required_62), (placed21 6 (2, 7) required_186), (placed21 2 (1, 0) required_187)]
def childrenD_189 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) envelope_8), (placed21 1 (0, 2) envelope_26), (placed21 4 (0, 6) envelope_62), (placed21 6 (2, 7) envelope_186), (placed21 2 (1, 0) envelope_187)]
theorem common_sub_189 : commonEnvelope childrenD_189 ⊆ insert (1, 5) required_189 := by decide +kernel
theorem child_required_sub_189 : ∀ j, childrenC_189 j ⊆ insert (1, 5) required_189 := by decide +kernel
theorem child_envelope_sub_189 : ∀ j, childrenD_189 j ⊆ envelope_189 := by decide +kernel
theorem pivot_mem_189 : (1, 5) ∈ envelope_189 := by decide +kernel
theorem children_work_189 : ∀ j, Template HasSnaky 5 (childrenC_189 j) (childrenD_189 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_62 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_186 6 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_187 2 (1, 0)).mono (by decide +kernel)
theorem row_works_189 : Template HasSnaky 6 required_189 envelope_189 := by
  refine compose HasSnaky 5 childrenC_189 childrenD_189 children_work_189 (1, 5)
    required_189 envelope_189 pivot_mem_189 child_required_sub_189 child_envelope_sub_189 ?_
  intro b hb
  exact common_sub_189 (mem_commonEnvelope childrenD_189 b hb)
def required_190 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_190 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_190 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) required_8), (placed21 1 (1, 2) required_26), (placed21 3 (0, 6) required_179), (placed21 6 (3, 7) required_186), (placed21 2 (2, 0) required_187)]
def childrenD_190 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) envelope_8), (placed21 1 (1, 2) envelope_26), (placed21 3 (0, 6) envelope_179), (placed21 6 (3, 7) envelope_186), (placed21 2 (2, 0) envelope_187)]
theorem common_sub_190 : commonEnvelope childrenD_190 ⊆ insert (2, 5) required_190 := by decide +kernel
theorem child_required_sub_190 : ∀ j, childrenC_190 j ⊆ insert (2, 5) required_190 := by decide +kernel
theorem child_envelope_sub_190 : ∀ j, childrenD_190 j ⊆ envelope_190 := by decide +kernel
theorem pivot_mem_190 : (2, 5) ∈ envelope_190 := by decide +kernel
theorem children_work_190 : ∀ j, Template HasSnaky 5 (childrenC_190 j) (childrenD_190 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_186 6 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_187 2 (2, 0)).mono (by decide +kernel)
theorem row_works_190 : Template HasSnaky 6 required_190 envelope_190 := by
  refine compose HasSnaky 5 childrenC_190 childrenD_190 children_work_190 (2, 5)
    required_190 envelope_190 pivot_mem_190 child_required_sub_190 child_envelope_sub_190 ?_
  intro b hb
  exact common_sub_190 (mem_commonEnvelope childrenD_190 b hb)
def required_192 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_192 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_192 : Fin 5 → Finset Cell := ![(placed21 0 (0, 1) required_9), (placed21 6 (2, 6) required_9), required_186, (placed21 0 (1, 0) required_187), (placed21 0 (0, 1) required_191)]
def childrenD_192 : Fin 5 → Finset Cell := ![(placed21 0 (0, 1) envelope_9), (placed21 6 (2, 6) envelope_9), envelope_186, (placed21 0 (1, 0) envelope_187), (placed21 0 (0, 1) envelope_191)]
theorem common_sub_192 : commonEnvelope childrenD_192 ⊆ insert (1, 5) required_192 := by decide +kernel
theorem child_required_sub_192 : ∀ j, childrenC_192 j ⊆ insert (1, 5) required_192 := by decide +kernel
theorem child_envelope_sub_192 : ∀ j, childrenD_192 j ⊆ envelope_192 := by decide +kernel
theorem pivot_mem_192 : (1, 5) ∈ envelope_192 := by decide +kernel
theorem children_work_192 : ∀ j, Template HasSnaky 5 (childrenC_192 j) (childrenD_192 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (2, 6)).mono (by decide +kernel)
  · exact row_works_186.mono (by decide +kernel)
  · exact (placed21_template row_works_187 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_191 0 (0, 1)).mono (by decide +kernel)
theorem row_works_192 : Template HasSnaky 6 required_192 envelope_192 := by
  refine compose HasSnaky 5 childrenC_192 childrenD_192 children_work_192 (1, 5)
    required_192 envelope_192 pivot_mem_192 child_required_sub_192 child_envelope_sub_192 ?_
  intro b hb
  exact common_sub_192 (mem_commonEnvelope childrenD_192 b hb)
def height_85 : ℕ := 6
def childrenH_85 : Fin 3 → ℕ := ![height_15, height_65, height_72]
theorem height_exact_85 : height_85 = 1 + Finset.univ.sup childrenH_85 := by decide +kernel
theorem required_origin_85 : ∀ x ∈ required_85,
    (∃ j, x ∈ childrenC_85 j) ∨ ∀ j, x ∈ childrenD_85 j := by decide +kernel
theorem required_exact_85 : required_85 =
    ((Finset.univ.biUnion childrenC_85) ∪ commonEnvelope childrenD_85).erase (2, 5) := by
  exact required_eq_combination childrenC_85 childrenD_85 (2, 5) required_85
    (by decide +kernel) child_required_sub_85 common_sub_85 required_origin_85
theorem envelope_origin_85 : ∀ x ∈ envelope_85,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_85 j := by decide +kernel
theorem envelope_exact_85 : envelope_85 =
    insert (2, 5) (Finset.univ.biUnion childrenD_85) := by
  exact envelope_eq_combination childrenD_85 (2, 5) envelope_85
    pivot_mem_85 child_envelope_sub_85 envelope_origin_85
def checked_85 : CheckedCard where
  required := required_85
  envelope := envelope_85
  height := height_85
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_85
def height_95 : ℕ := 6
def childrenH_95 : Fin 4 → ℕ := ![height_19, height_19, height_49, height_49]
theorem height_exact_95 : height_95 = 1 + Finset.univ.sup childrenH_95 := by decide +kernel
theorem required_origin_95 : ∀ x ∈ required_95,
    (∃ j, x ∈ childrenC_95 j) ∨ ∀ j, x ∈ childrenD_95 j := by decide +kernel
theorem required_exact_95 : required_95 =
    ((Finset.univ.biUnion childrenC_95) ∪ commonEnvelope childrenD_95).erase (1, 5) := by
  exact required_eq_combination childrenC_95 childrenD_95 (1, 5) required_95
    (by decide +kernel) child_required_sub_95 common_sub_95 required_origin_95
theorem envelope_origin_95 : ∀ x ∈ envelope_95,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_95 j := by decide +kernel
theorem envelope_exact_95 : envelope_95 =
    insert (1, 5) (Finset.univ.biUnion childrenD_95) := by
  exact envelope_eq_combination childrenD_95 (1, 5) envelope_95
    pivot_mem_95 child_envelope_sub_95 envelope_origin_95
def checked_95 : CheckedCard where
  required := required_95
  envelope := envelope_95
  height := height_95
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_95
def height_110 : ℕ := 6
def childrenH_110 : Fin 4 → ℕ := ![height_12, height_28, height_58, height_100]
theorem height_exact_110 : height_110 = 1 + Finset.univ.sup childrenH_110 := by decide +kernel
theorem required_origin_110 : ∀ x ∈ required_110,
    (∃ j, x ∈ childrenC_110 j) ∨ ∀ j, x ∈ childrenD_110 j := by decide +kernel
theorem required_exact_110 : required_110 =
    ((Finset.univ.biUnion childrenC_110) ∪ commonEnvelope childrenD_110).erase (3, 4) := by
  exact required_eq_combination childrenC_110 childrenD_110 (3, 4) required_110
    (by decide +kernel) child_required_sub_110 common_sub_110 required_origin_110
theorem envelope_origin_110 : ∀ x ∈ envelope_110,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_110 j := by decide +kernel
theorem envelope_exact_110 : envelope_110 =
    insert (3, 4) (Finset.univ.biUnion childrenD_110) := by
  exact envelope_eq_combination childrenD_110 (3, 4) envelope_110
    pivot_mem_110 child_envelope_sub_110 envelope_origin_110
def checked_110 : CheckedCard where
  required := required_110
  envelope := envelope_110
  height := height_110
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_110
def height_115 : ℕ := 6
def childrenH_115 : Fin 2 → ℕ := ![height_5, height_114]
theorem height_exact_115 : height_115 = 1 + Finset.univ.sup childrenH_115 := by decide +kernel
theorem required_origin_115 : ∀ x ∈ required_115,
    (∃ j, x ∈ childrenC_115 j) ∨ ∀ j, x ∈ childrenD_115 j := by decide +kernel
theorem required_exact_115 : required_115 =
    ((Finset.univ.biUnion childrenC_115) ∪ commonEnvelope childrenD_115).erase (3, 2) := by
  exact required_eq_combination childrenC_115 childrenD_115 (3, 2) required_115
    (by decide +kernel) child_required_sub_115 common_sub_115 required_origin_115
theorem envelope_origin_115 : ∀ x ∈ envelope_115,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_115 j := by decide +kernel
theorem envelope_exact_115 : envelope_115 =
    insert (3, 2) (Finset.univ.biUnion childrenD_115) := by
  exact envelope_eq_combination childrenD_115 (3, 2) envelope_115
    pivot_mem_115 child_envelope_sub_115 envelope_origin_115
def checked_115 : CheckedCard where
  required := required_115
  envelope := envelope_115
  height := height_115
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_115
def height_119 : ℕ := 6
def childrenH_119 : Fin 2 → ℕ := ![height_5, height_114]
theorem height_exact_119 : height_119 = 1 + Finset.univ.sup childrenH_119 := by decide +kernel
theorem required_origin_119 : ∀ x ∈ required_119,
    (∃ j, x ∈ childrenC_119 j) ∨ ∀ j, x ∈ childrenD_119 j := by decide +kernel
theorem required_exact_119 : required_119 =
    ((Finset.univ.biUnion childrenC_119) ∪ commonEnvelope childrenD_119).erase (2, 3) := by
  exact required_eq_combination childrenC_119 childrenD_119 (2, 3) required_119
    (by decide +kernel) child_required_sub_119 common_sub_119 required_origin_119
theorem envelope_origin_119 : ∀ x ∈ envelope_119,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_119 j := by decide +kernel
theorem envelope_exact_119 : envelope_119 =
    insert (2, 3) (Finset.univ.biUnion childrenD_119) := by
  exact envelope_eq_combination childrenD_119 (2, 3) envelope_119
    pivot_mem_119 child_envelope_sub_119 envelope_origin_119
def checked_119 : CheckedCard where
  required := required_119
  envelope := envelope_119
  height := height_119
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_119
def height_134 : ℕ := 6
def childrenH_134 : Fin 3 → ℕ := ![height_16, height_24, height_133]
theorem height_exact_134 : height_134 = 1 + Finset.univ.sup childrenH_134 := by decide +kernel
theorem required_origin_134 : ∀ x ∈ required_134,
    (∃ j, x ∈ childrenC_134 j) ∨ ∀ j, x ∈ childrenD_134 j := by decide +kernel
theorem required_exact_134 : required_134 =
    ((Finset.univ.biUnion childrenC_134) ∪ commonEnvelope childrenD_134).erase (4, 2) := by
  exact required_eq_combination childrenC_134 childrenD_134 (4, 2) required_134
    (by decide +kernel) child_required_sub_134 common_sub_134 required_origin_134
theorem envelope_origin_134 : ∀ x ∈ envelope_134,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_134 j := by decide +kernel
theorem envelope_exact_134 : envelope_134 =
    insert (4, 2) (Finset.univ.biUnion childrenD_134) := by
  exact envelope_eq_combination childrenD_134 (4, 2) envelope_134
    pivot_mem_134 child_envelope_sub_134 envelope_origin_134
def checked_134 : CheckedCard where
  required := required_134
  envelope := envelope_134
  height := height_134
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_134
def height_135 : ℕ := 6
def childrenH_135 : Fin 3 → ℕ := ![height_7, height_9, height_133]
theorem height_exact_135 : height_135 = 1 + Finset.univ.sup childrenH_135 := by decide +kernel
theorem required_origin_135 : ∀ x ∈ required_135,
    (∃ j, x ∈ childrenC_135 j) ∨ ∀ j, x ∈ childrenD_135 j := by decide +kernel
theorem required_exact_135 : required_135 =
    ((Finset.univ.biUnion childrenC_135) ∪ commonEnvelope childrenD_135).erase (2, 5) := by
  exact required_eq_combination childrenC_135 childrenD_135 (2, 5) required_135
    (by decide +kernel) child_required_sub_135 common_sub_135 required_origin_135
theorem envelope_origin_135 : ∀ x ∈ envelope_135,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_135 j := by decide +kernel
theorem envelope_exact_135 : envelope_135 =
    insert (2, 5) (Finset.univ.biUnion childrenD_135) := by
  exact envelope_eq_combination childrenD_135 (2, 5) envelope_135
    pivot_mem_135 child_envelope_sub_135 envelope_origin_135
def checked_135 : CheckedCard where
  required := required_135
  envelope := envelope_135
  height := height_135
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_135
def height_136 : ℕ := 6
def childrenH_136 : Fin 3 → ℕ := ![height_21, height_37, height_133]
theorem height_exact_136 : height_136 = 1 + Finset.univ.sup childrenH_136 := by decide +kernel
theorem required_origin_136 : ∀ x ∈ required_136,
    (∃ j, x ∈ childrenC_136 j) ∨ ∀ j, x ∈ childrenD_136 j := by decide +kernel
theorem required_exact_136 : required_136 =
    ((Finset.univ.biUnion childrenC_136) ∪ commonEnvelope childrenD_136).erase (2, 4) := by
  exact required_eq_combination childrenC_136 childrenD_136 (2, 4) required_136
    (by decide +kernel) child_required_sub_136 common_sub_136 required_origin_136
theorem envelope_origin_136 : ∀ x ∈ envelope_136,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_136 j := by decide +kernel
theorem envelope_exact_136 : envelope_136 =
    insert (2, 4) (Finset.univ.biUnion childrenD_136) := by
  exact envelope_eq_combination childrenD_136 (2, 4) envelope_136
    pivot_mem_136 child_envelope_sub_136 envelope_origin_136
def checked_136 : CheckedCard where
  required := required_136
  envelope := envelope_136
  height := height_136
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_136
def height_137 : ℕ := 6
def childrenH_137 : Fin 3 → ℕ := ![height_7, height_9, height_133]
theorem height_exact_137 : height_137 = 1 + Finset.univ.sup childrenH_137 := by decide +kernel
theorem required_origin_137 : ∀ x ∈ required_137,
    (∃ j, x ∈ childrenC_137 j) ∨ ∀ j, x ∈ childrenD_137 j := by decide +kernel
theorem required_exact_137 : required_137 =
    ((Finset.univ.biUnion childrenC_137) ∪ commonEnvelope childrenD_137).erase (4, 2) := by
  exact required_eq_combination childrenC_137 childrenD_137 (4, 2) required_137
    (by decide +kernel) child_required_sub_137 common_sub_137 required_origin_137
theorem envelope_origin_137 : ∀ x ∈ envelope_137,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_137 j := by decide +kernel
theorem envelope_exact_137 : envelope_137 =
    insert (4, 2) (Finset.univ.biUnion childrenD_137) := by
  exact envelope_eq_combination childrenD_137 (4, 2) envelope_137
    pivot_mem_137 child_envelope_sub_137 envelope_origin_137
def checked_137 : CheckedCard where
  required := required_137
  envelope := envelope_137
  height := height_137
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_137
def height_161 : ℕ := 6
def childrenH_161 : Fin 2 → ℕ := ![height_6, height_142]
theorem height_exact_161 : height_161 = 1 + Finset.univ.sup childrenH_161 := by decide +kernel
theorem required_origin_161 : ∀ x ∈ required_161,
    (∃ j, x ∈ childrenC_161 j) ∨ ∀ j, x ∈ childrenD_161 j := by decide +kernel
theorem required_exact_161 : required_161 =
    ((Finset.univ.biUnion childrenC_161) ∪ commonEnvelope childrenD_161).erase (4, 3) := by
  exact required_eq_combination childrenC_161 childrenD_161 (4, 3) required_161
    (by decide +kernel) child_required_sub_161 common_sub_161 required_origin_161
theorem envelope_origin_161 : ∀ x ∈ envelope_161,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_161 j := by decide +kernel
theorem envelope_exact_161 : envelope_161 =
    insert (4, 3) (Finset.univ.biUnion childrenD_161) := by
  exact envelope_eq_combination childrenD_161 (4, 3) envelope_161
    pivot_mem_161 child_envelope_sub_161 envelope_origin_161
def checked_161 : CheckedCard where
  required := required_161
  envelope := envelope_161
  height := height_161
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_161
def height_162 : ℕ := 6
def childrenH_162 : Fin 2 → ℕ := ![height_6, height_142]
theorem height_exact_162 : height_162 = 1 + Finset.univ.sup childrenH_162 := by decide +kernel
theorem required_origin_162 : ∀ x ∈ required_162,
    (∃ j, x ∈ childrenC_162 j) ∨ ∀ j, x ∈ childrenD_162 j := by decide +kernel
theorem required_exact_162 : required_162 =
    ((Finset.univ.biUnion childrenC_162) ∪ commonEnvelope childrenD_162).erase (4, 3) := by
  exact required_eq_combination childrenC_162 childrenD_162 (4, 3) required_162
    (by decide +kernel) child_required_sub_162 common_sub_162 required_origin_162
theorem envelope_origin_162 : ∀ x ∈ envelope_162,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_162 j := by decide +kernel
theorem envelope_exact_162 : envelope_162 =
    insert (4, 3) (Finset.univ.biUnion childrenD_162) := by
  exact envelope_eq_combination childrenD_162 (4, 3) envelope_162
    pivot_mem_162 child_envelope_sub_162 envelope_origin_162
def checked_162 : CheckedCard where
  required := required_162
  envelope := envelope_162
  height := height_162
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_162
def height_166 : ℕ := 6
def childrenH_166 : Fin 4 → ℕ := ![height_14, height_28, height_58, height_100]
theorem height_exact_166 : height_166 = 1 + Finset.univ.sup childrenH_166 := by decide +kernel
theorem required_origin_166 : ∀ x ∈ required_166,
    (∃ j, x ∈ childrenC_166 j) ∨ ∀ j, x ∈ childrenD_166 j := by decide +kernel
theorem required_exact_166 : required_166 =
    ((Finset.univ.biUnion childrenC_166) ∪ commonEnvelope childrenD_166).erase (3, 3) := by
  exact required_eq_combination childrenC_166 childrenD_166 (3, 3) required_166
    (by decide +kernel) child_required_sub_166 common_sub_166 required_origin_166
theorem envelope_origin_166 : ∀ x ∈ envelope_166,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_166 j := by decide +kernel
theorem envelope_exact_166 : envelope_166 =
    insert (3, 3) (Finset.univ.biUnion childrenD_166) := by
  exact envelope_eq_combination childrenD_166 (3, 3) envelope_166
    pivot_mem_166 child_envelope_sub_166 envelope_origin_166
def checked_166 : CheckedCard where
  required := required_166
  envelope := envelope_166
  height := height_166
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_166
def height_167 : ℕ := 6
def childrenH_167 : Fin 2 → ℕ := ![height_5, height_152]
theorem height_exact_167 : height_167 = 1 + Finset.univ.sup childrenH_167 := by decide +kernel
theorem required_origin_167 : ∀ x ∈ required_167,
    (∃ j, x ∈ childrenC_167 j) ∨ ∀ j, x ∈ childrenD_167 j := by decide +kernel
theorem required_exact_167 : required_167 =
    ((Finset.univ.biUnion childrenC_167) ∪ commonEnvelope childrenD_167).erase (3, 2) := by
  exact required_eq_combination childrenC_167 childrenD_167 (3, 2) required_167
    (by decide +kernel) child_required_sub_167 common_sub_167 required_origin_167
theorem envelope_origin_167 : ∀ x ∈ envelope_167,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_167 j := by decide +kernel
theorem envelope_exact_167 : envelope_167 =
    insert (3, 2) (Finset.univ.biUnion childrenD_167) := by
  exact envelope_eq_combination childrenD_167 (3, 2) envelope_167
    pivot_mem_167 child_envelope_sub_167 envelope_origin_167
def checked_167 : CheckedCard where
  required := required_167
  envelope := envelope_167
  height := height_167
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_167
def height_172 : ℕ := 6
def childrenH_172 : Fin 2 → ℕ := ![height_142, height_142]
theorem height_exact_172 : height_172 = 1 + Finset.univ.sup childrenH_172 := by decide +kernel
theorem required_origin_172 : ∀ x ∈ required_172,
    (∃ j, x ∈ childrenC_172 j) ∨ ∀ j, x ∈ childrenD_172 j := by decide +kernel
theorem required_exact_172 : required_172 =
    ((Finset.univ.biUnion childrenC_172) ∪ commonEnvelope childrenD_172).erase (4, 3) := by
  exact required_eq_combination childrenC_172 childrenD_172 (4, 3) required_172
    (by decide +kernel) child_required_sub_172 common_sub_172 required_origin_172
theorem envelope_origin_172 : ∀ x ∈ envelope_172,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_172 j := by decide +kernel
theorem envelope_exact_172 : envelope_172 =
    insert (4, 3) (Finset.univ.biUnion childrenD_172) := by
  exact envelope_eq_combination childrenD_172 (4, 3) envelope_172
    pivot_mem_172 child_envelope_sub_172 envelope_origin_172
def checked_172 : CheckedCard where
  required := required_172
  envelope := envelope_172
  height := height_172
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_172
def height_173 : ℕ := 6
def childrenH_173 : Fin 2 → ℕ := ![height_142, height_142]
theorem height_exact_173 : height_173 = 1 + Finset.univ.sup childrenH_173 := by decide +kernel
theorem required_origin_173 : ∀ x ∈ required_173,
    (∃ j, x ∈ childrenC_173 j) ∨ ∀ j, x ∈ childrenD_173 j := by decide +kernel
theorem required_exact_173 : required_173 =
    ((Finset.univ.biUnion childrenC_173) ∪ commonEnvelope childrenD_173).erase (4, 3) := by
  exact required_eq_combination childrenC_173 childrenD_173 (4, 3) required_173
    (by decide +kernel) child_required_sub_173 common_sub_173 required_origin_173
theorem envelope_origin_173 : ∀ x ∈ envelope_173,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_173 j := by decide +kernel
theorem envelope_exact_173 : envelope_173 =
    insert (4, 3) (Finset.univ.biUnion childrenD_173) := by
  exact envelope_eq_combination childrenD_173 (4, 3) envelope_173
    pivot_mem_173 child_envelope_sub_173 envelope_origin_173
def checked_173 : CheckedCard where
  required := required_173
  envelope := envelope_173
  height := height_173
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_173
def height_180 : ℕ := 6
def childrenH_180 : Fin 3 → ℕ := ![height_16, height_24, height_179]
theorem height_exact_180 : height_180 = 1 + Finset.univ.sup childrenH_180 := by decide +kernel
theorem required_origin_180 : ∀ x ∈ required_180,
    (∃ j, x ∈ childrenC_180 j) ∨ ∀ j, x ∈ childrenD_180 j := by decide +kernel
theorem required_exact_180 : required_180 =
    ((Finset.univ.biUnion childrenC_180) ∪ commonEnvelope childrenD_180).erase (4, 2) := by
  exact required_eq_combination childrenC_180 childrenD_180 (4, 2) required_180
    (by decide +kernel) child_required_sub_180 common_sub_180 required_origin_180
theorem envelope_origin_180 : ∀ x ∈ envelope_180,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_180 j := by decide +kernel
theorem envelope_exact_180 : envelope_180 =
    insert (4, 2) (Finset.univ.biUnion childrenD_180) := by
  exact envelope_eq_combination childrenD_180 (4, 2) envelope_180
    pivot_mem_180 child_envelope_sub_180 envelope_origin_180
def checked_180 : CheckedCard where
  required := required_180
  envelope := envelope_180
  height := height_180
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_180
def height_181 : ℕ := 6
def childrenH_181 : Fin 3 → ℕ := ![height_7, height_9, height_179]
theorem height_exact_181 : height_181 = 1 + Finset.univ.sup childrenH_181 := by decide +kernel
theorem required_origin_181 : ∀ x ∈ required_181,
    (∃ j, x ∈ childrenC_181 j) ∨ ∀ j, x ∈ childrenD_181 j := by decide +kernel
theorem required_exact_181 : required_181 =
    ((Finset.univ.biUnion childrenC_181) ∪ commonEnvelope childrenD_181).erase (4, 2) := by
  exact required_eq_combination childrenC_181 childrenD_181 (4, 2) required_181
    (by decide +kernel) child_required_sub_181 common_sub_181 required_origin_181
theorem envelope_origin_181 : ∀ x ∈ envelope_181,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_181 j := by decide +kernel
theorem envelope_exact_181 : envelope_181 =
    insert (4, 2) (Finset.univ.biUnion childrenD_181) := by
  exact envelope_eq_combination childrenD_181 (4, 2) envelope_181
    pivot_mem_181 child_envelope_sub_181 envelope_origin_181
def checked_181 : CheckedCard where
  required := required_181
  envelope := envelope_181
  height := height_181
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_181
def height_182 : ℕ := 6
def childrenH_182 : Fin 3 → ℕ := ![height_7, height_9, height_179]
theorem height_exact_182 : height_182 = 1 + Finset.univ.sup childrenH_182 := by decide +kernel
theorem required_origin_182 : ∀ x ∈ required_182,
    (∃ j, x ∈ childrenC_182 j) ∨ ∀ j, x ∈ childrenD_182 j := by decide +kernel
theorem required_exact_182 : required_182 =
    ((Finset.univ.biUnion childrenC_182) ∪ commonEnvelope childrenD_182).erase (2, 5) := by
  exact required_eq_combination childrenC_182 childrenD_182 (2, 5) required_182
    (by decide +kernel) child_required_sub_182 common_sub_182 required_origin_182
theorem envelope_origin_182 : ∀ x ∈ envelope_182,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_182 j := by decide +kernel
theorem envelope_exact_182 : envelope_182 =
    insert (2, 5) (Finset.univ.biUnion childrenD_182) := by
  exact envelope_eq_combination childrenD_182 (2, 5) envelope_182
    pivot_mem_182 child_envelope_sub_182 envelope_origin_182
def checked_182 : CheckedCard where
  required := required_182
  envelope := envelope_182
  height := height_182
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_182
def height_184 : ℕ := 6
def childrenH_184 : Fin 2 → ℕ := ![height_99, height_179]
theorem height_exact_184 : height_184 = 1 + Finset.univ.sup childrenH_184 := by decide +kernel
theorem required_origin_184 : ∀ x ∈ required_184,
    (∃ j, x ∈ childrenC_184 j) ∨ ∀ j, x ∈ childrenD_184 j := by decide +kernel
theorem required_exact_184 : required_184 =
    ((Finset.univ.biUnion childrenC_184) ∪ commonEnvelope childrenD_184).erase (2, 3) := by
  exact required_eq_combination childrenC_184 childrenD_184 (2, 3) required_184
    (by decide +kernel) child_required_sub_184 common_sub_184 required_origin_184
theorem envelope_origin_184 : ∀ x ∈ envelope_184,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_184 j := by decide +kernel
theorem envelope_exact_184 : envelope_184 =
    insert (2, 3) (Finset.univ.biUnion childrenD_184) := by
  exact envelope_eq_combination childrenD_184 (2, 3) envelope_184
    pivot_mem_184 child_envelope_sub_184 envelope_origin_184
def checked_184 : CheckedCard where
  required := required_184
  envelope := envelope_184
  height := height_184
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_184
def height_188 : ℕ := 6
def childrenH_188 : Fin 5 → ℕ := ![height_8, height_26, height_133, height_186, height_187]
theorem height_exact_188 : height_188 = 1 + Finset.univ.sup childrenH_188 := by decide +kernel
theorem required_origin_188 : ∀ x ∈ required_188,
    (∃ j, x ∈ childrenC_188 j) ∨ ∀ j, x ∈ childrenD_188 j := by decide +kernel
theorem required_exact_188 : required_188 =
    ((Finset.univ.biUnion childrenC_188) ∪ commonEnvelope childrenD_188).erase (2, 5) := by
  exact required_eq_combination childrenC_188 childrenD_188 (2, 5) required_188
    (by decide +kernel) child_required_sub_188 common_sub_188 required_origin_188
theorem envelope_origin_188 : ∀ x ∈ envelope_188,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_188 j := by decide +kernel
theorem envelope_exact_188 : envelope_188 =
    insert (2, 5) (Finset.univ.biUnion childrenD_188) := by
  exact envelope_eq_combination childrenD_188 (2, 5) envelope_188
    pivot_mem_188 child_envelope_sub_188 envelope_origin_188
def checked_188 : CheckedCard where
  required := required_188
  envelope := envelope_188
  height := height_188
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_188
def height_189 : ℕ := 6
def childrenH_189 : Fin 5 → ℕ := ![height_8, height_26, height_62, height_186, height_187]
theorem height_exact_189 : height_189 = 1 + Finset.univ.sup childrenH_189 := by decide +kernel
theorem required_origin_189 : ∀ x ∈ required_189,
    (∃ j, x ∈ childrenC_189 j) ∨ ∀ j, x ∈ childrenD_189 j := by decide +kernel
theorem required_exact_189 : required_189 =
    ((Finset.univ.biUnion childrenC_189) ∪ commonEnvelope childrenD_189).erase (1, 5) := by
  exact required_eq_combination childrenC_189 childrenD_189 (1, 5) required_189
    (by decide +kernel) child_required_sub_189 common_sub_189 required_origin_189
theorem envelope_origin_189 : ∀ x ∈ envelope_189,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_189 j := by decide +kernel
theorem envelope_exact_189 : envelope_189 =
    insert (1, 5) (Finset.univ.biUnion childrenD_189) := by
  exact envelope_eq_combination childrenD_189 (1, 5) envelope_189
    pivot_mem_189 child_envelope_sub_189 envelope_origin_189
def checked_189 : CheckedCard where
  required := required_189
  envelope := envelope_189
  height := height_189
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_189
def height_190 : ℕ := 6
def childrenH_190 : Fin 5 → ℕ := ![height_8, height_26, height_179, height_186, height_187]
theorem height_exact_190 : height_190 = 1 + Finset.univ.sup childrenH_190 := by decide +kernel
theorem required_origin_190 : ∀ x ∈ required_190,
    (∃ j, x ∈ childrenC_190 j) ∨ ∀ j, x ∈ childrenD_190 j := by decide +kernel
theorem required_exact_190 : required_190 =
    ((Finset.univ.biUnion childrenC_190) ∪ commonEnvelope childrenD_190).erase (2, 5) := by
  exact required_eq_combination childrenC_190 childrenD_190 (2, 5) required_190
    (by decide +kernel) child_required_sub_190 common_sub_190 required_origin_190
theorem envelope_origin_190 : ∀ x ∈ envelope_190,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_190 j := by decide +kernel
theorem envelope_exact_190 : envelope_190 =
    insert (2, 5) (Finset.univ.biUnion childrenD_190) := by
  exact envelope_eq_combination childrenD_190 (2, 5) envelope_190
    pivot_mem_190 child_envelope_sub_190 envelope_origin_190
def checked_190 : CheckedCard where
  required := required_190
  envelope := envelope_190
  height := height_190
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_190
def height_192 : ℕ := 6
def childrenH_192 : Fin 5 → ℕ := ![height_9, height_9, height_186, height_187, height_191]
theorem height_exact_192 : height_192 = 1 + Finset.univ.sup childrenH_192 := by decide +kernel
theorem required_origin_192 : ∀ x ∈ required_192,
    (∃ j, x ∈ childrenC_192 j) ∨ ∀ j, x ∈ childrenD_192 j := by decide +kernel
theorem required_exact_192 : required_192 =
    ((Finset.univ.biUnion childrenC_192) ∪ commonEnvelope childrenD_192).erase (1, 5) := by
  exact required_eq_combination childrenC_192 childrenD_192 (1, 5) required_192
    (by decide +kernel) child_required_sub_192 common_sub_192 required_origin_192
theorem envelope_origin_192 : ∀ x ∈ envelope_192,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_192 j := by decide +kernel
theorem envelope_exact_192 : envelope_192 =
    insert (1, 5) (Finset.univ.biUnion childrenD_192) := by
  exact envelope_eq_combination childrenD_192 (1, 5) envelope_192
    pivot_mem_192 child_envelope_sub_192 envelope_origin_192
def checked_192 : CheckedCard where
  required := required_192
  envelope := envelope_192
  height := height_192
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_192
end SnakyPrototype.Certificate21

end OAI
