import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_681_i1 : Finset Cell := ⟨(([(2, 4), (3, 4), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_681_i1 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (6, 3), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_681_i1 : Fin 3 → Finset Cell := ![(placed21 7 (5, 6) required_32), (placed21 3 (1, 4) required_44), (placed21 3 (3, 6) required_90)]
def childrenD_681_i1 : Fin 3 → Finset Cell := ![(placed21 7 (5, 6) envelope_32), (placed21 3 (1, 4) envelope_44), (placed21 3 (3, 6) envelope_90)]
theorem common_sub_681_i1 : commonEnvelope childrenD_681_i1 ⊆ insert (4, 3) required_681_i1 := by decide +kernel
theorem child_required_sub_681_i1 : ∀ j, childrenC_681_i1 j ⊆ insert (4, 3) required_681_i1 := by decide +kernel
theorem child_envelope_sub_681_i1 : ∀ j, childrenD_681_i1 j ⊆ envelope_681_i1 := by decide +kernel
theorem pivot_mem_681_i1 : (4, 3) ∈ envelope_681_i1 := by decide +kernel
theorem children_work_681_i1 : ∀ j, Template HasSnaky 4 (childrenC_681_i1 j) (childrenD_681_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_32 7 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_90 3 (3, 6)).mono (by decide +kernel)
theorem row_works_681_i1 : Template HasSnaky 5 required_681_i1 envelope_681_i1 := by
  refine compose HasSnaky 4 childrenC_681_i1 childrenD_681_i1 children_work_681_i1 (4, 3)
    required_681_i1 envelope_681_i1 pivot_mem_681_i1 child_required_sub_681_i1 child_envelope_sub_681_i1 ?_
  intro b hb
  exact common_sub_681_i1 (mem_commonEnvelope childrenD_681_i1 b hb)
def required_681_i2 : Finset Cell := ⟨(([(2, 4), (3, 4), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_681_i2 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_681_i2 : Fin 2 → Finset Cell := ![(placed21 0 (3, 3) required_17), (placed21 7 (5, 6) required_32)]
def childrenD_681_i2 : Fin 2 → Finset Cell := ![(placed21 0 (3, 3) envelope_17), (placed21 7 (5, 6) envelope_32)]
theorem common_sub_681_i2 : commonEnvelope childrenD_681_i2 ⊆ insert (4, 3) required_681_i2 := by decide +kernel
theorem child_required_sub_681_i2 : ∀ j, childrenC_681_i2 j ⊆ insert (4, 3) required_681_i2 := by decide +kernel
theorem child_envelope_sub_681_i2 : ∀ j, childrenD_681_i2 j ⊆ envelope_681_i2 := by decide +kernel
theorem pivot_mem_681_i2 : (4, 3) ∈ envelope_681_i2 := by decide +kernel
theorem children_work_681_i2 : ∀ j, Template HasSnaky 4 (childrenC_681_i2 j) (childrenD_681_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 7 (5, 6)).mono (by decide +kernel)
theorem row_works_681_i2 : Template HasSnaky 5 required_681_i2 envelope_681_i2 := by
  refine compose HasSnaky 4 childrenC_681_i2 childrenD_681_i2 children_work_681_i2 (4, 3)
    required_681_i2 envelope_681_i2 pivot_mem_681_i2 child_required_sub_681_i2 child_envelope_sub_681_i2 ?_
  intro b hb
  exact common_sub_681_i2 (mem_commonEnvelope childrenD_681_i2 b hb)
def required_681_i0 : Finset Cell := ⟨(([(2, 4), (3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_681_i0 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 6), (5, 7), (5, 8), (6, 3), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_681_i0 : Fin 4 → Finset Cell := ![(placed21 6 (4, 7) required_44), (placed21 6 (4, 7) required_52), required_681_i1, required_681_i2]
def childrenD_681_i0 : Fin 4 → Finset Cell := ![(placed21 6 (4, 7) envelope_44), (placed21 6 (4, 7) envelope_52), envelope_681_i1, envelope_681_i2]
theorem common_sub_681_i0 : commonEnvelope childrenD_681_i0 ⊆ insert (4, 6) required_681_i0 := by decide +kernel
theorem child_required_sub_681_i0 : ∀ j, childrenC_681_i0 j ⊆ insert (4, 6) required_681_i0 := by decide +kernel
theorem child_envelope_sub_681_i0 : ∀ j, childrenD_681_i0 j ⊆ envelope_681_i0 := by decide +kernel
theorem pivot_mem_681_i0 : (4, 6) ∈ envelope_681_i0 := by decide +kernel
theorem children_work_681_i0 : ∀ j, Template HasSnaky 5 (childrenC_681_i0 j) (childrenD_681_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (4, 7)).mono (by decide +kernel)
  · exact row_works_681_i1.mono (by decide +kernel)
  · exact row_works_681_i2.mono (by decide +kernel)
theorem row_works_681_i0 : Template HasSnaky 6 required_681_i0 envelope_681_i0 := by
  refine compose HasSnaky 5 childrenC_681_i0 childrenD_681_i0 children_work_681_i0 (4, 6)
    required_681_i0 envelope_681_i0 pivot_mem_681_i0 child_required_sub_681_i0 child_envelope_sub_681_i0 ?_
  intro b hb
  exact common_sub_681_i0 (mem_commonEnvelope childrenD_681_i0 b hb)
def required_681 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_681 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (6, 3), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_681 : Fin 2 → Finset Cell := ![(placed21 1 (0, 4) required_11), required_681_i0]
def childrenD_681 : Fin 2 → Finset Cell := ![(placed21 1 (0, 4) envelope_11), envelope_681_i0]
theorem common_sub_681 : commonEnvelope childrenD_681 ⊆ insert (3, 4) required_681 := by decide +kernel
theorem child_required_sub_681 : ∀ j, childrenC_681 j ⊆ insert (3, 4) required_681 := by decide +kernel
theorem child_envelope_sub_681 : ∀ j, childrenD_681 j ⊆ envelope_681 := by decide +kernel
theorem pivot_mem_681 : (3, 4) ∈ envelope_681 := by decide +kernel
theorem children_work_681 : ∀ j, Template HasSnaky 6 (childrenC_681 j) (childrenD_681 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 1 (0, 4)).mono (by decide +kernel)
  · exact row_works_681_i0.mono (by decide +kernel)
theorem row_works_681 : Template HasSnaky 7 required_681 envelope_681 := by
  refine compose HasSnaky 6 childrenC_681 childrenD_681 children_work_681 (3, 4)
    required_681 envelope_681 pivot_mem_681 child_required_sub_681 child_envelope_sub_681 ?_
  intro b hb
  exact common_sub_681 (mem_commonEnvelope childrenD_681 b hb)
def height_681_i1 : ℕ := 5
def childrenH_681_i1 : Fin 3 → ℕ := ![height_32, height_44, height_90]
theorem height_exact_681_i1 : height_681_i1 = 1 + Finset.univ.sup childrenH_681_i1 := by decide +kernel
theorem required_origin_681_i1 : ∀ x ∈ required_681_i1,
    (∃ j, x ∈ childrenC_681_i1 j) ∨ ∀ j, x ∈ childrenD_681_i1 j := by decide +kernel
theorem required_exact_681_i1 : required_681_i1 =
    ((Finset.univ.biUnion childrenC_681_i1) ∪ commonEnvelope childrenD_681_i1).erase (4, 3) := by
  exact required_eq_combination childrenC_681_i1 childrenD_681_i1 (4, 3) required_681_i1
    (by decide +kernel) child_required_sub_681_i1 common_sub_681_i1 required_origin_681_i1
theorem envelope_origin_681_i1 : ∀ x ∈ envelope_681_i1,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_681_i1 j := by decide +kernel
theorem envelope_exact_681_i1 : envelope_681_i1 =
    insert (4, 3) (Finset.univ.biUnion childrenD_681_i1) := by
  exact envelope_eq_combination childrenD_681_i1 (4, 3) envelope_681_i1
    pivot_mem_681_i1 child_envelope_sub_681_i1 envelope_origin_681_i1
def checked_681_i1 : CheckedCard where
  required := required_681_i1
  envelope := envelope_681_i1
  height := height_681_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_681_i1
def height_681_i2 : ℕ := 5
def childrenH_681_i2 : Fin 2 → ℕ := ![height_17, height_32]
theorem height_exact_681_i2 : height_681_i2 = 1 + Finset.univ.sup childrenH_681_i2 := by decide +kernel
theorem required_origin_681_i2 : ∀ x ∈ required_681_i2,
    (∃ j, x ∈ childrenC_681_i2 j) ∨ ∀ j, x ∈ childrenD_681_i2 j := by decide +kernel
theorem required_exact_681_i2 : required_681_i2 =
    ((Finset.univ.biUnion childrenC_681_i2) ∪ commonEnvelope childrenD_681_i2).erase (4, 3) := by
  exact required_eq_combination childrenC_681_i2 childrenD_681_i2 (4, 3) required_681_i2
    (by decide +kernel) child_required_sub_681_i2 common_sub_681_i2 required_origin_681_i2
theorem envelope_origin_681_i2 : ∀ x ∈ envelope_681_i2,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_681_i2 j := by decide +kernel
theorem envelope_exact_681_i2 : envelope_681_i2 =
    insert (4, 3) (Finset.univ.biUnion childrenD_681_i2) := by
  exact envelope_eq_combination childrenD_681_i2 (4, 3) envelope_681_i2
    pivot_mem_681_i2 child_envelope_sub_681_i2 envelope_origin_681_i2
def checked_681_i2 : CheckedCard where
  required := required_681_i2
  envelope := envelope_681_i2
  height := height_681_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_681_i2
def height_681_i0 : ℕ := 6
def childrenH_681_i0 : Fin 4 → ℕ := ![height_44, height_52, height_681_i1, height_681_i2]
theorem height_exact_681_i0 : height_681_i0 = 1 + Finset.univ.sup childrenH_681_i0 := by decide +kernel
theorem required_origin_681_i0 : ∀ x ∈ required_681_i0,
    (∃ j, x ∈ childrenC_681_i0 j) ∨ ∀ j, x ∈ childrenD_681_i0 j := by decide +kernel
theorem required_exact_681_i0 : required_681_i0 =
    ((Finset.univ.biUnion childrenC_681_i0) ∪ commonEnvelope childrenD_681_i0).erase (4, 6) := by
  exact required_eq_combination childrenC_681_i0 childrenD_681_i0 (4, 6) required_681_i0
    (by decide +kernel) child_required_sub_681_i0 common_sub_681_i0 required_origin_681_i0
theorem envelope_origin_681_i0 : ∀ x ∈ envelope_681_i0,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_681_i0 j := by decide +kernel
theorem envelope_exact_681_i0 : envelope_681_i0 =
    insert (4, 6) (Finset.univ.biUnion childrenD_681_i0) := by
  exact envelope_eq_combination childrenD_681_i0 (4, 6) envelope_681_i0
    pivot_mem_681_i0 child_envelope_sub_681_i0 envelope_origin_681_i0
def checked_681_i0 : CheckedCard where
  required := required_681_i0
  envelope := envelope_681_i0
  height := height_681_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_681_i0
def height_681 : ℕ := 7
def childrenH_681 : Fin 2 → ℕ := ![height_11, height_681_i0]
theorem height_exact_681 : height_681 = 1 + Finset.univ.sup childrenH_681 := by decide +kernel
theorem required_origin_681 : ∀ x ∈ required_681,
    (∃ j, x ∈ childrenC_681 j) ∨ ∀ j, x ∈ childrenD_681 j := by decide +kernel
theorem required_exact_681 : required_681 =
    ((Finset.univ.biUnion childrenC_681) ∪ commonEnvelope childrenD_681).erase (3, 4) := by
  exact required_eq_combination childrenC_681 childrenD_681 (3, 4) required_681
    (by decide +kernel) child_required_sub_681 common_sub_681 required_origin_681
theorem envelope_origin_681 : ∀ x ∈ envelope_681,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_681 j := by decide +kernel
theorem envelope_exact_681 : envelope_681 =
    insert (3, 4) (Finset.univ.biUnion childrenD_681) := by
  exact envelope_eq_combination childrenD_681 (3, 4) envelope_681
    pivot_mem_681 child_envelope_sub_681 envelope_origin_681
def checked_681 : CheckedCard where
  required := required_681
  envelope := envelope_681
  height := height_681
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_681
end SnakyPrototype.Certificate21

end OAI
