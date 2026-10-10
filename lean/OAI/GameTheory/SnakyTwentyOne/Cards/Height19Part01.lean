import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height18Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_694_i0 : Finset Cell := ⟨(([(5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_694_i0 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7), (9, 5), (9, 6), (9, 7), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_694_i0 : Fin 5 → Finset Cell := ![(placed21 4 (4, 11) required_390), (placed21 2 (7, 3) required_544), (placed21 1 (0, 5) required_545), (placed21 5 (9, 5) required_546), (placed21 1 (0, 5) required_549)]
def childrenD_694_i0 : Fin 5 → Finset Cell := ![(placed21 4 (4, 11) envelope_390), (placed21 2 (7, 3) envelope_544), (placed21 1 (0, 5) envelope_545), (placed21 5 (9, 5) envelope_546), (placed21 1 (0, 5) envelope_549)]
theorem common_sub_694_i0 : commonEnvelope childrenD_694_i0 ⊆ insert (4, 6) required_694_i0 := by decide +kernel
theorem child_required_sub_694_i0 : ∀ j, childrenC_694_i0 j ⊆ insert (4, 6) required_694_i0 := by decide +kernel
theorem child_envelope_sub_694_i0 : ∀ j, childrenD_694_i0 j ⊆ envelope_694_i0 := by decide +kernel
theorem pivot_mem_694_i0 : (4, 6) ∈ envelope_694_i0 := by decide +kernel
theorem children_work_694_i0 : ∀ j, Template HasSnaky 10 (childrenC_694_i0 j) (childrenD_694_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_390 4 (4, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_544 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 1 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_546 5 (9, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_549 1 (0, 5)).mono (by decide +kernel)
theorem row_works_694_i0 : Template HasSnaky 11 required_694_i0 envelope_694_i0 := by
  refine compose HasSnaky 10 childrenC_694_i0 childrenD_694_i0 children_work_694_i0 (4, 6)
    required_694_i0 envelope_694_i0 pivot_mem_694_i0 child_required_sub_694_i0 child_envelope_sub_694_i0 ?_
  intro b hb
  exact common_sub_694_i0 (mem_commonEnvelope childrenD_694_i0 b hb)
def required_694_i1 : Finset Cell := ⟨(([(5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_694_i1 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (1, 5), (1, 6), (1, 7), (1, 8), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 9), (4, 10), (4, 11), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (12, 1), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (13, 4), (13, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_694_i1 : Fin 4 → Finset Cell := ![(placed21 4 (5, 8) required_7), (placed21 3 (4, 7) required_26), (placed21 7 (8, 8) required_142), (placed21 3 (0, 11) required_693)]
def childrenD_694_i1 : Fin 4 → Finset Cell := ![(placed21 4 (5, 8) envelope_7), (placed21 3 (4, 7) envelope_26), (placed21 7 (8, 8) envelope_142), (placed21 3 (0, 11) envelope_693)]
theorem common_sub_694_i1 : commonEnvelope childrenD_694_i1 ⊆ insert (5, 4) required_694_i1 := by decide +kernel
theorem child_required_sub_694_i1 : ∀ j, childrenC_694_i1 j ⊆ insert (5, 4) required_694_i1 := by decide +kernel
theorem child_envelope_sub_694_i1 : ∀ j, childrenD_694_i1 j ⊆ envelope_694_i1 := by decide +kernel
theorem pivot_mem_694_i1 : (5, 4) ∈ envelope_694_i1 := by decide +kernel
theorem children_work_694_i1 : ∀ j, Template HasSnaky 14 (childrenC_694_i1 j) (childrenD_694_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 3 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_142 7 (8, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_693 3 (0, 11)).mono (by decide +kernel)
theorem row_works_694_i1 : Template HasSnaky 15 required_694_i1 envelope_694_i1 := by
  refine compose HasSnaky 14 childrenC_694_i1 childrenD_694_i1 children_work_694_i1 (5, 4)
    required_694_i1 envelope_694_i1 pivot_mem_694_i1 child_required_sub_694_i1 child_envelope_sub_694_i1 ?_
  intro b hb
  exact common_sub_694_i1 (mem_commonEnvelope childrenD_694_i1 b hb)
def required_694 : Finset Cell := ⟨(([(5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_694 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (1, 5), (1, 6), (1, 7), (1, 8), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (12, 1), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (13, 4), (13, 5), (13, 6), (13, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_694 : Fin 7 → Finset Cell := ![(placed21 3 (2, 8) required_116), (placed21 2 (7, 3) required_188), (placed21 1 (2, 5) required_397), (placed21 5 (8, 4) required_435), (placed21 0 (2, 2) required_691), required_694_i0, required_694_i1]
def childrenD_694 : Fin 7 → Finset Cell := ![(placed21 3 (2, 8) envelope_116), (placed21 2 (7, 3) envelope_188), (placed21 1 (2, 5) envelope_397), (placed21 5 (8, 4) envelope_435), (placed21 0 (2, 2) envelope_691), envelope_694_i0, envelope_694_i1]
theorem common_sub_694 : commonEnvelope childrenD_694 ⊆ insert (5, 7) required_694 := by decide +kernel
theorem child_required_sub_694 : ∀ j, childrenC_694 j ⊆ insert (5, 7) required_694 := by decide +kernel
theorem child_envelope_sub_694 : ∀ j, childrenD_694 j ⊆ envelope_694 := by decide +kernel
theorem pivot_mem_694 : (5, 7) ∈ envelope_694 := by decide +kernel
theorem children_work_694 : ∀ j, Template HasSnaky 18 (childrenC_694 j) (childrenD_694 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_116 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_397 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_691 0 (2, 2)).mono (by decide +kernel)
  · exact row_works_694_i0.mono (by decide +kernel)
  · exact row_works_694_i1.mono (by decide +kernel)
theorem row_works_694 : Template HasSnaky 19 required_694 envelope_694 := by
  refine compose HasSnaky 18 childrenC_694 childrenD_694 children_work_694 (5, 7)
    required_694 envelope_694 pivot_mem_694 child_required_sub_694 child_envelope_sub_694 ?_
  intro b hb
  exact common_sub_694 (mem_commonEnvelope childrenD_694 b hb)
def height_694_i0 : ℕ := 11
def childrenH_694_i0 : Fin 5 → ℕ := ![height_390, height_544, height_545, height_546, height_549]
theorem height_exact_694_i0 : height_694_i0 = 1 + Finset.univ.sup childrenH_694_i0 := by decide +kernel
theorem required_origin_694_i0 : ∀ x ∈ required_694_i0,
    (∃ j, x ∈ childrenC_694_i0 j) ∨ ∀ j, x ∈ childrenD_694_i0 j := by decide +kernel
theorem required_exact_694_i0 : required_694_i0 =
    ((Finset.univ.biUnion childrenC_694_i0) ∪ commonEnvelope childrenD_694_i0).erase (4, 6) := by
  exact required_eq_combination childrenC_694_i0 childrenD_694_i0 (4, 6) required_694_i0
    (by decide +kernel) child_required_sub_694_i0 common_sub_694_i0 required_origin_694_i0
theorem envelope_origin_694_i0 : ∀ x ∈ envelope_694_i0,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_694_i0 j := by decide +kernel
theorem envelope_exact_694_i0 : envelope_694_i0 =
    insert (4, 6) (Finset.univ.biUnion childrenD_694_i0) := by
  exact envelope_eq_combination childrenD_694_i0 (4, 6) envelope_694_i0
    pivot_mem_694_i0 child_envelope_sub_694_i0 envelope_origin_694_i0
def checked_694_i0 : CheckedCard where
  required := required_694_i0
  envelope := envelope_694_i0
  height := height_694_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_694_i0
def height_694_i1 : ℕ := 15
def childrenH_694_i1 : Fin 4 → ℕ := ![height_7, height_26, height_142, height_693]
theorem height_exact_694_i1 : height_694_i1 = 1 + Finset.univ.sup childrenH_694_i1 := by decide +kernel
theorem required_origin_694_i1 : ∀ x ∈ required_694_i1,
    (∃ j, x ∈ childrenC_694_i1 j) ∨ ∀ j, x ∈ childrenD_694_i1 j := by decide +kernel
theorem required_exact_694_i1 : required_694_i1 =
    ((Finset.univ.biUnion childrenC_694_i1) ∪ commonEnvelope childrenD_694_i1).erase (5, 4) := by
  exact required_eq_combination childrenC_694_i1 childrenD_694_i1 (5, 4) required_694_i1
    (by decide +kernel) child_required_sub_694_i1 common_sub_694_i1 required_origin_694_i1
theorem envelope_origin_694_i1 : ∀ x ∈ envelope_694_i1,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_694_i1 j := by decide +kernel
theorem envelope_exact_694_i1 : envelope_694_i1 =
    insert (5, 4) (Finset.univ.biUnion childrenD_694_i1) := by
  exact envelope_eq_combination childrenD_694_i1 (5, 4) envelope_694_i1
    pivot_mem_694_i1 child_envelope_sub_694_i1 envelope_origin_694_i1
def checked_694_i1 : CheckedCard where
  required := required_694_i1
  envelope := envelope_694_i1
  height := height_694_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_694_i1
def height_694 : ℕ := 19
def childrenH_694 : Fin 7 → ℕ := ![height_116, height_188, height_397, height_435, height_691, height_694_i0, height_694_i1]
theorem height_exact_694 : height_694 = 1 + Finset.univ.sup childrenH_694 := by decide +kernel
theorem required_origin_694 : ∀ x ∈ required_694,
    (∃ j, x ∈ childrenC_694 j) ∨ ∀ j, x ∈ childrenD_694 j := by decide +kernel
theorem required_exact_694 : required_694 =
    ((Finset.univ.biUnion childrenC_694) ∪ commonEnvelope childrenD_694).erase (5, 7) := by
  exact required_eq_combination childrenC_694 childrenD_694 (5, 7) required_694
    (by decide +kernel) child_required_sub_694 common_sub_694 required_origin_694
theorem envelope_origin_694 : ∀ x ∈ envelope_694,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_694 j := by decide +kernel
theorem envelope_exact_694 : envelope_694 =
    insert (5, 7) (Finset.univ.biUnion childrenD_694) := by
  exact envelope_eq_combination childrenD_694 (5, 7) envelope_694
    pivot_mem_694 child_envelope_sub_694 envelope_origin_694
def checked_694 : CheckedCard where
  required := required_694
  envelope := envelope_694
  height := height_694
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_694
end SnakyPrototype.Certificate21

end OAI
