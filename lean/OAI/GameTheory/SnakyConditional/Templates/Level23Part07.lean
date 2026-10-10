import OAI.GameTheory.SnakyConditional.Templates.Level16Part05
import OAI.GameTheory.SnakyConditional.Templates.Level18Part02
import OAI.GameTheory.SnakyConditional.Templates.Level22Part01

namespace OAI

namespace SnakyConditional
def required_558 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_558 : Finset Cell := ⟨(([(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_558 : Fin 4 → Finset Cell := ![(placedSet 5 (1, 0) required_180), (placedSet 4 (-3, 1) required_443), (placedSet 0 (-3, 1) required_513), (placedSet 1 (1, 0) required_442)]
def childrenD_558 : Fin 4 → Finset Cell := ![(placedSet 5 (1, 0) envelope_180), (placedSet 4 (-3, 1) envelope_443), (placedSet 0 (-3, 1) envelope_513), (placedSet 1 (1, 0) envelope_442)]
theorem common_sub_558 : commonEnvelope childrenD_558 ⊆ insert (0, 0) required_558 := by decide
theorem child_required_sub_558 : ∀ j, childrenC_558 j ⊆ insert (0, 0) required_558 := by decide
theorem Internal.SnakyRows008C.containment_558_0 :
    placedSet 5 (1, 0) envelope_180 ⊆ envelope_558 := by decide
theorem Internal.SnakyRows008C.containment_558_1 :
    placedSet 4 (-3, 1) envelope_443 ⊆ envelope_558 := by decide
theorem Internal.SnakyRows008C.containment_558_2 :
    placedSet 0 (-3, 1) envelope_513 ⊆ envelope_558 := by decide
theorem Internal.SnakyRows008C.containment_558_3 :
    placedSet 1 (1, 0) envelope_442 ⊆ envelope_558 := by decide
theorem child_envelope_sub_558 : ∀ j, childrenD_558 j ⊆ envelope_558 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows008C.containment_558_0
  · exact Internal.SnakyRows008C.containment_558_1
  · exact Internal.SnakyRows008C.containment_558_2
  · exact Internal.SnakyRows008C.containment_558_3
theorem pivot_mem_558 : (0, 0) ∈ envelope_558 := by decide
theorem children_work_558 : ∀ j, Template HasSnaky 20 (childrenC_558 j) (childrenD_558 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_180 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_443 4 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_513 0 (-3, 1)).mono (by decide)
  · exact (placed_template_map row_works_442 1 (1, 0)).mono (by decide)
theorem row_works_558 : Template HasSnaky 21 required_558 envelope_558 := by
  refine compose HasSnaky 20 childrenC_558 childrenD_558 children_work_558 (0, 0)
    required_558 envelope_558 pivot_mem_558 child_required_sub_558 child_envelope_sub_558 ?_
  intro b hb; exact common_sub_558 (mem_commonEnvelope childrenD_558 b hb)
def required_577 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_577_3 : List Cell := ([(-9, -2), (-9, 0), (-8, -2), (-8, -1), (-8, 0), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-6, -6), (-6, -5), (-6, -4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_3_chain : (named_envelope_577_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_3_head : (named_envelope_577_3.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_3_last : (named_envelope_577_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-772 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_4 : List Cell := ([(-6, -3), (-6, -2), (-6, -1), (-6, 0), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_4_chain : (named_envelope_577_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_4_head : (named_envelope_577_4.map Internal.SnakyRows009.namedCellKey).head? = some (-771 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_4_last : (named_envelope_577_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-516 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_2 : List Cell := Internal.SnakyRows009.named_envelope_577_3 ++ Internal.SnakyRows009.named_envelope_577_4
theorem Internal.SnakyRows009.named_envelope_577_2_chain : (named_envelope_577_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_577_3 Internal.SnakyRows009.named_envelope_577_4 (-772 : ℤ) (-771 : ℤ)
    Internal.SnakyRows009.named_envelope_577_3_chain Internal.SnakyRows009.named_envelope_577_4_chain Internal.SnakyRows009.named_envelope_577_3_last Internal.SnakyRows009.named_envelope_577_4_head (by decide)
theorem Internal.SnakyRows009.named_envelope_577_2_head : (named_envelope_577_2.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_577_3 Internal.SnakyRows009.named_envelope_577_4 (-1154 : ℤ) Internal.SnakyRows009.named_envelope_577_3_head
theorem Internal.SnakyRows009.named_envelope_577_2_last : (named_envelope_577_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-516 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_577_3 Internal.SnakyRows009.named_envelope_577_4 (-516 : ℤ) Internal.SnakyRows009.named_envelope_577_4_last
def Internal.SnakyRows009.named_envelope_577_6 : List Cell := ([(-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -8)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_6_chain : (named_envelope_577_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_6_head : (named_envelope_577_6.map Internal.SnakyRows009.namedCellKey).head? = some (-515 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_6_last : (named_envelope_577_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-264 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_7 : List Cell := ([(-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_7_chain : (named_envelope_577_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_7_head : (named_envelope_577_7.map Internal.SnakyRows009.namedCellKey).head? = some (-263 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_7_last : (named_envelope_577_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-2 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_5 : List Cell := Internal.SnakyRows009.named_envelope_577_6 ++ Internal.SnakyRows009.named_envelope_577_7
theorem Internal.SnakyRows009.named_envelope_577_5_chain : (named_envelope_577_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_577_6 Internal.SnakyRows009.named_envelope_577_7 (-264 : ℤ) (-263 : ℤ)
    Internal.SnakyRows009.named_envelope_577_6_chain Internal.SnakyRows009.named_envelope_577_7_chain Internal.SnakyRows009.named_envelope_577_6_last Internal.SnakyRows009.named_envelope_577_7_head (by decide)
theorem Internal.SnakyRows009.named_envelope_577_5_head : (named_envelope_577_5.map Internal.SnakyRows009.namedCellKey).head? = some (-515 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_577_6 Internal.SnakyRows009.named_envelope_577_7 (-515 : ℤ) Internal.SnakyRows009.named_envelope_577_6_head
theorem Internal.SnakyRows009.named_envelope_577_5_last : (named_envelope_577_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-2 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_577_6 Internal.SnakyRows009.named_envelope_577_7 (-2 : ℤ) Internal.SnakyRows009.named_envelope_577_7_last
def Internal.SnakyRows009.named_envelope_577_1 : List Cell := Internal.SnakyRows009.named_envelope_577_2 ++ Internal.SnakyRows009.named_envelope_577_5
theorem Internal.SnakyRows009.named_envelope_577_1_chain : (named_envelope_577_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_577_2 Internal.SnakyRows009.named_envelope_577_5 (-516 : ℤ) (-515 : ℤ)
    Internal.SnakyRows009.named_envelope_577_2_chain Internal.SnakyRows009.named_envelope_577_5_chain Internal.SnakyRows009.named_envelope_577_2_last Internal.SnakyRows009.named_envelope_577_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_577_1_head : (named_envelope_577_1.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_577_2 Internal.SnakyRows009.named_envelope_577_5 (-1154 : ℤ) Internal.SnakyRows009.named_envelope_577_2_head
theorem Internal.SnakyRows009.named_envelope_577_1_last : (named_envelope_577_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (-2 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_577_2 Internal.SnakyRows009.named_envelope_577_5 (-2 : ℤ) Internal.SnakyRows009.named_envelope_577_5_last
def Internal.SnakyRows009.named_envelope_577_10 : List Cell := ([(0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_10_chain : (named_envelope_577_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_10_head : (named_envelope_577_10.map Internal.SnakyRows009.namedCellKey).head? = some (-1 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_10_last : (named_envelope_577_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (259 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_11 : List Cell := ([(2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_11_chain : (named_envelope_577_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_11_head : (named_envelope_577_11.map Internal.SnakyRows009.namedCellKey).head? = some (260 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_11_last : (named_envelope_577_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (512 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_9 : List Cell := Internal.SnakyRows009.named_envelope_577_10 ++ Internal.SnakyRows009.named_envelope_577_11
theorem Internal.SnakyRows009.named_envelope_577_9_chain : (named_envelope_577_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_577_10 Internal.SnakyRows009.named_envelope_577_11 (259 : ℤ) (260 : ℤ)
    Internal.SnakyRows009.named_envelope_577_10_chain Internal.SnakyRows009.named_envelope_577_11_chain Internal.SnakyRows009.named_envelope_577_10_last Internal.SnakyRows009.named_envelope_577_11_head (by decide)
theorem Internal.SnakyRows009.named_envelope_577_9_head : (named_envelope_577_9.map Internal.SnakyRows009.namedCellKey).head? = some (-1 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_577_10 Internal.SnakyRows009.named_envelope_577_11 (-1 : ℤ) Internal.SnakyRows009.named_envelope_577_10_head
theorem Internal.SnakyRows009.named_envelope_577_9_last : (named_envelope_577_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (512 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_577_10 Internal.SnakyRows009.named_envelope_577_11 (512 : ℤ) Internal.SnakyRows009.named_envelope_577_11_last
def Internal.SnakyRows009.named_envelope_577_13 : List Cell := ([(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_13_chain : (named_envelope_577_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_13_head : (named_envelope_577_13.map Internal.SnakyRows009.namedCellKey).head? = some (513 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_13_last : (named_envelope_577_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (767 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_14 : List Cell := ([(6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3), (8, -2), (8, -1), (9, -3), (9, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_577_14_chain : (named_envelope_577_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_577_14_head : (named_envelope_577_14.map Internal.SnakyRows009.namedCellKey).head? = some (768 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_577_14_last : (named_envelope_577_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (1151 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_577_12 : List Cell := Internal.SnakyRows009.named_envelope_577_13 ++ Internal.SnakyRows009.named_envelope_577_14
theorem Internal.SnakyRows009.named_envelope_577_12_chain : (named_envelope_577_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_577_13 Internal.SnakyRows009.named_envelope_577_14 (767 : ℤ) (768 : ℤ)
    Internal.SnakyRows009.named_envelope_577_13_chain Internal.SnakyRows009.named_envelope_577_14_chain Internal.SnakyRows009.named_envelope_577_13_last Internal.SnakyRows009.named_envelope_577_14_head (by decide)
theorem Internal.SnakyRows009.named_envelope_577_12_head : (named_envelope_577_12.map Internal.SnakyRows009.namedCellKey).head? = some (513 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_577_13 Internal.SnakyRows009.named_envelope_577_14 (513 : ℤ) Internal.SnakyRows009.named_envelope_577_13_head
theorem Internal.SnakyRows009.named_envelope_577_12_last : (named_envelope_577_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (1151 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_577_13 Internal.SnakyRows009.named_envelope_577_14 (1151 : ℤ) Internal.SnakyRows009.named_envelope_577_14_last
def Internal.SnakyRows009.named_envelope_577_8 : List Cell := Internal.SnakyRows009.named_envelope_577_9 ++ Internal.SnakyRows009.named_envelope_577_12
theorem Internal.SnakyRows009.named_envelope_577_8_chain : (named_envelope_577_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_577_9 Internal.SnakyRows009.named_envelope_577_12 (512 : ℤ) (513 : ℤ)
    Internal.SnakyRows009.named_envelope_577_9_chain Internal.SnakyRows009.named_envelope_577_12_chain Internal.SnakyRows009.named_envelope_577_9_last Internal.SnakyRows009.named_envelope_577_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_577_8_head : (named_envelope_577_8.map Internal.SnakyRows009.namedCellKey).head? = some (-1 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_577_9 Internal.SnakyRows009.named_envelope_577_12 (-1 : ℤ) Internal.SnakyRows009.named_envelope_577_9_head
theorem Internal.SnakyRows009.named_envelope_577_8_last : (named_envelope_577_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (1151 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_577_9 Internal.SnakyRows009.named_envelope_577_12 (1151 : ℤ) Internal.SnakyRows009.named_envelope_577_12_last
def Internal.SnakyRows009.named_envelope_577_0 : List Cell := Internal.SnakyRows009.named_envelope_577_1 ++ Internal.SnakyRows009.named_envelope_577_8
theorem Internal.SnakyRows009.named_envelope_577_0_chain : (named_envelope_577_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_577_1 Internal.SnakyRows009.named_envelope_577_8 (-2 : ℤ) (-1 : ℤ)
    Internal.SnakyRows009.named_envelope_577_1_chain Internal.SnakyRows009.named_envelope_577_8_chain Internal.SnakyRows009.named_envelope_577_1_last Internal.SnakyRows009.named_envelope_577_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_577_0_head : (named_envelope_577_0.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_577_1 Internal.SnakyRows009.named_envelope_577_8 (-1154 : ℤ) Internal.SnakyRows009.named_envelope_577_1_head
theorem Internal.SnakyRows009.named_envelope_577_0_last : (named_envelope_577_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1151 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_577_1 Internal.SnakyRows009.named_envelope_577_8 (1151 : ℤ) Internal.SnakyRows009.named_envelope_577_8_last
theorem Internal.SnakyRows009.named_envelope_577_nodup : (Internal.SnakyRows009.named_envelope_577_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_577_0 Internal.SnakyRows009.named_envelope_577_0_chain
def envelope_577 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_577_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_577_nodup⟩
def childrenC_577 : Fin 4 → Finset Cell := ![(placedSet 7 (1, 0) required_64), (placedSet 1 (-1, -3) required_64), (placedSet 1 (1, 0) required_443), (placedSet 7 (-1, -3) required_443)]
def childrenD_577 : Fin 4 → Finset Cell := ![(placedSet 7 (1, 0) envelope_64), (placedSet 1 (-1, -3) envelope_64), (placedSet 1 (1, 0) envelope_443), (placedSet 7 (-1, -3) envelope_443)]
theorem common_sub_577 : commonEnvelope childrenD_577 ⊆ insert (0, 0) required_577 := by decide
theorem child_required_sub_577 : ∀ j, childrenC_577 j ⊆ insert (0, 0) required_577 := by decide
theorem Internal.SnakyRows009.containment_577_0 :
    placedSet 7 (1, 0) envelope_64 ⊆ envelope_577 := by decide
theorem Internal.SnakyRows009.containment_577_1 :
    placedSet 1 (-1, -3) envelope_64 ⊆ envelope_577 := by decide
theorem Internal.SnakyRows009.containment_577_2 :
    placedSet 1 (1, 0) envelope_443 ⊆ envelope_577 := by decide
theorem Internal.SnakyRows009.containment_577_3 :
    placedSet 7 (-1, -3) envelope_443 ⊆ envelope_577 := by decide
theorem child_envelope_sub_577 : ∀ j, childrenD_577 j ⊆ envelope_577 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_577_0
  · exact Internal.SnakyRows009.containment_577_1
  · exact Internal.SnakyRows009.containment_577_2
  · exact Internal.SnakyRows009.containment_577_3
theorem pivot_mem_577 : (0, 0) ∈ envelope_577 := by decide
theorem children_work_577 : ∀ j, Template HasSnaky 20 (childrenC_577 j) (childrenD_577 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 7 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_64 1 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_443 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_443 7 (-1, -3)).mono (by decide)
theorem row_works_577 : Template HasSnaky 21 required_577 envelope_577 := by
  refine compose HasSnaky 20 childrenC_577 childrenD_577 children_work_577 (0, 0)
    required_577 envelope_577 pivot_mem_577 child_required_sub_577 child_envelope_sub_577 ?_
  intro b hb; exact common_sub_577 (mem_commonEnvelope childrenD_577 b hb)
end SnakyConditional

end OAI
