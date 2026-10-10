import OAI.GameTheory.SnakyConditional.Templates.Level17Part06
import OAI.GameTheory.SnakyConditional.Templates.Level23Part04
import OAI.GameTheory.SnakyConditional.Templates.Level23Part07

namespace OAI

namespace SnakyConditional
def required_584 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_584_4 : List Cell := ([(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_4_chain : (named_envelope_584_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_4_head : (named_envelope_584_4.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_4_last : (named_envelope_584_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-898 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_5 : List Cell := ([(-7, -1), (-7, 0), (-7, 1), (-7, 3), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_5_chain : (named_envelope_584_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_5_head : (named_envelope_584_5.map Internal.SnakyRows009.namedCellKey).head? = some (-897 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_5_last : (named_envelope_584_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-769 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_3 : List Cell := Internal.SnakyRows009.named_envelope_584_4 ++ Internal.SnakyRows009.named_envelope_584_5
theorem Internal.SnakyRows009.named_envelope_584_3_chain : (named_envelope_584_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_4 Internal.SnakyRows009.named_envelope_584_5 (-898 : ℤ) (-897 : ℤ)
    Internal.SnakyRows009.named_envelope_584_4_chain Internal.SnakyRows009.named_envelope_584_5_chain Internal.SnakyRows009.named_envelope_584_4_last Internal.SnakyRows009.named_envelope_584_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_3_head : (named_envelope_584_3.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_4 Internal.SnakyRows009.named_envelope_584_5 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_584_4_head
theorem Internal.SnakyRows009.named_envelope_584_3_last : (named_envelope_584_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-769 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_4 Internal.SnakyRows009.named_envelope_584_5 (-769 : ℤ) Internal.SnakyRows009.named_envelope_584_5_last
def Internal.SnakyRows009.named_envelope_584_7 : List Cell := ([(-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_7_chain : (named_envelope_584_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_7_head : (named_envelope_584_7.map Internal.SnakyRows009.namedCellKey).head? = some (-768 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_7_last : (named_envelope_584_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-641 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_8 : List Cell := ([(-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_8_chain : (named_envelope_584_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_8_head : (named_envelope_584_8.map Internal.SnakyRows009.namedCellKey).head? = some (-640 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_8_last : (named_envelope_584_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-514 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_6 : List Cell := Internal.SnakyRows009.named_envelope_584_7 ++ Internal.SnakyRows009.named_envelope_584_8
theorem Internal.SnakyRows009.named_envelope_584_6_chain : (named_envelope_584_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_7 Internal.SnakyRows009.named_envelope_584_8 (-641 : ℤ) (-640 : ℤ)
    Internal.SnakyRows009.named_envelope_584_7_chain Internal.SnakyRows009.named_envelope_584_8_chain Internal.SnakyRows009.named_envelope_584_7_last Internal.SnakyRows009.named_envelope_584_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_6_head : (named_envelope_584_6.map Internal.SnakyRows009.namedCellKey).head? = some (-768 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_7 Internal.SnakyRows009.named_envelope_584_8 (-768 : ℤ) Internal.SnakyRows009.named_envelope_584_7_head
theorem Internal.SnakyRows009.named_envelope_584_6_last : (named_envelope_584_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-514 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_7 Internal.SnakyRows009.named_envelope_584_8 (-514 : ℤ) Internal.SnakyRows009.named_envelope_584_8_last
def Internal.SnakyRows009.named_envelope_584_2 : List Cell := Internal.SnakyRows009.named_envelope_584_3 ++ Internal.SnakyRows009.named_envelope_584_6
theorem Internal.SnakyRows009.named_envelope_584_2_chain : (named_envelope_584_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_3 Internal.SnakyRows009.named_envelope_584_6 (-769 : ℤ) (-768 : ℤ)
    Internal.SnakyRows009.named_envelope_584_3_chain Internal.SnakyRows009.named_envelope_584_6_chain Internal.SnakyRows009.named_envelope_584_3_last Internal.SnakyRows009.named_envelope_584_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_2_head : (named_envelope_584_2.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_3 Internal.SnakyRows009.named_envelope_584_6 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_584_3_head
theorem Internal.SnakyRows009.named_envelope_584_2_last : (named_envelope_584_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-514 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_3 Internal.SnakyRows009.named_envelope_584_6 (-514 : ℤ) Internal.SnakyRows009.named_envelope_584_6_last
def Internal.SnakyRows009.named_envelope_584_11 : List Cell := ([(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -6), (-3, -5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_11_chain : (named_envelope_584_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_11_head : (named_envelope_584_11.map Internal.SnakyRows009.namedCellKey).head? = some (-513 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_11_last : (named_envelope_584_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-389 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_12 : List Cell := ([(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_12_chain : (named_envelope_584_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_12_head : (named_envelope_584_12.map Internal.SnakyRows009.namedCellKey).head? = some (-388 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_12_last : (named_envelope_584_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (-380 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_10 : List Cell := Internal.SnakyRows009.named_envelope_584_11 ++ Internal.SnakyRows009.named_envelope_584_12
theorem Internal.SnakyRows009.named_envelope_584_10_chain : (named_envelope_584_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_11 Internal.SnakyRows009.named_envelope_584_12 (-389 : ℤ) (-388 : ℤ)
    Internal.SnakyRows009.named_envelope_584_11_chain Internal.SnakyRows009.named_envelope_584_12_chain Internal.SnakyRows009.named_envelope_584_11_last Internal.SnakyRows009.named_envelope_584_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_10_head : (named_envelope_584_10.map Internal.SnakyRows009.namedCellKey).head? = some (-513 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_11 Internal.SnakyRows009.named_envelope_584_12 (-513 : ℤ) Internal.SnakyRows009.named_envelope_584_11_head
theorem Internal.SnakyRows009.named_envelope_584_10_last : (named_envelope_584_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (-380 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_11 Internal.SnakyRows009.named_envelope_584_12 (-380 : ℤ) Internal.SnakyRows009.named_envelope_584_12_last
def Internal.SnakyRows009.named_envelope_584_14 : List Cell := ([(-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_14_chain : (named_envelope_584_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_14_head : (named_envelope_584_14.map Internal.SnakyRows009.namedCellKey).head? = some (-263 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_14_last : (named_envelope_584_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (-255 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_15 : List Cell := ([(-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_15_chain : (named_envelope_584_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_15_head : (named_envelope_584_15.map Internal.SnakyRows009.namedCellKey).head? = some (-254 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_15_last : (named_envelope_584_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (-128 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_13 : List Cell := Internal.SnakyRows009.named_envelope_584_14 ++ Internal.SnakyRows009.named_envelope_584_15
theorem Internal.SnakyRows009.named_envelope_584_13_chain : (named_envelope_584_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_14 Internal.SnakyRows009.named_envelope_584_15 (-255 : ℤ) (-254 : ℤ)
    Internal.SnakyRows009.named_envelope_584_14_chain Internal.SnakyRows009.named_envelope_584_15_chain Internal.SnakyRows009.named_envelope_584_14_last Internal.SnakyRows009.named_envelope_584_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_13_head : (named_envelope_584_13.map Internal.SnakyRows009.namedCellKey).head? = some (-263 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_14 Internal.SnakyRows009.named_envelope_584_15 (-263 : ℤ) Internal.SnakyRows009.named_envelope_584_14_head
theorem Internal.SnakyRows009.named_envelope_584_13_last : (named_envelope_584_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (-128 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_14 Internal.SnakyRows009.named_envelope_584_15 (-128 : ℤ) Internal.SnakyRows009.named_envelope_584_15_last
def Internal.SnakyRows009.named_envelope_584_9 : List Cell := Internal.SnakyRows009.named_envelope_584_10 ++ Internal.SnakyRows009.named_envelope_584_13
theorem Internal.SnakyRows009.named_envelope_584_9_chain : (named_envelope_584_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_10 Internal.SnakyRows009.named_envelope_584_13 (-380 : ℤ) (-263 : ℤ)
    Internal.SnakyRows009.named_envelope_584_10_chain Internal.SnakyRows009.named_envelope_584_13_chain Internal.SnakyRows009.named_envelope_584_10_last Internal.SnakyRows009.named_envelope_584_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_9_head : (named_envelope_584_9.map Internal.SnakyRows009.namedCellKey).head? = some (-513 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_10 Internal.SnakyRows009.named_envelope_584_13 (-513 : ℤ) Internal.SnakyRows009.named_envelope_584_10_head
theorem Internal.SnakyRows009.named_envelope_584_9_last : (named_envelope_584_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (-128 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_10 Internal.SnakyRows009.named_envelope_584_13 (-128 : ℤ) Internal.SnakyRows009.named_envelope_584_13_last
def Internal.SnakyRows009.named_envelope_584_1 : List Cell := Internal.SnakyRows009.named_envelope_584_2 ++ Internal.SnakyRows009.named_envelope_584_9
theorem Internal.SnakyRows009.named_envelope_584_1_chain : (named_envelope_584_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_2 Internal.SnakyRows009.named_envelope_584_9 (-514 : ℤ) (-513 : ℤ)
    Internal.SnakyRows009.named_envelope_584_2_chain Internal.SnakyRows009.named_envelope_584_9_chain Internal.SnakyRows009.named_envelope_584_2_last Internal.SnakyRows009.named_envelope_584_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_1_head : (named_envelope_584_1.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_2 Internal.SnakyRows009.named_envelope_584_9 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_584_2_head
theorem Internal.SnakyRows009.named_envelope_584_1_last : (named_envelope_584_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (-128 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_2 Internal.SnakyRows009.named_envelope_584_9 (-128 : ℤ) Internal.SnakyRows009.named_envelope_584_9_last
def Internal.SnakyRows009.named_envelope_584_19 : List Cell := ([(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_19_chain : (named_envelope_584_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_19_head : (named_envelope_584_19.map Internal.SnakyRows009.namedCellKey).head? = some (-127 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_19_last : (named_envelope_584_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (-1 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_20 : List Cell := ([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_20_chain : (named_envelope_584_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_20_head : (named_envelope_584_20.map Internal.SnakyRows009.namedCellKey).head? = some (0 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_20_last : (named_envelope_584_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (130 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_18 : List Cell := Internal.SnakyRows009.named_envelope_584_19 ++ Internal.SnakyRows009.named_envelope_584_20
theorem Internal.SnakyRows009.named_envelope_584_18_chain : (named_envelope_584_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_19 Internal.SnakyRows009.named_envelope_584_20 (-1 : ℤ) (0 : ℤ)
    Internal.SnakyRows009.named_envelope_584_19_chain Internal.SnakyRows009.named_envelope_584_20_chain Internal.SnakyRows009.named_envelope_584_19_last Internal.SnakyRows009.named_envelope_584_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_18_head : (named_envelope_584_18.map Internal.SnakyRows009.namedCellKey).head? = some (-127 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_19 Internal.SnakyRows009.named_envelope_584_20 (-127 : ℤ) Internal.SnakyRows009.named_envelope_584_19_head
theorem Internal.SnakyRows009.named_envelope_584_18_last : (named_envelope_584_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (130 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_19 Internal.SnakyRows009.named_envelope_584_20 (130 : ℤ) Internal.SnakyRows009.named_envelope_584_20_last
def Internal.SnakyRows009.named_envelope_584_22 : List Cell := ([(1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_22_chain : (named_envelope_584_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_22_head : (named_envelope_584_22.map Internal.SnakyRows009.namedCellKey).head? = some (131 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_22_last : (named_envelope_584_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (259 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_23 : List Cell := ([(2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_23_chain : (named_envelope_584_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_23_head : (named_envelope_584_23.map Internal.SnakyRows009.namedCellKey).head? = some (260 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_23_last : (named_envelope_584_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_21 : List Cell := Internal.SnakyRows009.named_envelope_584_22 ++ Internal.SnakyRows009.named_envelope_584_23
theorem Internal.SnakyRows009.named_envelope_584_21_chain : (named_envelope_584_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_22 Internal.SnakyRows009.named_envelope_584_23 (259 : ℤ) (260 : ℤ)
    Internal.SnakyRows009.named_envelope_584_22_chain Internal.SnakyRows009.named_envelope_584_23_chain Internal.SnakyRows009.named_envelope_584_22_last Internal.SnakyRows009.named_envelope_584_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_21_head : (named_envelope_584_21.map Internal.SnakyRows009.namedCellKey).head? = some (131 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_22 Internal.SnakyRows009.named_envelope_584_23 (131 : ℤ) Internal.SnakyRows009.named_envelope_584_22_head
theorem Internal.SnakyRows009.named_envelope_584_21_last : (named_envelope_584_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_22 Internal.SnakyRows009.named_envelope_584_23 (387 : ℤ) Internal.SnakyRows009.named_envelope_584_23_last
def Internal.SnakyRows009.named_envelope_584_17 : List Cell := Internal.SnakyRows009.named_envelope_584_18 ++ Internal.SnakyRows009.named_envelope_584_21
theorem Internal.SnakyRows009.named_envelope_584_17_chain : (named_envelope_584_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_18 Internal.SnakyRows009.named_envelope_584_21 (130 : ℤ) (131 : ℤ)
    Internal.SnakyRows009.named_envelope_584_18_chain Internal.SnakyRows009.named_envelope_584_21_chain Internal.SnakyRows009.named_envelope_584_18_last Internal.SnakyRows009.named_envelope_584_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_17_head : (named_envelope_584_17.map Internal.SnakyRows009.namedCellKey).head? = some (-127 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_18 Internal.SnakyRows009.named_envelope_584_21 (-127 : ℤ) Internal.SnakyRows009.named_envelope_584_18_head
theorem Internal.SnakyRows009.named_envelope_584_17_last : (named_envelope_584_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_18 Internal.SnakyRows009.named_envelope_584_21 (387 : ℤ) Internal.SnakyRows009.named_envelope_584_21_last
def Internal.SnakyRows009.named_envelope_584_26 : List Cell := ([(3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_26_chain : (named_envelope_584_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_26_head : (named_envelope_584_26.map Internal.SnakyRows009.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_26_last : (named_envelope_584_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (515 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_27 : List Cell := ([(4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_27_chain : (named_envelope_584_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_27_head : (named_envelope_584_27.map Internal.SnakyRows009.namedCellKey).head? = some (516 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_27_last : (named_envelope_584_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (644 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_25 : List Cell := Internal.SnakyRows009.named_envelope_584_26 ++ Internal.SnakyRows009.named_envelope_584_27
theorem Internal.SnakyRows009.named_envelope_584_25_chain : (named_envelope_584_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_26 Internal.SnakyRows009.named_envelope_584_27 (515 : ℤ) (516 : ℤ)
    Internal.SnakyRows009.named_envelope_584_26_chain Internal.SnakyRows009.named_envelope_584_27_chain Internal.SnakyRows009.named_envelope_584_26_last Internal.SnakyRows009.named_envelope_584_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_25_head : (named_envelope_584_25.map Internal.SnakyRows009.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_26 Internal.SnakyRows009.named_envelope_584_27 (388 : ℤ) Internal.SnakyRows009.named_envelope_584_26_head
theorem Internal.SnakyRows009.named_envelope_584_25_last : (named_envelope_584_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (644 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_26 Internal.SnakyRows009.named_envelope_584_27 (644 : ℤ) Internal.SnakyRows009.named_envelope_584_27_last
def Internal.SnakyRows009.named_envelope_584_29 : List Cell := ([(6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_29_chain : (named_envelope_584_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_29_head : (named_envelope_584_29.map Internal.SnakyRows009.namedCellKey).head? = some (766 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_29_last : (named_envelope_584_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (895 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_30 : List Cell := ([(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (9, -2), (9, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_584_30_chain : (named_envelope_584_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_584_30_head : (named_envelope_584_30.map Internal.SnakyRows009.namedCellKey).head? = some (896 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_584_30_last : (named_envelope_584_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (1152 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_584_28 : List Cell := Internal.SnakyRows009.named_envelope_584_29 ++ Internal.SnakyRows009.named_envelope_584_30
theorem Internal.SnakyRows009.named_envelope_584_28_chain : (named_envelope_584_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_29 Internal.SnakyRows009.named_envelope_584_30 (895 : ℤ) (896 : ℤ)
    Internal.SnakyRows009.named_envelope_584_29_chain Internal.SnakyRows009.named_envelope_584_30_chain Internal.SnakyRows009.named_envelope_584_29_last Internal.SnakyRows009.named_envelope_584_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_28_head : (named_envelope_584_28.map Internal.SnakyRows009.namedCellKey).head? = some (766 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_29 Internal.SnakyRows009.named_envelope_584_30 (766 : ℤ) Internal.SnakyRows009.named_envelope_584_29_head
theorem Internal.SnakyRows009.named_envelope_584_28_last : (named_envelope_584_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (1152 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_29 Internal.SnakyRows009.named_envelope_584_30 (1152 : ℤ) Internal.SnakyRows009.named_envelope_584_30_last
def Internal.SnakyRows009.named_envelope_584_24 : List Cell := Internal.SnakyRows009.named_envelope_584_25 ++ Internal.SnakyRows009.named_envelope_584_28
theorem Internal.SnakyRows009.named_envelope_584_24_chain : (named_envelope_584_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_25 Internal.SnakyRows009.named_envelope_584_28 (644 : ℤ) (766 : ℤ)
    Internal.SnakyRows009.named_envelope_584_25_chain Internal.SnakyRows009.named_envelope_584_28_chain Internal.SnakyRows009.named_envelope_584_25_last Internal.SnakyRows009.named_envelope_584_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_24_head : (named_envelope_584_24.map Internal.SnakyRows009.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_25 Internal.SnakyRows009.named_envelope_584_28 (388 : ℤ) Internal.SnakyRows009.named_envelope_584_25_head
theorem Internal.SnakyRows009.named_envelope_584_24_last : (named_envelope_584_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (1152 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_25 Internal.SnakyRows009.named_envelope_584_28 (1152 : ℤ) Internal.SnakyRows009.named_envelope_584_28_last
def Internal.SnakyRows009.named_envelope_584_16 : List Cell := Internal.SnakyRows009.named_envelope_584_17 ++ Internal.SnakyRows009.named_envelope_584_24
theorem Internal.SnakyRows009.named_envelope_584_16_chain : (named_envelope_584_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_17 Internal.SnakyRows009.named_envelope_584_24 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows009.named_envelope_584_17_chain Internal.SnakyRows009.named_envelope_584_24_chain Internal.SnakyRows009.named_envelope_584_17_last Internal.SnakyRows009.named_envelope_584_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_16_head : (named_envelope_584_16.map Internal.SnakyRows009.namedCellKey).head? = some (-127 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_17 Internal.SnakyRows009.named_envelope_584_24 (-127 : ℤ) Internal.SnakyRows009.named_envelope_584_17_head
theorem Internal.SnakyRows009.named_envelope_584_16_last : (named_envelope_584_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (1152 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_17 Internal.SnakyRows009.named_envelope_584_24 (1152 : ℤ) Internal.SnakyRows009.named_envelope_584_24_last
def Internal.SnakyRows009.named_envelope_584_0 : List Cell := Internal.SnakyRows009.named_envelope_584_1 ++ Internal.SnakyRows009.named_envelope_584_16
theorem Internal.SnakyRows009.named_envelope_584_0_chain : (named_envelope_584_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_584_1 Internal.SnakyRows009.named_envelope_584_16 (-128 : ℤ) (-127 : ℤ)
    Internal.SnakyRows009.named_envelope_584_1_chain Internal.SnakyRows009.named_envelope_584_16_chain Internal.SnakyRows009.named_envelope_584_1_last Internal.SnakyRows009.named_envelope_584_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_584_0_head : (named_envelope_584_0.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_584_1 Internal.SnakyRows009.named_envelope_584_16 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_584_1_head
theorem Internal.SnakyRows009.named_envelope_584_0_last : (named_envelope_584_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1152 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_584_1 Internal.SnakyRows009.named_envelope_584_16 (1152 : ℤ) Internal.SnakyRows009.named_envelope_584_16_last
theorem Internal.SnakyRows009.named_envelope_584_nodup : (Internal.SnakyRows009.named_envelope_584_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_584_0 Internal.SnakyRows009.named_envelope_584_0_chain
def envelope_584 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_584_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_584_nodup⟩
def childrenC_584 : Fin 6 → Finset Cell := ![(placedSet 1 (0, 1) required_263), (placedSet 4 (-1, 1) required_236), (placedSet 3 (-1, 0) required_548), (placedSet 3 (0, 1) required_295), (placedSet 0 (0, 1) required_577), (placedSet 1 (0, 1) required_173)]
def childrenD_584 : Fin 6 → Finset Cell := ![(placedSet 1 (0, 1) envelope_263), (placedSet 4 (-1, 1) envelope_236), (placedSet 3 (-1, 0) envelope_548), (placedSet 3 (0, 1) envelope_295), (placedSet 0 (0, 1) envelope_577), (placedSet 1 (0, 1) envelope_173)]
theorem common_sub_584 : commonEnvelope childrenD_584 ⊆ insert (0, 0) required_584 := by decide
theorem child_required_sub_584 : ∀ j, childrenC_584 j ⊆ insert (0, 0) required_584 := by decide
theorem Internal.SnakyRows009.containment_584_0 :
    placedSet 1 (0, 1) envelope_263 ⊆ envelope_584 := by decide
theorem Internal.SnakyRows009.containment_584_1 :
    placedSet 4 (-1, 1) envelope_236 ⊆ envelope_584 := by decide
theorem Internal.SnakyRows009.containment_584_2 :
    placedSet 3 (-1, 0) envelope_548 ⊆ envelope_584 := by decide
theorem Internal.SnakyRows009.containment_584_3 :
    placedSet 3 (0, 1) envelope_295 ⊆ envelope_584 := by decide
theorem Internal.SnakyRows009.containment_584_4 :
    placedSet 0 (0, 1) envelope_577 ⊆ envelope_584 := by decide +kernel
theorem Internal.SnakyRows009.containment_584_5 :
    placedSet 1 (0, 1) envelope_173 ⊆ envelope_584 := by decide
theorem child_envelope_sub_584 : ∀ j, childrenD_584 j ⊆ envelope_584 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_584_0
  · exact Internal.SnakyRows009.containment_584_1
  · exact Internal.SnakyRows009.containment_584_2
  · exact Internal.SnakyRows009.containment_584_3
  · exact Internal.SnakyRows009.containment_584_4
  · exact Internal.SnakyRows009.containment_584_5
theorem pivot_mem_584 : (0, 0) ∈ envelope_584 := by decide
theorem children_work_584 : ∀ j, Template HasSnaky 21 (childrenC_584 j) (childrenD_584 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_263 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_236 4 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_548 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_295 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_577 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_173 1 (0, 1)).mono (by decide)
theorem row_works_584 : Template HasSnaky 22 required_584 envelope_584 := by
  refine compose HasSnaky 21 childrenC_584 childrenD_584 children_work_584 (0, 0)
    required_584 envelope_584 pivot_mem_584 child_required_sub_584 child_envelope_sub_584 ?_
  intro b hb; exact common_sub_584 (mem_commonEnvelope childrenD_584 b hb)
def required_585 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_585_4 : List Cell := ([(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_4_chain : (named_envelope_585_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_4_head : (named_envelope_585_4.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_4_last : (named_envelope_585_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-898 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_5 : List Cell := ([(-7, -1), (-7, 0), (-7, 1), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_5_chain : (named_envelope_585_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_5_head : (named_envelope_585_5.map Internal.SnakyRows009.namedCellKey).head? = some (-897 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_5_last : (named_envelope_585_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-767 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_3 : List Cell := Internal.SnakyRows009.named_envelope_585_4 ++ Internal.SnakyRows009.named_envelope_585_5
theorem Internal.SnakyRows009.named_envelope_585_3_chain : (named_envelope_585_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_4 Internal.SnakyRows009.named_envelope_585_5 (-898 : ℤ) (-897 : ℤ)
    Internal.SnakyRows009.named_envelope_585_4_chain Internal.SnakyRows009.named_envelope_585_5_chain Internal.SnakyRows009.named_envelope_585_4_last Internal.SnakyRows009.named_envelope_585_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_3_head : (named_envelope_585_3.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_4 Internal.SnakyRows009.named_envelope_585_5 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_585_4_head
theorem Internal.SnakyRows009.named_envelope_585_3_last : (named_envelope_585_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-767 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_4 Internal.SnakyRows009.named_envelope_585_5 (-767 : ℤ) Internal.SnakyRows009.named_envelope_585_5_last
def Internal.SnakyRows009.named_envelope_585_7 : List Cell := ([(-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -7), (-4, -6), (-4, -5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_7_chain : (named_envelope_585_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_7_head : (named_envelope_585_7.map Internal.SnakyRows009.namedCellKey).head? = some (-645 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_7_last : (named_envelope_585_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-517 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_8 : List Cell := ([(-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -7), (-3, -6), (-3, -5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_8_chain : (named_envelope_585_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_8_head : (named_envelope_585_8.map Internal.SnakyRows009.namedCellKey).head? = some (-516 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_8_last : (named_envelope_585_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-389 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_6 : List Cell := Internal.SnakyRows009.named_envelope_585_7 ++ Internal.SnakyRows009.named_envelope_585_8
theorem Internal.SnakyRows009.named_envelope_585_6_chain : (named_envelope_585_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_7 Internal.SnakyRows009.named_envelope_585_8 (-517 : ℤ) (-516 : ℤ)
    Internal.SnakyRows009.named_envelope_585_7_chain Internal.SnakyRows009.named_envelope_585_8_chain Internal.SnakyRows009.named_envelope_585_7_last Internal.SnakyRows009.named_envelope_585_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_6_head : (named_envelope_585_6.map Internal.SnakyRows009.namedCellKey).head? = some (-645 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_7 Internal.SnakyRows009.named_envelope_585_8 (-645 : ℤ) Internal.SnakyRows009.named_envelope_585_7_head
theorem Internal.SnakyRows009.named_envelope_585_6_last : (named_envelope_585_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-389 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_7 Internal.SnakyRows009.named_envelope_585_8 (-389 : ℤ) Internal.SnakyRows009.named_envelope_585_8_last
def Internal.SnakyRows009.named_envelope_585_2 : List Cell := Internal.SnakyRows009.named_envelope_585_3 ++ Internal.SnakyRows009.named_envelope_585_6
theorem Internal.SnakyRows009.named_envelope_585_2_chain : (named_envelope_585_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_3 Internal.SnakyRows009.named_envelope_585_6 (-767 : ℤ) (-645 : ℤ)
    Internal.SnakyRows009.named_envelope_585_3_chain Internal.SnakyRows009.named_envelope_585_6_chain Internal.SnakyRows009.named_envelope_585_3_last Internal.SnakyRows009.named_envelope_585_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_2_head : (named_envelope_585_2.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_3 Internal.SnakyRows009.named_envelope_585_6 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_585_3_head
theorem Internal.SnakyRows009.named_envelope_585_2_last : (named_envelope_585_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-389 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_3 Internal.SnakyRows009.named_envelope_585_6 (-389 : ℤ) Internal.SnakyRows009.named_envelope_585_6_last
def Internal.SnakyRows009.named_envelope_585_11 : List Cell := ([(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -7), (-2, -6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_11_chain : (named_envelope_585_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_11_head : (named_envelope_585_11.map Internal.SnakyRows009.namedCellKey).head? = some (-388 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_11_last : (named_envelope_585_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-262 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_12 : List Cell := ([(-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -7), (-1, -6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_12_chain : (named_envelope_585_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_12_head : (named_envelope_585_12.map Internal.SnakyRows009.namedCellKey).head? = some (-261 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_12_last : (named_envelope_585_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (-134 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_10 : List Cell := Internal.SnakyRows009.named_envelope_585_11 ++ Internal.SnakyRows009.named_envelope_585_12
theorem Internal.SnakyRows009.named_envelope_585_10_chain : (named_envelope_585_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_11 Internal.SnakyRows009.named_envelope_585_12 (-262 : ℤ) (-261 : ℤ)
    Internal.SnakyRows009.named_envelope_585_11_chain Internal.SnakyRows009.named_envelope_585_12_chain Internal.SnakyRows009.named_envelope_585_11_last Internal.SnakyRows009.named_envelope_585_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_10_head : (named_envelope_585_10.map Internal.SnakyRows009.namedCellKey).head? = some (-388 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_11 Internal.SnakyRows009.named_envelope_585_12 (-388 : ℤ) Internal.SnakyRows009.named_envelope_585_11_head
theorem Internal.SnakyRows009.named_envelope_585_10_last : (named_envelope_585_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (-134 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_11 Internal.SnakyRows009.named_envelope_585_12 (-134 : ℤ) Internal.SnakyRows009.named_envelope_585_12_last
def Internal.SnakyRows009.named_envelope_585_14 : List Cell := ([(-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_14_chain : (named_envelope_585_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_14_head : (named_envelope_585_14.map Internal.SnakyRows009.namedCellKey).head? = some (-133 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_14_last : (named_envelope_585_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (0 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_15 : List Cell := ([(0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_15_chain : (named_envelope_585_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_15_head : (named_envelope_585_15.map Internal.SnakyRows009.namedCellKey).head? = some (1 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_15_last : (named_envelope_585_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (130 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_13 : List Cell := Internal.SnakyRows009.named_envelope_585_14 ++ Internal.SnakyRows009.named_envelope_585_15
theorem Internal.SnakyRows009.named_envelope_585_13_chain : (named_envelope_585_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_14 Internal.SnakyRows009.named_envelope_585_15 (0 : ℤ) (1 : ℤ)
    Internal.SnakyRows009.named_envelope_585_14_chain Internal.SnakyRows009.named_envelope_585_15_chain Internal.SnakyRows009.named_envelope_585_14_last Internal.SnakyRows009.named_envelope_585_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_13_head : (named_envelope_585_13.map Internal.SnakyRows009.namedCellKey).head? = some (-133 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_14 Internal.SnakyRows009.named_envelope_585_15 (-133 : ℤ) Internal.SnakyRows009.named_envelope_585_14_head
theorem Internal.SnakyRows009.named_envelope_585_13_last : (named_envelope_585_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (130 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_14 Internal.SnakyRows009.named_envelope_585_15 (130 : ℤ) Internal.SnakyRows009.named_envelope_585_15_last
def Internal.SnakyRows009.named_envelope_585_9 : List Cell := Internal.SnakyRows009.named_envelope_585_10 ++ Internal.SnakyRows009.named_envelope_585_13
theorem Internal.SnakyRows009.named_envelope_585_9_chain : (named_envelope_585_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_10 Internal.SnakyRows009.named_envelope_585_13 (-134 : ℤ) (-133 : ℤ)
    Internal.SnakyRows009.named_envelope_585_10_chain Internal.SnakyRows009.named_envelope_585_13_chain Internal.SnakyRows009.named_envelope_585_10_last Internal.SnakyRows009.named_envelope_585_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_9_head : (named_envelope_585_9.map Internal.SnakyRows009.namedCellKey).head? = some (-388 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_10 Internal.SnakyRows009.named_envelope_585_13 (-388 : ℤ) Internal.SnakyRows009.named_envelope_585_10_head
theorem Internal.SnakyRows009.named_envelope_585_9_last : (named_envelope_585_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (130 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_10 Internal.SnakyRows009.named_envelope_585_13 (130 : ℤ) Internal.SnakyRows009.named_envelope_585_13_last
def Internal.SnakyRows009.named_envelope_585_1 : List Cell := Internal.SnakyRows009.named_envelope_585_2 ++ Internal.SnakyRows009.named_envelope_585_9
theorem Internal.SnakyRows009.named_envelope_585_1_chain : (named_envelope_585_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_2 Internal.SnakyRows009.named_envelope_585_9 (-389 : ℤ) (-388 : ℤ)
    Internal.SnakyRows009.named_envelope_585_2_chain Internal.SnakyRows009.named_envelope_585_9_chain Internal.SnakyRows009.named_envelope_585_2_last Internal.SnakyRows009.named_envelope_585_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_1_head : (named_envelope_585_1.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_2 Internal.SnakyRows009.named_envelope_585_9 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_585_2_head
theorem Internal.SnakyRows009.named_envelope_585_1_last : (named_envelope_585_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (130 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_2 Internal.SnakyRows009.named_envelope_585_9 (130 : ℤ) Internal.SnakyRows009.named_envelope_585_9_last
def Internal.SnakyRows009.named_envelope_585_19 : List Cell := ([(1, 3), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_19_chain : (named_envelope_585_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_19_head : (named_envelope_585_19.map Internal.SnakyRows009.namedCellKey).head? = some (131 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_19_last : (named_envelope_585_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (256 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_20 : List Cell := ([(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_20_chain : (named_envelope_585_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_20_head : (named_envelope_585_20.map Internal.SnakyRows009.namedCellKey).head? = some (257 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_20_last : (named_envelope_585_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (381 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_18 : List Cell := Internal.SnakyRows009.named_envelope_585_19 ++ Internal.SnakyRows009.named_envelope_585_20
theorem Internal.SnakyRows009.named_envelope_585_18_chain : (named_envelope_585_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_19 Internal.SnakyRows009.named_envelope_585_20 (256 : ℤ) (257 : ℤ)
    Internal.SnakyRows009.named_envelope_585_19_chain Internal.SnakyRows009.named_envelope_585_20_chain Internal.SnakyRows009.named_envelope_585_19_last Internal.SnakyRows009.named_envelope_585_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_18_head : (named_envelope_585_18.map Internal.SnakyRows009.namedCellKey).head? = some (131 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_19 Internal.SnakyRows009.named_envelope_585_20 (131 : ℤ) Internal.SnakyRows009.named_envelope_585_19_head
theorem Internal.SnakyRows009.named_envelope_585_18_last : (named_envelope_585_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (381 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_19 Internal.SnakyRows009.named_envelope_585_20 (381 : ℤ) Internal.SnakyRows009.named_envelope_585_20_last
def Internal.SnakyRows009.named_envelope_585_22 : List Cell := ([(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -7), (4, -6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_22_chain : (named_envelope_585_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_22_head : (named_envelope_585_22.map Internal.SnakyRows009.namedCellKey).head? = some (382 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_22_last : (named_envelope_585_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (506 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_23 : List Cell := ([(4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_23_chain : (named_envelope_585_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_23_head : (named_envelope_585_23.map Internal.SnakyRows009.namedCellKey).head? = some (507 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_23_last : (named_envelope_585_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (516 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_21 : List Cell := Internal.SnakyRows009.named_envelope_585_22 ++ Internal.SnakyRows009.named_envelope_585_23
theorem Internal.SnakyRows009.named_envelope_585_21_chain : (named_envelope_585_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_22 Internal.SnakyRows009.named_envelope_585_23 (506 : ℤ) (507 : ℤ)
    Internal.SnakyRows009.named_envelope_585_22_chain Internal.SnakyRows009.named_envelope_585_23_chain Internal.SnakyRows009.named_envelope_585_22_last Internal.SnakyRows009.named_envelope_585_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_21_head : (named_envelope_585_21.map Internal.SnakyRows009.namedCellKey).head? = some (382 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_22 Internal.SnakyRows009.named_envelope_585_23 (382 : ℤ) Internal.SnakyRows009.named_envelope_585_22_head
theorem Internal.SnakyRows009.named_envelope_585_21_last : (named_envelope_585_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (516 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_22 Internal.SnakyRows009.named_envelope_585_23 (516 : ℤ) Internal.SnakyRows009.named_envelope_585_23_last
def Internal.SnakyRows009.named_envelope_585_17 : List Cell := Internal.SnakyRows009.named_envelope_585_18 ++ Internal.SnakyRows009.named_envelope_585_21
theorem Internal.SnakyRows009.named_envelope_585_17_chain : (named_envelope_585_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_18 Internal.SnakyRows009.named_envelope_585_21 (381 : ℤ) (382 : ℤ)
    Internal.SnakyRows009.named_envelope_585_18_chain Internal.SnakyRows009.named_envelope_585_21_chain Internal.SnakyRows009.named_envelope_585_18_last Internal.SnakyRows009.named_envelope_585_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_17_head : (named_envelope_585_17.map Internal.SnakyRows009.namedCellKey).head? = some (131 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_18 Internal.SnakyRows009.named_envelope_585_21 (131 : ℤ) Internal.SnakyRows009.named_envelope_585_18_head
theorem Internal.SnakyRows009.named_envelope_585_17_last : (named_envelope_585_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (516 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_18 Internal.SnakyRows009.named_envelope_585_21 (516 : ℤ) Internal.SnakyRows009.named_envelope_585_21_last
def Internal.SnakyRows009.named_envelope_585_26 : List Cell := ([(4, 5), (4, 6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_26_chain : (named_envelope_585_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_26_head : (named_envelope_585_26.map Internal.SnakyRows009.namedCellKey).head? = some (517 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_26_last : (named_envelope_585_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (642 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_27 : List Cell := ([(5, 3), (5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_27_chain : (named_envelope_585_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_27_head : (named_envelope_585_27.map Internal.SnakyRows009.namedCellKey).head? = some (643 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_27_last : (named_envelope_585_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (770 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_25 : List Cell := Internal.SnakyRows009.named_envelope_585_26 ++ Internal.SnakyRows009.named_envelope_585_27
theorem Internal.SnakyRows009.named_envelope_585_25_chain : (named_envelope_585_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_26 Internal.SnakyRows009.named_envelope_585_27 (642 : ℤ) (643 : ℤ)
    Internal.SnakyRows009.named_envelope_585_26_chain Internal.SnakyRows009.named_envelope_585_27_chain Internal.SnakyRows009.named_envelope_585_26_last Internal.SnakyRows009.named_envelope_585_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_25_head : (named_envelope_585_25.map Internal.SnakyRows009.namedCellKey).head? = some (517 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_26 Internal.SnakyRows009.named_envelope_585_27 (517 : ℤ) Internal.SnakyRows009.named_envelope_585_26_head
theorem Internal.SnakyRows009.named_envelope_585_25_last : (named_envelope_585_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (770 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_26 Internal.SnakyRows009.named_envelope_585_27 (770 : ℤ) Internal.SnakyRows009.named_envelope_585_27_last
def Internal.SnakyRows009.named_envelope_585_29 : List Cell := ([(6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_29_chain : (named_envelope_585_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_29_head : (named_envelope_585_29.map Internal.SnakyRows009.namedCellKey).head? = some (771 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_29_last : (named_envelope_585_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (898 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_30 : List Cell := ([(7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (9, -2), (9, -1), (9, 0), (9, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_585_30_chain : (named_envelope_585_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_585_30_head : (named_envelope_585_30.map Internal.SnakyRows009.namedCellKey).head? = some (899 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_585_30_last : (named_envelope_585_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (1153 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_585_28 : List Cell := Internal.SnakyRows009.named_envelope_585_29 ++ Internal.SnakyRows009.named_envelope_585_30
theorem Internal.SnakyRows009.named_envelope_585_28_chain : (named_envelope_585_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_29 Internal.SnakyRows009.named_envelope_585_30 (898 : ℤ) (899 : ℤ)
    Internal.SnakyRows009.named_envelope_585_29_chain Internal.SnakyRows009.named_envelope_585_30_chain Internal.SnakyRows009.named_envelope_585_29_last Internal.SnakyRows009.named_envelope_585_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_28_head : (named_envelope_585_28.map Internal.SnakyRows009.namedCellKey).head? = some (771 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_29 Internal.SnakyRows009.named_envelope_585_30 (771 : ℤ) Internal.SnakyRows009.named_envelope_585_29_head
theorem Internal.SnakyRows009.named_envelope_585_28_last : (named_envelope_585_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_29 Internal.SnakyRows009.named_envelope_585_30 (1153 : ℤ) Internal.SnakyRows009.named_envelope_585_30_last
def Internal.SnakyRows009.named_envelope_585_24 : List Cell := Internal.SnakyRows009.named_envelope_585_25 ++ Internal.SnakyRows009.named_envelope_585_28
theorem Internal.SnakyRows009.named_envelope_585_24_chain : (named_envelope_585_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_25 Internal.SnakyRows009.named_envelope_585_28 (770 : ℤ) (771 : ℤ)
    Internal.SnakyRows009.named_envelope_585_25_chain Internal.SnakyRows009.named_envelope_585_28_chain Internal.SnakyRows009.named_envelope_585_25_last Internal.SnakyRows009.named_envelope_585_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_24_head : (named_envelope_585_24.map Internal.SnakyRows009.namedCellKey).head? = some (517 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_25 Internal.SnakyRows009.named_envelope_585_28 (517 : ℤ) Internal.SnakyRows009.named_envelope_585_25_head
theorem Internal.SnakyRows009.named_envelope_585_24_last : (named_envelope_585_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_25 Internal.SnakyRows009.named_envelope_585_28 (1153 : ℤ) Internal.SnakyRows009.named_envelope_585_28_last
def Internal.SnakyRows009.named_envelope_585_16 : List Cell := Internal.SnakyRows009.named_envelope_585_17 ++ Internal.SnakyRows009.named_envelope_585_24
theorem Internal.SnakyRows009.named_envelope_585_16_chain : (named_envelope_585_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_17 Internal.SnakyRows009.named_envelope_585_24 (516 : ℤ) (517 : ℤ)
    Internal.SnakyRows009.named_envelope_585_17_chain Internal.SnakyRows009.named_envelope_585_24_chain Internal.SnakyRows009.named_envelope_585_17_last Internal.SnakyRows009.named_envelope_585_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_16_head : (named_envelope_585_16.map Internal.SnakyRows009.namedCellKey).head? = some (131 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_17 Internal.SnakyRows009.named_envelope_585_24 (131 : ℤ) Internal.SnakyRows009.named_envelope_585_17_head
theorem Internal.SnakyRows009.named_envelope_585_16_last : (named_envelope_585_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_17 Internal.SnakyRows009.named_envelope_585_24 (1153 : ℤ) Internal.SnakyRows009.named_envelope_585_24_last
def Internal.SnakyRows009.named_envelope_585_0 : List Cell := Internal.SnakyRows009.named_envelope_585_1 ++ Internal.SnakyRows009.named_envelope_585_16
theorem Internal.SnakyRows009.named_envelope_585_0_chain : (named_envelope_585_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_585_1 Internal.SnakyRows009.named_envelope_585_16 (130 : ℤ) (131 : ℤ)
    Internal.SnakyRows009.named_envelope_585_1_chain Internal.SnakyRows009.named_envelope_585_16_chain Internal.SnakyRows009.named_envelope_585_1_last Internal.SnakyRows009.named_envelope_585_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_585_0_head : (named_envelope_585_0.map Internal.SnakyRows009.namedCellKey).head? = some (-1153 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_585_1 Internal.SnakyRows009.named_envelope_585_16 (-1153 : ℤ) Internal.SnakyRows009.named_envelope_585_1_head
theorem Internal.SnakyRows009.named_envelope_585_0_last : (named_envelope_585_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_585_1 Internal.SnakyRows009.named_envelope_585_16 (1153 : ℤ) Internal.SnakyRows009.named_envelope_585_16_last
theorem Internal.SnakyRows009.named_envelope_585_nodup : (Internal.SnakyRows009.named_envelope_585_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_585_0 Internal.SnakyRows009.named_envelope_585_0_chain
def envelope_585 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_585_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_585_nodup⟩
def childrenC_585 : Fin 6 → Finset Cell := ![(placedSet 2 (1, -3) required_236), (placedSet 4 (0, 1) required_300), (placedSet 1 (0, 1) required_479), (placedSet 0 (0, 1) required_577), (placedSet 3 (0, 1) required_183), (placedSet 6 (1, -3) required_527)]
def childrenD_585 : Fin 6 → Finset Cell := ![(placedSet 2 (1, -3) envelope_236), (placedSet 4 (0, 1) envelope_300), (placedSet 1 (0, 1) envelope_479), (placedSet 0 (0, 1) envelope_577), (placedSet 3 (0, 1) envelope_183), (placedSet 6 (1, -3) envelope_527)]
theorem common_sub_585 : commonEnvelope childrenD_585 ⊆ insert (0, 0) required_585 := by decide
theorem child_required_sub_585 : ∀ j, childrenC_585 j ⊆ insert (0, 0) required_585 := by decide
theorem Internal.SnakyRows009.containment_585_0 :
    placedSet 2 (1, -3) envelope_236 ⊆ envelope_585 := by decide
theorem Internal.SnakyRows009.containment_585_1 :
    placedSet 4 (0, 1) envelope_300 ⊆ envelope_585 := by decide
theorem Internal.SnakyRows009.containment_585_2 :
    placedSet 1 (0, 1) envelope_479 ⊆ envelope_585 := by decide +kernel
theorem Internal.SnakyRows009.containment_585_3 :
    placedSet 0 (0, 1) envelope_577 ⊆ envelope_585 := by decide +kernel
theorem Internal.SnakyRows009.containment_585_4 :
    placedSet 3 (0, 1) envelope_183 ⊆ envelope_585 := by decide
theorem Internal.SnakyRows009.containment_585_5 :
    placedSet 6 (1, -3) envelope_527 ⊆ envelope_585 := by decide
theorem child_envelope_sub_585 : ∀ j, childrenD_585 j ⊆ envelope_585 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_585_0
  · exact Internal.SnakyRows009.containment_585_1
  · exact Internal.SnakyRows009.containment_585_2
  · exact Internal.SnakyRows009.containment_585_3
  · exact Internal.SnakyRows009.containment_585_4
  · exact Internal.SnakyRows009.containment_585_5
theorem pivot_mem_585 : (0, 0) ∈ envelope_585 := by decide
theorem children_work_585 : ∀ j, Template HasSnaky 21 (childrenC_585 j) (childrenD_585 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_236 2 (1, -3)).mono (by decide)
  · exact (placed_template_map row_works_300 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_479 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_577 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_183 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_527 6 (1, -3)).mono (by decide)
theorem row_works_585 : Template HasSnaky 22 required_585 envelope_585 := by
  refine compose HasSnaky 21 childrenC_585 childrenD_585 children_work_585 (0, 0)
    required_585 envelope_585 pivot_mem_585 child_required_sub_585 child_envelope_sub_585 ?_
  intro b hb; exact common_sub_585 (mem_commonEnvelope childrenD_585 b hb)
end SnakyConditional

end OAI
