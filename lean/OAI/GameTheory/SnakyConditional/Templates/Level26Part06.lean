import OAI.GameTheory.SnakyConditional.Templates.Level17Part05
import OAI.GameTheory.SnakyConditional.Templates.Level20Part04
import OAI.GameTheory.SnakyConditional.Templates.Level21Part03
import OAI.GameTheory.SnakyConditional.Templates.Level25Part03

namespace OAI

namespace SnakyConditional
def required_576 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_576_4 : List Cell := ([(-9, -2), (-9, 0), (-9, 2), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_4_chain : (named_envelope_576_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_4_head : (named_envelope_576_4.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_4_last : (named_envelope_576_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-898 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_5 : List Cell := ([(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -4), (-6, -3), (-6, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_5_chain : (named_envelope_576_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_5_head : (named_envelope_576_5.map Internal.SnakyRows009.namedCellKey).head? = some (-897 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_5_last : (named_envelope_576_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-770 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_3 : List Cell := Internal.SnakyRows009.named_envelope_576_4 ++ Internal.SnakyRows009.named_envelope_576_5
theorem Internal.SnakyRows009.named_envelope_576_3_chain : (named_envelope_576_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_4 Internal.SnakyRows009.named_envelope_576_5 (-898 : ℤ) (-897 : ℤ)
    Internal.SnakyRows009.named_envelope_576_4_chain Internal.SnakyRows009.named_envelope_576_5_chain Internal.SnakyRows009.named_envelope_576_4_last Internal.SnakyRows009.named_envelope_576_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_3_head : (named_envelope_576_3.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_4 Internal.SnakyRows009.named_envelope_576_5 (-1154 : ℤ) Internal.SnakyRows009.named_envelope_576_4_head
theorem Internal.SnakyRows009.named_envelope_576_3_last : (named_envelope_576_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-770 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_4 Internal.SnakyRows009.named_envelope_576_5 (-770 : ℤ) Internal.SnakyRows009.named_envelope_576_5_last
def Internal.SnakyRows009.named_envelope_576_7 : List Cell := ([(-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -3), (-5, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_7_chain : (named_envelope_576_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_7_head : (named_envelope_576_7.map Internal.SnakyRows009.namedCellKey).head? = some (-769 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_7_last : (named_envelope_576_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-642 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_8 : List Cell := ([(-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_8_chain : (named_envelope_576_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_8_head : (named_envelope_576_8.map Internal.SnakyRows009.namedCellKey).head? = some (-641 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_8_last : (named_envelope_576_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-633 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_6 : List Cell := Internal.SnakyRows009.named_envelope_576_7 ++ Internal.SnakyRows009.named_envelope_576_8
theorem Internal.SnakyRows009.named_envelope_576_6_chain : (named_envelope_576_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_7 Internal.SnakyRows009.named_envelope_576_8 (-642 : ℤ) (-641 : ℤ)
    Internal.SnakyRows009.named_envelope_576_7_chain Internal.SnakyRows009.named_envelope_576_8_chain Internal.SnakyRows009.named_envelope_576_7_last Internal.SnakyRows009.named_envelope_576_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_6_head : (named_envelope_576_6.map Internal.SnakyRows009.namedCellKey).head? = some (-769 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_7 Internal.SnakyRows009.named_envelope_576_8 (-769 : ℤ) Internal.SnakyRows009.named_envelope_576_7_head
theorem Internal.SnakyRows009.named_envelope_576_6_last : (named_envelope_576_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-633 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_7 Internal.SnakyRows009.named_envelope_576_8 (-633 : ℤ) Internal.SnakyRows009.named_envelope_576_8_last
def Internal.SnakyRows009.named_envelope_576_2 : List Cell := Internal.SnakyRows009.named_envelope_576_3 ++ Internal.SnakyRows009.named_envelope_576_6
theorem Internal.SnakyRows009.named_envelope_576_2_chain : (named_envelope_576_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_3 Internal.SnakyRows009.named_envelope_576_6 (-770 : ℤ) (-769 : ℤ)
    Internal.SnakyRows009.named_envelope_576_3_chain Internal.SnakyRows009.named_envelope_576_6_chain Internal.SnakyRows009.named_envelope_576_3_last Internal.SnakyRows009.named_envelope_576_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_2_head : (named_envelope_576_2.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_3 Internal.SnakyRows009.named_envelope_576_6 (-1154 : ℤ) Internal.SnakyRows009.named_envelope_576_3_head
theorem Internal.SnakyRows009.named_envelope_576_2_last : (named_envelope_576_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-633 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_3 Internal.SnakyRows009.named_envelope_576_6 (-633 : ℤ) Internal.SnakyRows009.named_envelope_576_6_last
def Internal.SnakyRows009.named_envelope_576_11 : List Cell := ([(-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_11_chain : (named_envelope_576_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_11_head : (named_envelope_576_11.map Internal.SnakyRows009.namedCellKey).head? = some (-516 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_11_last : (named_envelope_576_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-508 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_12 : List Cell := ([(-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_12_chain : (named_envelope_576_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_12_head : (named_envelope_576_12.map Internal.SnakyRows009.namedCellKey).head? = some (-507 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_12_last : (named_envelope_576_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (-383 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_10 : List Cell := Internal.SnakyRows009.named_envelope_576_11 ++ Internal.SnakyRows009.named_envelope_576_12
theorem Internal.SnakyRows009.named_envelope_576_10_chain : (named_envelope_576_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_11 Internal.SnakyRows009.named_envelope_576_12 (-508 : ℤ) (-507 : ℤ)
    Internal.SnakyRows009.named_envelope_576_11_chain Internal.SnakyRows009.named_envelope_576_12_chain Internal.SnakyRows009.named_envelope_576_11_last Internal.SnakyRows009.named_envelope_576_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_10_head : (named_envelope_576_10.map Internal.SnakyRows009.namedCellKey).head? = some (-516 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_11 Internal.SnakyRows009.named_envelope_576_12 (-516 : ℤ) Internal.SnakyRows009.named_envelope_576_11_head
theorem Internal.SnakyRows009.named_envelope_576_10_last : (named_envelope_576_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (-383 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_11 Internal.SnakyRows009.named_envelope_576_12 (-383 : ℤ) Internal.SnakyRows009.named_envelope_576_12_last
def Internal.SnakyRows009.named_envelope_576_14 : List Cell := ([(-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_14_chain : (named_envelope_576_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_14_head : (named_envelope_576_14.map Internal.SnakyRows009.namedCellKey).head? = some (-382 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_14_last : (named_envelope_576_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (-258 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_15 : List Cell := ([(-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_15_chain : (named_envelope_576_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_15_head : (named_envelope_576_15.map Internal.SnakyRows009.namedCellKey).head? = some (-257 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_15_last : (named_envelope_576_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (-249 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_13 : List Cell := Internal.SnakyRows009.named_envelope_576_14 ++ Internal.SnakyRows009.named_envelope_576_15
theorem Internal.SnakyRows009.named_envelope_576_13_chain : (named_envelope_576_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_14 Internal.SnakyRows009.named_envelope_576_15 (-258 : ℤ) (-257 : ℤ)
    Internal.SnakyRows009.named_envelope_576_14_chain Internal.SnakyRows009.named_envelope_576_15_chain Internal.SnakyRows009.named_envelope_576_14_last Internal.SnakyRows009.named_envelope_576_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_13_head : (named_envelope_576_13.map Internal.SnakyRows009.namedCellKey).head? = some (-382 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_14 Internal.SnakyRows009.named_envelope_576_15 (-382 : ℤ) Internal.SnakyRows009.named_envelope_576_14_head
theorem Internal.SnakyRows009.named_envelope_576_13_last : (named_envelope_576_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (-249 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_14 Internal.SnakyRows009.named_envelope_576_15 (-249 : ℤ) Internal.SnakyRows009.named_envelope_576_15_last
def Internal.SnakyRows009.named_envelope_576_9 : List Cell := Internal.SnakyRows009.named_envelope_576_10 ++ Internal.SnakyRows009.named_envelope_576_13
theorem Internal.SnakyRows009.named_envelope_576_9_chain : (named_envelope_576_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_10 Internal.SnakyRows009.named_envelope_576_13 (-383 : ℤ) (-382 : ℤ)
    Internal.SnakyRows009.named_envelope_576_10_chain Internal.SnakyRows009.named_envelope_576_13_chain Internal.SnakyRows009.named_envelope_576_10_last Internal.SnakyRows009.named_envelope_576_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_9_head : (named_envelope_576_9.map Internal.SnakyRows009.namedCellKey).head? = some (-516 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_10 Internal.SnakyRows009.named_envelope_576_13 (-516 : ℤ) Internal.SnakyRows009.named_envelope_576_10_head
theorem Internal.SnakyRows009.named_envelope_576_9_last : (named_envelope_576_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (-249 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_10 Internal.SnakyRows009.named_envelope_576_13 (-249 : ℤ) Internal.SnakyRows009.named_envelope_576_13_last
def Internal.SnakyRows009.named_envelope_576_1 : List Cell := Internal.SnakyRows009.named_envelope_576_2 ++ Internal.SnakyRows009.named_envelope_576_9
theorem Internal.SnakyRows009.named_envelope_576_1_chain : (named_envelope_576_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_2 Internal.SnakyRows009.named_envelope_576_9 (-633 : ℤ) (-516 : ℤ)
    Internal.SnakyRows009.named_envelope_576_2_chain Internal.SnakyRows009.named_envelope_576_9_chain Internal.SnakyRows009.named_envelope_576_2_last Internal.SnakyRows009.named_envelope_576_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_1_head : (named_envelope_576_1.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_2 Internal.SnakyRows009.named_envelope_576_9 (-1154 : ℤ) Internal.SnakyRows009.named_envelope_576_2_head
theorem Internal.SnakyRows009.named_envelope_576_1_last : (named_envelope_576_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (-249 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_2 Internal.SnakyRows009.named_envelope_576_9 (-249 : ℤ) Internal.SnakyRows009.named_envelope_576_9_last
def Internal.SnakyRows009.named_envelope_576_19 : List Cell := ([(-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_19_chain : (named_envelope_576_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_19_head : (named_envelope_576_19.map Internal.SnakyRows009.namedCellKey).head? = some (-248 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_19_last : (named_envelope_576_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (-123 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_20 : List Cell := ([(-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_20_chain : (named_envelope_576_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_20_head : (named_envelope_576_20.map Internal.SnakyRows009.namedCellKey).head? = some (-122 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_20_last : (named_envelope_576_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (2 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_18 : List Cell := Internal.SnakyRows009.named_envelope_576_19 ++ Internal.SnakyRows009.named_envelope_576_20
theorem Internal.SnakyRows009.named_envelope_576_18_chain : (named_envelope_576_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_19 Internal.SnakyRows009.named_envelope_576_20 (-123 : ℤ) (-122 : ℤ)
    Internal.SnakyRows009.named_envelope_576_19_chain Internal.SnakyRows009.named_envelope_576_20_chain Internal.SnakyRows009.named_envelope_576_19_last Internal.SnakyRows009.named_envelope_576_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_18_head : (named_envelope_576_18.map Internal.SnakyRows009.namedCellKey).head? = some (-248 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_19 Internal.SnakyRows009.named_envelope_576_20 (-248 : ℤ) Internal.SnakyRows009.named_envelope_576_19_head
theorem Internal.SnakyRows009.named_envelope_576_18_last : (named_envelope_576_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (2 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_19 Internal.SnakyRows009.named_envelope_576_20 (2 : ℤ) Internal.SnakyRows009.named_envelope_576_20_last
def Internal.SnakyRows009.named_envelope_576_22 : List Cell := ([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_22_chain : (named_envelope_576_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_22_head : (named_envelope_576_22.map Internal.SnakyRows009.namedCellKey).head? = some (3 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_22_last : (named_envelope_576_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (128 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_23 : List Cell := ([(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_23_chain : (named_envelope_576_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_23_head : (named_envelope_576_23.map Internal.SnakyRows009.namedCellKey).head? = some (129 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_23_last : (named_envelope_576_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (137 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_21 : List Cell := Internal.SnakyRows009.named_envelope_576_22 ++ Internal.SnakyRows009.named_envelope_576_23
theorem Internal.SnakyRows009.named_envelope_576_21_chain : (named_envelope_576_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_22 Internal.SnakyRows009.named_envelope_576_23 (128 : ℤ) (129 : ℤ)
    Internal.SnakyRows009.named_envelope_576_22_chain Internal.SnakyRows009.named_envelope_576_23_chain Internal.SnakyRows009.named_envelope_576_22_last Internal.SnakyRows009.named_envelope_576_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_21_head : (named_envelope_576_21.map Internal.SnakyRows009.namedCellKey).head? = some (3 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_22 Internal.SnakyRows009.named_envelope_576_23 (3 : ℤ) Internal.SnakyRows009.named_envelope_576_22_head
theorem Internal.SnakyRows009.named_envelope_576_21_last : (named_envelope_576_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (137 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_22 Internal.SnakyRows009.named_envelope_576_23 (137 : ℤ) Internal.SnakyRows009.named_envelope_576_23_last
def Internal.SnakyRows009.named_envelope_576_17 : List Cell := Internal.SnakyRows009.named_envelope_576_18 ++ Internal.SnakyRows009.named_envelope_576_21
theorem Internal.SnakyRows009.named_envelope_576_17_chain : (named_envelope_576_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_18 Internal.SnakyRows009.named_envelope_576_21 (2 : ℤ) (3 : ℤ)
    Internal.SnakyRows009.named_envelope_576_18_chain Internal.SnakyRows009.named_envelope_576_21_chain Internal.SnakyRows009.named_envelope_576_18_last Internal.SnakyRows009.named_envelope_576_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_17_head : (named_envelope_576_17.map Internal.SnakyRows009.namedCellKey).head? = some (-248 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_18 Internal.SnakyRows009.named_envelope_576_21 (-248 : ℤ) Internal.SnakyRows009.named_envelope_576_18_head
theorem Internal.SnakyRows009.named_envelope_576_17_last : (named_envelope_576_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (137 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_18 Internal.SnakyRows009.named_envelope_576_21 (137 : ℤ) Internal.SnakyRows009.named_envelope_576_21_last
def Internal.SnakyRows009.named_envelope_576_26 : List Cell := ([(1, 10), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_26_chain : (named_envelope_576_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_26_head : (named_envelope_576_26.map Internal.SnakyRows009.namedCellKey).head? = some (138 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_26_last : (named_envelope_576_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (263 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_27 : List Cell := ([(2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_27_chain : (named_envelope_576_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_27_head : (named_envelope_576_27.map Internal.SnakyRows009.namedCellKey).head? = some (264 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_27_last : (named_envelope_576_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (388 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_25 : List Cell := Internal.SnakyRows009.named_envelope_576_26 ++ Internal.SnakyRows009.named_envelope_576_27
theorem Internal.SnakyRows009.named_envelope_576_25_chain : (named_envelope_576_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_26 Internal.SnakyRows009.named_envelope_576_27 (263 : ℤ) (264 : ℤ)
    Internal.SnakyRows009.named_envelope_576_26_chain Internal.SnakyRows009.named_envelope_576_27_chain Internal.SnakyRows009.named_envelope_576_26_last Internal.SnakyRows009.named_envelope_576_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_25_head : (named_envelope_576_25.map Internal.SnakyRows009.namedCellKey).head? = some (138 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_26 Internal.SnakyRows009.named_envelope_576_27 (138 : ℤ) Internal.SnakyRows009.named_envelope_576_26_head
theorem Internal.SnakyRows009.named_envelope_576_25_last : (named_envelope_576_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (388 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_26 Internal.SnakyRows009.named_envelope_576_27 (388 : ℤ) Internal.SnakyRows009.named_envelope_576_27_last
def Internal.SnakyRows009.named_envelope_576_29 : List Cell := ([(3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_29_chain : (named_envelope_576_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_29_head : (named_envelope_576_29.map Internal.SnakyRows009.namedCellKey).head? = some (389 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_29_last : (named_envelope_576_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (518 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_30 : List Cell := ([(4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_576_30_chain : (named_envelope_576_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_576_30_head : (named_envelope_576_30.map Internal.SnakyRows009.namedCellKey).head? = some (519 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_576_30_last : (named_envelope_576_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (772 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_576_28 : List Cell := Internal.SnakyRows009.named_envelope_576_29 ++ Internal.SnakyRows009.named_envelope_576_30
theorem Internal.SnakyRows009.named_envelope_576_28_chain : (named_envelope_576_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_29 Internal.SnakyRows009.named_envelope_576_30 (518 : ℤ) (519 : ℤ)
    Internal.SnakyRows009.named_envelope_576_29_chain Internal.SnakyRows009.named_envelope_576_30_chain Internal.SnakyRows009.named_envelope_576_29_last Internal.SnakyRows009.named_envelope_576_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_28_head : (named_envelope_576_28.map Internal.SnakyRows009.namedCellKey).head? = some (389 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_29 Internal.SnakyRows009.named_envelope_576_30 (389 : ℤ) Internal.SnakyRows009.named_envelope_576_29_head
theorem Internal.SnakyRows009.named_envelope_576_28_last : (named_envelope_576_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (772 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_29 Internal.SnakyRows009.named_envelope_576_30 (772 : ℤ) Internal.SnakyRows009.named_envelope_576_30_last
def Internal.SnakyRows009.named_envelope_576_24 : List Cell := Internal.SnakyRows009.named_envelope_576_25 ++ Internal.SnakyRows009.named_envelope_576_28
theorem Internal.SnakyRows009.named_envelope_576_24_chain : (named_envelope_576_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_25 Internal.SnakyRows009.named_envelope_576_28 (388 : ℤ) (389 : ℤ)
    Internal.SnakyRows009.named_envelope_576_25_chain Internal.SnakyRows009.named_envelope_576_28_chain Internal.SnakyRows009.named_envelope_576_25_last Internal.SnakyRows009.named_envelope_576_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_24_head : (named_envelope_576_24.map Internal.SnakyRows009.namedCellKey).head? = some (138 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_25 Internal.SnakyRows009.named_envelope_576_28 (138 : ℤ) Internal.SnakyRows009.named_envelope_576_25_head
theorem Internal.SnakyRows009.named_envelope_576_24_last : (named_envelope_576_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (772 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_25 Internal.SnakyRows009.named_envelope_576_28 (772 : ℤ) Internal.SnakyRows009.named_envelope_576_28_last
def Internal.SnakyRows009.named_envelope_576_16 : List Cell := Internal.SnakyRows009.named_envelope_576_17 ++ Internal.SnakyRows009.named_envelope_576_24
theorem Internal.SnakyRows009.named_envelope_576_16_chain : (named_envelope_576_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_17 Internal.SnakyRows009.named_envelope_576_24 (137 : ℤ) (138 : ℤ)
    Internal.SnakyRows009.named_envelope_576_17_chain Internal.SnakyRows009.named_envelope_576_24_chain Internal.SnakyRows009.named_envelope_576_17_last Internal.SnakyRows009.named_envelope_576_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_16_head : (named_envelope_576_16.map Internal.SnakyRows009.namedCellKey).head? = some (-248 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_17 Internal.SnakyRows009.named_envelope_576_24 (-248 : ℤ) Internal.SnakyRows009.named_envelope_576_17_head
theorem Internal.SnakyRows009.named_envelope_576_16_last : (named_envelope_576_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (772 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_17 Internal.SnakyRows009.named_envelope_576_24 (772 : ℤ) Internal.SnakyRows009.named_envelope_576_24_last
def Internal.SnakyRows009.named_envelope_576_0 : List Cell := Internal.SnakyRows009.named_envelope_576_1 ++ Internal.SnakyRows009.named_envelope_576_16
theorem Internal.SnakyRows009.named_envelope_576_0_chain : (named_envelope_576_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_576_1 Internal.SnakyRows009.named_envelope_576_16 (-249 : ℤ) (-248 : ℤ)
    Internal.SnakyRows009.named_envelope_576_1_chain Internal.SnakyRows009.named_envelope_576_16_chain Internal.SnakyRows009.named_envelope_576_1_last Internal.SnakyRows009.named_envelope_576_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_576_0_head : (named_envelope_576_0.map Internal.SnakyRows009.namedCellKey).head? = some (-1154 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_576_1 Internal.SnakyRows009.named_envelope_576_16 (-1154 : ℤ) Internal.SnakyRows009.named_envelope_576_1_head
theorem Internal.SnakyRows009.named_envelope_576_0_last : (named_envelope_576_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (772 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_576_1 Internal.SnakyRows009.named_envelope_576_16 (772 : ℤ) Internal.SnakyRows009.named_envelope_576_16_last
theorem Internal.SnakyRows009.named_envelope_576_nodup : (Internal.SnakyRows009.named_envelope_576_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_576_0 Internal.SnakyRows009.named_envelope_576_0_chain
def envelope_576 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_576_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_576_nodup⟩
def childrenC_576 : Fin 10 → Finset Cell := ![(placedSet 0 (1, 0) required_495), (placedSet 4 (1, 0) required_544), (placedSet 3 (-1, 1) required_462), (placedSet 0 (-1, 2) required_540), (placedSet 4 (1, 0) required_355), (placedSet 0 (-1, 2) required_539), (placedSet 4 (1, 0) required_497), (placedSet 1 (1, 0) required_390), (placedSet 0 (-2, 0) required_563), (placedSet 4 (1, 0) required_518)]
def childrenD_576 : Fin 10 → Finset Cell := ![(placedSet 0 (1, 0) envelope_495), (placedSet 4 (1, 0) envelope_544), (placedSet 3 (-1, 1) envelope_462), (placedSet 0 (-1, 2) envelope_540), (placedSet 4 (1, 0) envelope_355), (placedSet 0 (-1, 2) envelope_539), (placedSet 4 (1, 0) envelope_497), (placedSet 1 (1, 0) envelope_390), (placedSet 0 (-2, 0) envelope_563), (placedSet 4 (1, 0) envelope_518)]
theorem common_sub_576 : commonEnvelope childrenD_576 ⊆ insert (0, 0) required_576 := by decide
theorem child_required_sub_576 : ∀ j, childrenC_576 j ⊆ insert (0, 0) required_576 := by decide
theorem Internal.SnakyRows009.containment_576_0 :
    placedSet 0 (1, 0) envelope_495 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_1 :
    placedSet 4 (1, 0) envelope_544 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_2 :
    placedSet 3 (-1, 1) envelope_462 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_3 :
    placedSet 0 (-1, 2) envelope_540 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_4 :
    placedSet 4 (1, 0) envelope_355 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_5 :
    placedSet 0 (-1, 2) envelope_539 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_6 :
    placedSet 4 (1, 0) envelope_497 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_7 :
    placedSet 1 (1, 0) envelope_390 ⊆ envelope_576 := by decide
theorem Internal.SnakyRows009.containment_576_8 :
    placedSet 0 (-2, 0) envelope_563 ⊆ envelope_576 := by decide +kernel
theorem Internal.SnakyRows009.containment_576_9 :
    placedSet 4 (1, 0) envelope_518 ⊆ envelope_576 := by decide
theorem child_envelope_sub_576 : ∀ j, childrenD_576 j ⊆ envelope_576 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_576_0
  · exact Internal.SnakyRows009.containment_576_1
  · exact Internal.SnakyRows009.containment_576_2
  · exact Internal.SnakyRows009.containment_576_3
  · exact Internal.SnakyRows009.containment_576_4
  · exact Internal.SnakyRows009.containment_576_5
  · exact Internal.SnakyRows009.containment_576_6
  · exact Internal.SnakyRows009.containment_576_7
  · exact Internal.SnakyRows009.containment_576_8
  · exact Internal.SnakyRows009.containment_576_9
theorem pivot_mem_576 : (0, 0) ∈ envelope_576 := by decide
theorem children_work_576 : ∀ j, Template HasSnaky 23 (childrenC_576 j) (childrenD_576 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_495 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_544 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_462 3 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_540 0 (-1, 2)).mono (by decide)
  · exact (placed_template_map row_works_355 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_539 0 (-1, 2)).mono (by decide)
  · exact (placed_template_map row_works_497 4 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_390 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_563 0 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_518 4 (1, 0)).mono (by decide)
theorem row_works_576 : Template HasSnaky 24 required_576 envelope_576 := by
  refine compose HasSnaky 23 childrenC_576 childrenD_576 children_work_576 (0, 0)
    required_576 envelope_576 pivot_mem_576 child_required_sub_576 child_envelope_sub_576 ?_
  intro b hb; exact common_sub_576 (mem_commonEnvelope childrenD_576 b hb)
end SnakyConditional

end OAI
