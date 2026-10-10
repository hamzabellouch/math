import OAI.GameTheory.SnakyConditional.Templates.Level22Part02
import OAI.GameTheory.SnakyConditional.Templates.Level25Part05

namespace OAI

namespace SnakyConditional
def required_582 : Finset Cell := ⟨(([(1, -4), (1, -3), (1, -2), (2, -4)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows009.named_envelope_582_4 : List Cell := ([(-6, 1), (-6, 2), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -1), (-4, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_4_chain : (named_envelope_582_4.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_4_head : (named_envelope_582_4.map Internal.SnakyRows009.namedCellKey).head? = some (-767 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_4_last : (named_envelope_582_4.map Internal.SnakyRows009.namedCellKey).getLast? = some (-511 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_5 : List Cell := ([(-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1), (-3, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_5_chain : (named_envelope_582_5.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_5_head : (named_envelope_582_5.map Internal.SnakyRows009.namedCellKey).head? = some (-510 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_5_last : (named_envelope_582_5.map Internal.SnakyRows009.namedCellKey).getLast? = some (-384 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_3 : List Cell := Internal.SnakyRows009.named_envelope_582_4 ++ Internal.SnakyRows009.named_envelope_582_5
theorem Internal.SnakyRows009.named_envelope_582_3_chain : (named_envelope_582_3.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_4 Internal.SnakyRows009.named_envelope_582_5 (-511 : ℤ) (-510 : ℤ)
    Internal.SnakyRows009.named_envelope_582_4_chain Internal.SnakyRows009.named_envelope_582_5_chain Internal.SnakyRows009.named_envelope_582_4_last Internal.SnakyRows009.named_envelope_582_5_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_3_head : (named_envelope_582_3.map Internal.SnakyRows009.namedCellKey).head? = some (-767 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_4 Internal.SnakyRows009.named_envelope_582_5 (-767 : ℤ) Internal.SnakyRows009.named_envelope_582_4_head
theorem Internal.SnakyRows009.named_envelope_582_3_last : (named_envelope_582_3.map Internal.SnakyRows009.namedCellKey).getLast? = some (-384 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_4 Internal.SnakyRows009.named_envelope_582_5 (-384 : ℤ) Internal.SnakyRows009.named_envelope_582_5_last
def Internal.SnakyRows009.named_envelope_582_7 : List Cell := ([(-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -3), (-2, -2), (-2, -1), (-2, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_7_chain : (named_envelope_582_7.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_7_head : (named_envelope_582_7.map Internal.SnakyRows009.namedCellKey).head? = some (-383 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_7_last : (named_envelope_582_7.map Internal.SnakyRows009.namedCellKey).getLast? = some (-256 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_8 : List Cell := ([(-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_8_chain : (named_envelope_582_8.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_8_head : (named_envelope_582_8.map Internal.SnakyRows009.namedCellKey).head? = some (-255 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_8_last : (named_envelope_582_8.map Internal.SnakyRows009.namedCellKey).getLast? = some (-132 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_6 : List Cell := Internal.SnakyRows009.named_envelope_582_7 ++ Internal.SnakyRows009.named_envelope_582_8
theorem Internal.SnakyRows009.named_envelope_582_6_chain : (named_envelope_582_6.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_7 Internal.SnakyRows009.named_envelope_582_8 (-256 : ℤ) (-255 : ℤ)
    Internal.SnakyRows009.named_envelope_582_7_chain Internal.SnakyRows009.named_envelope_582_8_chain Internal.SnakyRows009.named_envelope_582_7_last Internal.SnakyRows009.named_envelope_582_8_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_6_head : (named_envelope_582_6.map Internal.SnakyRows009.namedCellKey).head? = some (-383 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_7 Internal.SnakyRows009.named_envelope_582_8 (-383 : ℤ) Internal.SnakyRows009.named_envelope_582_7_head
theorem Internal.SnakyRows009.named_envelope_582_6_last : (named_envelope_582_6.map Internal.SnakyRows009.namedCellKey).getLast? = some (-132 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_7 Internal.SnakyRows009.named_envelope_582_8 (-132 : ℤ) Internal.SnakyRows009.named_envelope_582_8_last
def Internal.SnakyRows009.named_envelope_582_2 : List Cell := Internal.SnakyRows009.named_envelope_582_3 ++ Internal.SnakyRows009.named_envelope_582_6
theorem Internal.SnakyRows009.named_envelope_582_2_chain : (named_envelope_582_2.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_3 Internal.SnakyRows009.named_envelope_582_6 (-384 : ℤ) (-383 : ℤ)
    Internal.SnakyRows009.named_envelope_582_3_chain Internal.SnakyRows009.named_envelope_582_6_chain Internal.SnakyRows009.named_envelope_582_3_last Internal.SnakyRows009.named_envelope_582_6_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_2_head : (named_envelope_582_2.map Internal.SnakyRows009.namedCellKey).head? = some (-767 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_3 Internal.SnakyRows009.named_envelope_582_6 (-767 : ℤ) Internal.SnakyRows009.named_envelope_582_3_head
theorem Internal.SnakyRows009.named_envelope_582_2_last : (named_envelope_582_2.map Internal.SnakyRows009.namedCellKey).getLast? = some (-132 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_3 Internal.SnakyRows009.named_envelope_582_6 (-132 : ℤ) Internal.SnakyRows009.named_envelope_582_6_last
def Internal.SnakyRows009.named_envelope_582_11 : List Cell := ([(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_11_chain : (named_envelope_582_11.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_11_head : (named_envelope_582_11.map Internal.SnakyRows009.namedCellKey).head? = some (-131 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_11_last : (named_envelope_582_11.map Internal.SnakyRows009.namedCellKey).getLast? = some (-122 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_12 : List Cell := ([(-1, 7), (-1, 8), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_12_chain : (named_envelope_582_12.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_12_head : (named_envelope_582_12.map Internal.SnakyRows009.namedCellKey).head? = some (-121 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_12_last : (named_envelope_582_12.map Internal.SnakyRows009.namedCellKey).getLast? = some (4 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_10 : List Cell := Internal.SnakyRows009.named_envelope_582_11 ++ Internal.SnakyRows009.named_envelope_582_12
theorem Internal.SnakyRows009.named_envelope_582_10_chain : (named_envelope_582_10.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_11 Internal.SnakyRows009.named_envelope_582_12 (-122 : ℤ) (-121 : ℤ)
    Internal.SnakyRows009.named_envelope_582_11_chain Internal.SnakyRows009.named_envelope_582_12_chain Internal.SnakyRows009.named_envelope_582_11_last Internal.SnakyRows009.named_envelope_582_12_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_10_head : (named_envelope_582_10.map Internal.SnakyRows009.namedCellKey).head? = some (-131 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_11 Internal.SnakyRows009.named_envelope_582_12 (-131 : ℤ) Internal.SnakyRows009.named_envelope_582_11_head
theorem Internal.SnakyRows009.named_envelope_582_10_last : (named_envelope_582_10.map Internal.SnakyRows009.namedCellKey).getLast? = some (4 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_11 Internal.SnakyRows009.named_envelope_582_12 (4 : ℤ) Internal.SnakyRows009.named_envelope_582_12_last
def Internal.SnakyRows009.named_envelope_582_14 : List Cell := ([(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_14_chain : (named_envelope_582_14.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_14_head : (named_envelope_582_14.map Internal.SnakyRows009.namedCellKey).head? = some (5 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_14_last : (named_envelope_582_14.map Internal.SnakyRows009.namedCellKey).getLast? = some (128 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_15 : List Cell := ([(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, 0)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_15_chain : (named_envelope_582_15.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_15_head : (named_envelope_582_15.map Internal.SnakyRows009.namedCellKey).head? = some (129 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_15_last : (named_envelope_582_15.map Internal.SnakyRows009.namedCellKey).getLast? = some (256 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_13 : List Cell := Internal.SnakyRows009.named_envelope_582_14 ++ Internal.SnakyRows009.named_envelope_582_15
theorem Internal.SnakyRows009.named_envelope_582_13_chain : (named_envelope_582_13.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_14 Internal.SnakyRows009.named_envelope_582_15 (128 : ℤ) (129 : ℤ)
    Internal.SnakyRows009.named_envelope_582_14_chain Internal.SnakyRows009.named_envelope_582_15_chain Internal.SnakyRows009.named_envelope_582_14_last Internal.SnakyRows009.named_envelope_582_15_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_13_head : (named_envelope_582_13.map Internal.SnakyRows009.namedCellKey).head? = some (5 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_14 Internal.SnakyRows009.named_envelope_582_15 (5 : ℤ) Internal.SnakyRows009.named_envelope_582_14_head
theorem Internal.SnakyRows009.named_envelope_582_13_last : (named_envelope_582_13.map Internal.SnakyRows009.namedCellKey).getLast? = some (256 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_14 Internal.SnakyRows009.named_envelope_582_15 (256 : ℤ) Internal.SnakyRows009.named_envelope_582_15_last
def Internal.SnakyRows009.named_envelope_582_9 : List Cell := Internal.SnakyRows009.named_envelope_582_10 ++ Internal.SnakyRows009.named_envelope_582_13
theorem Internal.SnakyRows009.named_envelope_582_9_chain : (named_envelope_582_9.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_10 Internal.SnakyRows009.named_envelope_582_13 (4 : ℤ) (5 : ℤ)
    Internal.SnakyRows009.named_envelope_582_10_chain Internal.SnakyRows009.named_envelope_582_13_chain Internal.SnakyRows009.named_envelope_582_10_last Internal.SnakyRows009.named_envelope_582_13_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_9_head : (named_envelope_582_9.map Internal.SnakyRows009.namedCellKey).head? = some (-131 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_10 Internal.SnakyRows009.named_envelope_582_13 (-131 : ℤ) Internal.SnakyRows009.named_envelope_582_10_head
theorem Internal.SnakyRows009.named_envelope_582_9_last : (named_envelope_582_9.map Internal.SnakyRows009.namedCellKey).getLast? = some (256 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_10 Internal.SnakyRows009.named_envelope_582_13 (256 : ℤ) Internal.SnakyRows009.named_envelope_582_13_last
def Internal.SnakyRows009.named_envelope_582_1 : List Cell := Internal.SnakyRows009.named_envelope_582_2 ++ Internal.SnakyRows009.named_envelope_582_9
theorem Internal.SnakyRows009.named_envelope_582_1_chain : (named_envelope_582_1.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_2 Internal.SnakyRows009.named_envelope_582_9 (-132 : ℤ) (-131 : ℤ)
    Internal.SnakyRows009.named_envelope_582_2_chain Internal.SnakyRows009.named_envelope_582_9_chain Internal.SnakyRows009.named_envelope_582_2_last Internal.SnakyRows009.named_envelope_582_9_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_1_head : (named_envelope_582_1.map Internal.SnakyRows009.namedCellKey).head? = some (-767 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_2 Internal.SnakyRows009.named_envelope_582_9 (-767 : ℤ) Internal.SnakyRows009.named_envelope_582_2_head
theorem Internal.SnakyRows009.named_envelope_582_1_last : (named_envelope_582_1.map Internal.SnakyRows009.namedCellKey).getLast? = some (256 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_2 Internal.SnakyRows009.named_envelope_582_9 (256 : ℤ) Internal.SnakyRows009.named_envelope_582_9_last
def Internal.SnakyRows009.named_envelope_582_19 : List Cell := ([(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -9), (3, -8), (3, -7)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_19_chain : (named_envelope_582_19.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_19_head : (named_envelope_582_19.map Internal.SnakyRows009.namedCellKey).head? = some (257 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_19_last : (named_envelope_582_19.map Internal.SnakyRows009.namedCellKey).getLast? = some (377 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_20 : List Cell := ([(3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_20_chain : (named_envelope_582_20.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_20_head : (named_envelope_582_20.map Internal.SnakyRows009.namedCellKey).head? = some (378 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_20_last : (named_envelope_582_20.map Internal.SnakyRows009.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_18 : List Cell := Internal.SnakyRows009.named_envelope_582_19 ++ Internal.SnakyRows009.named_envelope_582_20
theorem Internal.SnakyRows009.named_envelope_582_18_chain : (named_envelope_582_18.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_19 Internal.SnakyRows009.named_envelope_582_20 (377 : ℤ) (378 : ℤ)
    Internal.SnakyRows009.named_envelope_582_19_chain Internal.SnakyRows009.named_envelope_582_20_chain Internal.SnakyRows009.named_envelope_582_19_last Internal.SnakyRows009.named_envelope_582_20_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_18_head : (named_envelope_582_18.map Internal.SnakyRows009.namedCellKey).head? = some (257 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_19 Internal.SnakyRows009.named_envelope_582_20 (257 : ℤ) Internal.SnakyRows009.named_envelope_582_19_head
theorem Internal.SnakyRows009.named_envelope_582_18_last : (named_envelope_582_18.map Internal.SnakyRows009.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_19 Internal.SnakyRows009.named_envelope_582_20 (387 : ℤ) Internal.SnakyRows009.named_envelope_582_20_last
def Internal.SnakyRows009.named_envelope_582_22 : List Cell := ([(3, 4), (3, 5), (3, 6), (3, 7), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_22_chain : (named_envelope_582_22.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_22_head : (named_envelope_582_22.map Internal.SnakyRows009.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_22_last : (named_envelope_582_22.map Internal.SnakyRows009.namedCellKey).getLast? = some (509 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_23 : List Cell := ([(4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -9)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_23_chain : (named_envelope_582_23.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_23_head : (named_envelope_582_23.map Internal.SnakyRows009.namedCellKey).head? = some (510 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_23_last : (named_envelope_582_23.map Internal.SnakyRows009.namedCellKey).getLast? = some (631 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_21 : List Cell := Internal.SnakyRows009.named_envelope_582_22 ++ Internal.SnakyRows009.named_envelope_582_23
theorem Internal.SnakyRows009.named_envelope_582_21_chain : (named_envelope_582_21.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_22 Internal.SnakyRows009.named_envelope_582_23 (509 : ℤ) (510 : ℤ)
    Internal.SnakyRows009.named_envelope_582_22_chain Internal.SnakyRows009.named_envelope_582_23_chain Internal.SnakyRows009.named_envelope_582_22_last Internal.SnakyRows009.named_envelope_582_23_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_21_head : (named_envelope_582_21.map Internal.SnakyRows009.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_22 Internal.SnakyRows009.named_envelope_582_23 (388 : ℤ) Internal.SnakyRows009.named_envelope_582_22_head
theorem Internal.SnakyRows009.named_envelope_582_21_last : (named_envelope_582_21.map Internal.SnakyRows009.namedCellKey).getLast? = some (631 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_22 Internal.SnakyRows009.named_envelope_582_23 (631 : ℤ) Internal.SnakyRows009.named_envelope_582_23_last
def Internal.SnakyRows009.named_envelope_582_17 : List Cell := Internal.SnakyRows009.named_envelope_582_18 ++ Internal.SnakyRows009.named_envelope_582_21
theorem Internal.SnakyRows009.named_envelope_582_17_chain : (named_envelope_582_17.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_18 Internal.SnakyRows009.named_envelope_582_21 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows009.named_envelope_582_18_chain Internal.SnakyRows009.named_envelope_582_21_chain Internal.SnakyRows009.named_envelope_582_18_last Internal.SnakyRows009.named_envelope_582_21_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_17_head : (named_envelope_582_17.map Internal.SnakyRows009.namedCellKey).head? = some (257 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_18 Internal.SnakyRows009.named_envelope_582_21 (257 : ℤ) Internal.SnakyRows009.named_envelope_582_18_head
theorem Internal.SnakyRows009.named_envelope_582_17_last : (named_envelope_582_17.map Internal.SnakyRows009.namedCellKey).getLast? = some (631 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_18 Internal.SnakyRows009.named_envelope_582_21 (631 : ℤ) Internal.SnakyRows009.named_envelope_582_21_last
def Internal.SnakyRows009.named_envelope_582_26 : List Cell := ([(5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_26_chain : (named_envelope_582_26.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_26_head : (named_envelope_582_26.map Internal.SnakyRows009.namedCellKey).head? = some (632 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_26_last : (named_envelope_582_26.map Internal.SnakyRows009.namedCellKey).getLast? = some (641 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_27 : List Cell := ([(5, 2), (5, 3), (5, 4), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_27_chain : (named_envelope_582_27.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_27_head : (named_envelope_582_27.map Internal.SnakyRows009.namedCellKey).head? = some (642 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_27_last : (named_envelope_582_27.map Internal.SnakyRows009.namedCellKey).getLast? = some (767 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_25 : List Cell := Internal.SnakyRows009.named_envelope_582_26 ++ Internal.SnakyRows009.named_envelope_582_27
theorem Internal.SnakyRows009.named_envelope_582_25_chain : (named_envelope_582_25.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_26 Internal.SnakyRows009.named_envelope_582_27 (641 : ℤ) (642 : ℤ)
    Internal.SnakyRows009.named_envelope_582_26_chain Internal.SnakyRows009.named_envelope_582_27_chain Internal.SnakyRows009.named_envelope_582_26_last Internal.SnakyRows009.named_envelope_582_27_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_25_head : (named_envelope_582_25.map Internal.SnakyRows009.namedCellKey).head? = some (632 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_26 Internal.SnakyRows009.named_envelope_582_27 (632 : ℤ) Internal.SnakyRows009.named_envelope_582_26_head
theorem Internal.SnakyRows009.named_envelope_582_25_last : (named_envelope_582_25.map Internal.SnakyRows009.namedCellKey).getLast? = some (767 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_26 Internal.SnakyRows009.named_envelope_582_27 (767 : ℤ) Internal.SnakyRows009.named_envelope_582_27_last
def Internal.SnakyRows009.named_envelope_582_29 : List Cell := ([(6, 2), (6, 4), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (8, -7)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_29_chain : (named_envelope_582_29.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_29_head : (named_envelope_582_29.map Internal.SnakyRows009.namedCellKey).head? = some (770 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_29_last : (named_envelope_582_29.map Internal.SnakyRows009.namedCellKey).getLast? = some (1017 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_30 : List Cell := ([(8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (9, -3), (9, -2), (9, -1), (10, -3), (10, -1)] : List Cell)
theorem Internal.SnakyRows009.named_envelope_582_30_chain : (named_envelope_582_30.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows009.named_envelope_582_30_head : (named_envelope_582_30.map Internal.SnakyRows009.namedCellKey).head? = some (1018 : ℤ) := by decide
theorem Internal.SnakyRows009.named_envelope_582_30_last : (named_envelope_582_30.map Internal.SnakyRows009.namedCellKey).getLast? = some (1279 : ℤ) := by decide
def Internal.SnakyRows009.named_envelope_582_28 : List Cell := Internal.SnakyRows009.named_envelope_582_29 ++ Internal.SnakyRows009.named_envelope_582_30
theorem Internal.SnakyRows009.named_envelope_582_28_chain : (named_envelope_582_28.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_29 Internal.SnakyRows009.named_envelope_582_30 (1017 : ℤ) (1018 : ℤ)
    Internal.SnakyRows009.named_envelope_582_29_chain Internal.SnakyRows009.named_envelope_582_30_chain Internal.SnakyRows009.named_envelope_582_29_last Internal.SnakyRows009.named_envelope_582_30_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_28_head : (named_envelope_582_28.map Internal.SnakyRows009.namedCellKey).head? = some (770 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_29 Internal.SnakyRows009.named_envelope_582_30 (770 : ℤ) Internal.SnakyRows009.named_envelope_582_29_head
theorem Internal.SnakyRows009.named_envelope_582_28_last : (named_envelope_582_28.map Internal.SnakyRows009.namedCellKey).getLast? = some (1279 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_29 Internal.SnakyRows009.named_envelope_582_30 (1279 : ℤ) Internal.SnakyRows009.named_envelope_582_30_last
def Internal.SnakyRows009.named_envelope_582_24 : List Cell := Internal.SnakyRows009.named_envelope_582_25 ++ Internal.SnakyRows009.named_envelope_582_28
theorem Internal.SnakyRows009.named_envelope_582_24_chain : (named_envelope_582_24.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_25 Internal.SnakyRows009.named_envelope_582_28 (767 : ℤ) (770 : ℤ)
    Internal.SnakyRows009.named_envelope_582_25_chain Internal.SnakyRows009.named_envelope_582_28_chain Internal.SnakyRows009.named_envelope_582_25_last Internal.SnakyRows009.named_envelope_582_28_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_24_head : (named_envelope_582_24.map Internal.SnakyRows009.namedCellKey).head? = some (632 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_25 Internal.SnakyRows009.named_envelope_582_28 (632 : ℤ) Internal.SnakyRows009.named_envelope_582_25_head
theorem Internal.SnakyRows009.named_envelope_582_24_last : (named_envelope_582_24.map Internal.SnakyRows009.namedCellKey).getLast? = some (1279 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_25 Internal.SnakyRows009.named_envelope_582_28 (1279 : ℤ) Internal.SnakyRows009.named_envelope_582_28_last
def Internal.SnakyRows009.named_envelope_582_16 : List Cell := Internal.SnakyRows009.named_envelope_582_17 ++ Internal.SnakyRows009.named_envelope_582_24
theorem Internal.SnakyRows009.named_envelope_582_16_chain : (named_envelope_582_16.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_17 Internal.SnakyRows009.named_envelope_582_24 (631 : ℤ) (632 : ℤ)
    Internal.SnakyRows009.named_envelope_582_17_chain Internal.SnakyRows009.named_envelope_582_24_chain Internal.SnakyRows009.named_envelope_582_17_last Internal.SnakyRows009.named_envelope_582_24_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_16_head : (named_envelope_582_16.map Internal.SnakyRows009.namedCellKey).head? = some (257 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_17 Internal.SnakyRows009.named_envelope_582_24 (257 : ℤ) Internal.SnakyRows009.named_envelope_582_17_head
theorem Internal.SnakyRows009.named_envelope_582_16_last : (named_envelope_582_16.map Internal.SnakyRows009.namedCellKey).getLast? = some (1279 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_17 Internal.SnakyRows009.named_envelope_582_24 (1279 : ℤ) Internal.SnakyRows009.named_envelope_582_24_last
def Internal.SnakyRows009.named_envelope_582_0 : List Cell := Internal.SnakyRows009.named_envelope_582_1 ++ Internal.SnakyRows009.named_envelope_582_16
theorem Internal.SnakyRows009.named_envelope_582_0_chain : (named_envelope_582_0.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows009.named_chain_append Internal.SnakyRows009.named_envelope_582_1 Internal.SnakyRows009.named_envelope_582_16 (256 : ℤ) (257 : ℤ)
    Internal.SnakyRows009.named_envelope_582_1_chain Internal.SnakyRows009.named_envelope_582_16_chain Internal.SnakyRows009.named_envelope_582_1_last Internal.SnakyRows009.named_envelope_582_16_head (by decide)
theorem Internal.SnakyRows009.named_envelope_582_0_head : (named_envelope_582_0.map Internal.SnakyRows009.namedCellKey).head? = some (-767 : ℤ) :=
  Internal.SnakyRows009.named_head_append Internal.SnakyRows009.named_envelope_582_1 Internal.SnakyRows009.named_envelope_582_16 (-767 : ℤ) Internal.SnakyRows009.named_envelope_582_1_head
theorem Internal.SnakyRows009.named_envelope_582_0_last : (named_envelope_582_0.map Internal.SnakyRows009.namedCellKey).getLast? = some (1279 : ℤ) :=
  Internal.SnakyRows009.named_last_append Internal.SnakyRows009.named_envelope_582_1 Internal.SnakyRows009.named_envelope_582_16 (1279 : ℤ) Internal.SnakyRows009.named_envelope_582_16_last
theorem Internal.SnakyRows009.named_envelope_582_nodup : (Internal.SnakyRows009.named_envelope_582_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows009.named_nodup_of_chain Internal.SnakyRows009.named_envelope_582_0 Internal.SnakyRows009.named_envelope_582_0_chain
def envelope_582 : Finset Cell := ⟨(Internal.SnakyRows009.named_envelope_582_0 : Multiset Cell), Internal.SnakyRows009.named_envelope_582_nodup⟩
def childrenC_582 : Fin 5 → Finset Cell := ![(placedSet 3 (0, -1) required_40), (placedSet 5 (1, -1) required_446), (placedSet 0 (3, -4) required_523), (placedSet 4 (1, -1) required_480), (placedSet 4 (1, 0) required_567)]
def childrenD_582 : Fin 5 → Finset Cell := ![(placedSet 3 (0, -1) envelope_40), (placedSet 5 (1, -1) envelope_446), (placedSet 0 (3, -4) envelope_523), (placedSet 4 (1, -1) envelope_480), (placedSet 4 (1, 0) envelope_567)]
theorem common_sub_582 : commonEnvelope childrenD_582 ⊆ insert (0, 0) required_582 := by decide
theorem child_required_sub_582 : ∀ j, childrenC_582 j ⊆ insert (0, 0) required_582 := by decide
theorem Internal.SnakyRows009.containment_582_0 :
    placedSet 3 (0, -1) envelope_40 ⊆ envelope_582 := by decide
theorem Internal.SnakyRows009.containment_582_1 :
    placedSet 5 (1, -1) envelope_446 ⊆ envelope_582 := by decide
theorem Internal.SnakyRows009.containment_582_2 :
    placedSet 0 (3, -4) envelope_523 ⊆ envelope_582 := by decide
theorem Internal.SnakyRows009.containment_582_3 :
    placedSet 4 (1, -1) envelope_480 ⊆ envelope_582 := by decide
theorem Internal.SnakyRows009.containment_582_4 :
    placedSet 4 (1, 0) envelope_567 ⊆ envelope_582 := by decide +kernel
theorem child_envelope_sub_582 : ∀ j, childrenD_582 j ⊆ envelope_582 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows009.containment_582_0
  · exact Internal.SnakyRows009.containment_582_1
  · exact Internal.SnakyRows009.containment_582_2
  · exact Internal.SnakyRows009.containment_582_3
  · exact Internal.SnakyRows009.containment_582_4
theorem pivot_mem_582 : (0, 0) ∈ envelope_582 := by decide
theorem children_work_582 : ∀ j, Template HasSnaky 23 (childrenC_582 j) (childrenD_582 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_40 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_446 5 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_523 0 (3, -4)).mono (by decide)
  · exact (placed_template_map row_works_480 4 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_567 4 (1, 0)).mono (by decide)
theorem row_works_582 : Template HasSnaky 24 required_582 envelope_582 := by
  refine compose HasSnaky 23 childrenC_582 childrenD_582 children_work_582 (0, 0)
    required_582 envelope_582 pivot_mem_582 child_required_sub_582 child_envelope_sub_582 ?_
  intro b hb; exact common_sub_582 (mem_commonEnvelope childrenD_582 b hb)
end SnakyConditional

end OAI
