import OAI.GameTheory.SnakyConditional.Templates.Level13Part07
import OAI.GameTheory.SnakyConditional.Templates.Level15Part07
import OAI.GameTheory.SnakyConditional.Templates.Level31Part01
import OAI.GameTheory.SnakyConditional.Templates.Level31Part02

namespace OAI

namespace SnakyConditional
def required_605 : Finset Cell := ⟨(([(-3, -3), (-2, -3), (-2, -2), (-2, 0), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011.named_envelope_605_5 : List Cell := ([(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_5_chain : (named_envelope_605_5.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_5_head : (named_envelope_605_5.map Internal.SnakyRows011.namedCellKey).head? = some (-897 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_5_last : (named_envelope_605_5.map Internal.SnakyRows011.namedCellKey).getLast? = some (-765 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_6 : List Cell := ([(-6, 4), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_6_chain : (named_envelope_605_6.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_6_head : (named_envelope_605_6.map Internal.SnakyRows011.namedCellKey).head? = some (-764 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_6_last : (named_envelope_605_6.map Internal.SnakyRows011.namedCellKey).getLast? = some (-637 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_4 : List Cell := Internal.SnakyRows011.named_envelope_605_5 ++ Internal.SnakyRows011.named_envelope_605_6
theorem Internal.SnakyRows011.named_envelope_605_4_chain : (named_envelope_605_4.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_5 Internal.SnakyRows011.named_envelope_605_6 (-765 : ℤ) (-764 : ℤ)
    Internal.SnakyRows011.named_envelope_605_5_chain Internal.SnakyRows011.named_envelope_605_6_chain Internal.SnakyRows011.named_envelope_605_5_last Internal.SnakyRows011.named_envelope_605_6_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_4_head : (named_envelope_605_4.map Internal.SnakyRows011.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_5 Internal.SnakyRows011.named_envelope_605_6 (-897 : ℤ) Internal.SnakyRows011.named_envelope_605_5_head
theorem Internal.SnakyRows011.named_envelope_605_4_last : (named_envelope_605_4.map Internal.SnakyRows011.namedCellKey).getLast? = some (-637 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_5 Internal.SnakyRows011.named_envelope_605_6 (-637 : ℤ) Internal.SnakyRows011.named_envelope_605_6_last
def Internal.SnakyRows011.named_envelope_605_8 : List Cell := ([(-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_8_chain : (named_envelope_605_8.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_8_head : (named_envelope_605_8.map Internal.SnakyRows011.namedCellKey).head? = some (-636 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_8_last : (named_envelope_605_8.map Internal.SnakyRows011.namedCellKey).getLast? = some (-510 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_9 : List Cell := ([(-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_9_chain : (named_envelope_605_9.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_9_head : (named_envelope_605_9.map Internal.SnakyRows011.namedCellKey).head? = some (-509 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_9_last : (named_envelope_605_9.map Internal.SnakyRows011.namedCellKey).getLast? = some (-500 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_7 : List Cell := Internal.SnakyRows011.named_envelope_605_8 ++ Internal.SnakyRows011.named_envelope_605_9
theorem Internal.SnakyRows011.named_envelope_605_7_chain : (named_envelope_605_7.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_8 Internal.SnakyRows011.named_envelope_605_9 (-510 : ℤ) (-509 : ℤ)
    Internal.SnakyRows011.named_envelope_605_8_chain Internal.SnakyRows011.named_envelope_605_9_chain Internal.SnakyRows011.named_envelope_605_8_last Internal.SnakyRows011.named_envelope_605_9_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_7_head : (named_envelope_605_7.map Internal.SnakyRows011.namedCellKey).head? = some (-636 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_8 Internal.SnakyRows011.named_envelope_605_9 (-636 : ℤ) Internal.SnakyRows011.named_envelope_605_8_head
theorem Internal.SnakyRows011.named_envelope_605_7_last : (named_envelope_605_7.map Internal.SnakyRows011.namedCellKey).getLast? = some (-500 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_8 Internal.SnakyRows011.named_envelope_605_9 (-500 : ℤ) Internal.SnakyRows011.named_envelope_605_9_last
def Internal.SnakyRows011.named_envelope_605_3 : List Cell := Internal.SnakyRows011.named_envelope_605_4 ++ Internal.SnakyRows011.named_envelope_605_7
theorem Internal.SnakyRows011.named_envelope_605_3_chain : (named_envelope_605_3.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_4 Internal.SnakyRows011.named_envelope_605_7 (-637 : ℤ) (-636 : ℤ)
    Internal.SnakyRows011.named_envelope_605_4_chain Internal.SnakyRows011.named_envelope_605_7_chain Internal.SnakyRows011.named_envelope_605_4_last Internal.SnakyRows011.named_envelope_605_7_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_3_head : (named_envelope_605_3.map Internal.SnakyRows011.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_4 Internal.SnakyRows011.named_envelope_605_7 (-897 : ℤ) Internal.SnakyRows011.named_envelope_605_4_head
theorem Internal.SnakyRows011.named_envelope_605_3_last : (named_envelope_605_3.map Internal.SnakyRows011.namedCellKey).getLast? = some (-500 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_4 Internal.SnakyRows011.named_envelope_605_7 (-500 : ℤ) Internal.SnakyRows011.named_envelope_605_7_last
def Internal.SnakyRows011.named_envelope_605_12 : List Cell := ([(-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_12_chain : (named_envelope_605_12.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_12_head : (named_envelope_605_12.map Internal.SnakyRows011.namedCellKey).head? = some (-387 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_12_last : (named_envelope_605_12.map Internal.SnakyRows011.namedCellKey).getLast? = some (-378 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_13 : List Cell := ([(-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -3), (-2, -2), (-2, 0), (-2, 1)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_13_chain : (named_envelope_605_13.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_13_head : (named_envelope_605_13.map Internal.SnakyRows011.namedCellKey).head? = some (-377 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_13_last : (named_envelope_605_13.map Internal.SnakyRows011.namedCellKey).getLast? = some (-255 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_11 : List Cell := Internal.SnakyRows011.named_envelope_605_12 ++ Internal.SnakyRows011.named_envelope_605_13
theorem Internal.SnakyRows011.named_envelope_605_11_chain : (named_envelope_605_11.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_12 Internal.SnakyRows011.named_envelope_605_13 (-378 : ℤ) (-377 : ℤ)
    Internal.SnakyRows011.named_envelope_605_12_chain Internal.SnakyRows011.named_envelope_605_13_chain Internal.SnakyRows011.named_envelope_605_12_last Internal.SnakyRows011.named_envelope_605_13_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_11_head : (named_envelope_605_11.map Internal.SnakyRows011.namedCellKey).head? = some (-387 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_12 Internal.SnakyRows011.named_envelope_605_13 (-387 : ℤ) Internal.SnakyRows011.named_envelope_605_12_head
theorem Internal.SnakyRows011.named_envelope_605_11_last : (named_envelope_605_11.map Internal.SnakyRows011.namedCellKey).getLast? = some (-255 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_12 Internal.SnakyRows011.named_envelope_605_13 (-255 : ℤ) Internal.SnakyRows011.named_envelope_605_13_last
def Internal.SnakyRows011.named_envelope_605_15 : List Cell := ([(-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_15_chain : (named_envelope_605_15.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_15_head : (named_envelope_605_15.map Internal.SnakyRows011.namedCellKey).head? = some (-254 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_15_last : (named_envelope_605_15.map Internal.SnakyRows011.namedCellKey).getLast? = some (-246 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_16 : List Cell := ([(-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_16_chain : (named_envelope_605_16.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_16_head : (named_envelope_605_16.map Internal.SnakyRows011.namedCellKey).head? = some (-245 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_16_last : (named_envelope_605_16.map Internal.SnakyRows011.namedCellKey).getLast? = some (-130 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_14 : List Cell := Internal.SnakyRows011.named_envelope_605_15 ++ Internal.SnakyRows011.named_envelope_605_16
theorem Internal.SnakyRows011.named_envelope_605_14_chain : (named_envelope_605_14.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_15 Internal.SnakyRows011.named_envelope_605_16 (-246 : ℤ) (-245 : ℤ)
    Internal.SnakyRows011.named_envelope_605_15_chain Internal.SnakyRows011.named_envelope_605_16_chain Internal.SnakyRows011.named_envelope_605_15_last Internal.SnakyRows011.named_envelope_605_16_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_14_head : (named_envelope_605_14.map Internal.SnakyRows011.namedCellKey).head? = some (-254 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_15 Internal.SnakyRows011.named_envelope_605_16 (-254 : ℤ) Internal.SnakyRows011.named_envelope_605_15_head
theorem Internal.SnakyRows011.named_envelope_605_14_last : (named_envelope_605_14.map Internal.SnakyRows011.namedCellKey).getLast? = some (-130 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_15 Internal.SnakyRows011.named_envelope_605_16 (-130 : ℤ) Internal.SnakyRows011.named_envelope_605_16_last
def Internal.SnakyRows011.named_envelope_605_10 : List Cell := Internal.SnakyRows011.named_envelope_605_11 ++ Internal.SnakyRows011.named_envelope_605_14
theorem Internal.SnakyRows011.named_envelope_605_10_chain : (named_envelope_605_10.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_11 Internal.SnakyRows011.named_envelope_605_14 (-255 : ℤ) (-254 : ℤ)
    Internal.SnakyRows011.named_envelope_605_11_chain Internal.SnakyRows011.named_envelope_605_14_chain Internal.SnakyRows011.named_envelope_605_11_last Internal.SnakyRows011.named_envelope_605_14_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_10_head : (named_envelope_605_10.map Internal.SnakyRows011.namedCellKey).head? = some (-387 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_11 Internal.SnakyRows011.named_envelope_605_14 (-387 : ℤ) Internal.SnakyRows011.named_envelope_605_11_head
theorem Internal.SnakyRows011.named_envelope_605_10_last : (named_envelope_605_10.map Internal.SnakyRows011.namedCellKey).getLast? = some (-130 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_11 Internal.SnakyRows011.named_envelope_605_14 (-130 : ℤ) Internal.SnakyRows011.named_envelope_605_14_last
def Internal.SnakyRows011.named_envelope_605_2 : List Cell := Internal.SnakyRows011.named_envelope_605_3 ++ Internal.SnakyRows011.named_envelope_605_10
theorem Internal.SnakyRows011.named_envelope_605_2_chain : (named_envelope_605_2.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_3 Internal.SnakyRows011.named_envelope_605_10 (-500 : ℤ) (-387 : ℤ)
    Internal.SnakyRows011.named_envelope_605_3_chain Internal.SnakyRows011.named_envelope_605_10_chain Internal.SnakyRows011.named_envelope_605_3_last Internal.SnakyRows011.named_envelope_605_10_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_2_head : (named_envelope_605_2.map Internal.SnakyRows011.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_3 Internal.SnakyRows011.named_envelope_605_10 (-897 : ℤ) Internal.SnakyRows011.named_envelope_605_3_head
theorem Internal.SnakyRows011.named_envelope_605_2_last : (named_envelope_605_2.map Internal.SnakyRows011.namedCellKey).getLast? = some (-130 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_3 Internal.SnakyRows011.named_envelope_605_10 (-130 : ℤ) Internal.SnakyRows011.named_envelope_605_10_last
def Internal.SnakyRows011.named_envelope_605_20 : List Cell := ([(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_20_chain : (named_envelope_605_20.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_20_head : (named_envelope_605_20.map Internal.SnakyRows011.namedCellKey).head? = some (-129 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_20_last : (named_envelope_605_20.map Internal.SnakyRows011.namedCellKey).getLast? = some (-121 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_21 : List Cell := ([(-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_21_chain : (named_envelope_605_21.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_21_head : (named_envelope_605_21.map Internal.SnakyRows011.namedCellKey).head? = some (-120 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_21_last : (named_envelope_605_21.map Internal.SnakyRows011.namedCellKey).getLast? = some (-4 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_19 : List Cell := Internal.SnakyRows011.named_envelope_605_20 ++ Internal.SnakyRows011.named_envelope_605_21
theorem Internal.SnakyRows011.named_envelope_605_19_chain : (named_envelope_605_19.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_20 Internal.SnakyRows011.named_envelope_605_21 (-121 : ℤ) (-120 : ℤ)
    Internal.SnakyRows011.named_envelope_605_20_chain Internal.SnakyRows011.named_envelope_605_21_chain Internal.SnakyRows011.named_envelope_605_20_last Internal.SnakyRows011.named_envelope_605_21_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_19_head : (named_envelope_605_19.map Internal.SnakyRows011.namedCellKey).head? = some (-129 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_20 Internal.SnakyRows011.named_envelope_605_21 (-129 : ℤ) Internal.SnakyRows011.named_envelope_605_20_head
theorem Internal.SnakyRows011.named_envelope_605_19_last : (named_envelope_605_19.map Internal.SnakyRows011.namedCellKey).getLast? = some (-4 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_20 Internal.SnakyRows011.named_envelope_605_21 (-4 : ℤ) Internal.SnakyRows011.named_envelope_605_21_last
def Internal.SnakyRows011.named_envelope_605_23 : List Cell := ([(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_23_chain : (named_envelope_605_23.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_23_head : (named_envelope_605_23.map Internal.SnakyRows011.namedCellKey).head? = some (-3 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_23_last : (named_envelope_605_23.map Internal.SnakyRows011.namedCellKey).getLast? = some (5 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_24 : List Cell := ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_24_chain : (named_envelope_605_24.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_24_head : (named_envelope_605_24.map Internal.SnakyRows011.namedCellKey).head? = some (6 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_24_last : (named_envelope_605_24.map Internal.SnakyRows011.namedCellKey).getLast? = some (121 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_22 : List Cell := Internal.SnakyRows011.named_envelope_605_23 ++ Internal.SnakyRows011.named_envelope_605_24
theorem Internal.SnakyRows011.named_envelope_605_22_chain : (named_envelope_605_22.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_23 Internal.SnakyRows011.named_envelope_605_24 (5 : ℤ) (6 : ℤ)
    Internal.SnakyRows011.named_envelope_605_23_chain Internal.SnakyRows011.named_envelope_605_24_chain Internal.SnakyRows011.named_envelope_605_23_last Internal.SnakyRows011.named_envelope_605_24_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_22_head : (named_envelope_605_22.map Internal.SnakyRows011.namedCellKey).head? = some (-3 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_23 Internal.SnakyRows011.named_envelope_605_24 (-3 : ℤ) Internal.SnakyRows011.named_envelope_605_23_head
theorem Internal.SnakyRows011.named_envelope_605_22_last : (named_envelope_605_22.map Internal.SnakyRows011.namedCellKey).getLast? = some (121 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_23 Internal.SnakyRows011.named_envelope_605_24 (121 : ℤ) Internal.SnakyRows011.named_envelope_605_24_last
def Internal.SnakyRows011.named_envelope_605_18 : List Cell := Internal.SnakyRows011.named_envelope_605_19 ++ Internal.SnakyRows011.named_envelope_605_22
theorem Internal.SnakyRows011.named_envelope_605_18_chain : (named_envelope_605_18.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_19 Internal.SnakyRows011.named_envelope_605_22 (-4 : ℤ) (-3 : ℤ)
    Internal.SnakyRows011.named_envelope_605_19_chain Internal.SnakyRows011.named_envelope_605_22_chain Internal.SnakyRows011.named_envelope_605_19_last Internal.SnakyRows011.named_envelope_605_22_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_18_head : (named_envelope_605_18.map Internal.SnakyRows011.namedCellKey).head? = some (-129 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_19 Internal.SnakyRows011.named_envelope_605_22 (-129 : ℤ) Internal.SnakyRows011.named_envelope_605_19_head
theorem Internal.SnakyRows011.named_envelope_605_18_last : (named_envelope_605_18.map Internal.SnakyRows011.namedCellKey).getLast? = some (121 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_19 Internal.SnakyRows011.named_envelope_605_22 (121 : ℤ) Internal.SnakyRows011.named_envelope_605_22_last
def Internal.SnakyRows011.named_envelope_605_27 : List Cell := ([(1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_27_chain : (named_envelope_605_27.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_27_head : (named_envelope_605_27.map Internal.SnakyRows011.namedCellKey).head? = some (122 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_27_last : (named_envelope_605_27.map Internal.SnakyRows011.namedCellKey).getLast? = some (131 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_28 : List Cell := ([(1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_28_chain : (named_envelope_605_28.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_28_head : (named_envelope_605_28.map Internal.SnakyRows011.namedCellKey).head? = some (132 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_28_last : (named_envelope_605_28.map Internal.SnakyRows011.namedCellKey).getLast? = some (140 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_26 : List Cell := Internal.SnakyRows011.named_envelope_605_27 ++ Internal.SnakyRows011.named_envelope_605_28
theorem Internal.SnakyRows011.named_envelope_605_26_chain : (named_envelope_605_26.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_27 Internal.SnakyRows011.named_envelope_605_28 (131 : ℤ) (132 : ℤ)
    Internal.SnakyRows011.named_envelope_605_27_chain Internal.SnakyRows011.named_envelope_605_28_chain Internal.SnakyRows011.named_envelope_605_27_last Internal.SnakyRows011.named_envelope_605_28_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_26_head : (named_envelope_605_26.map Internal.SnakyRows011.namedCellKey).head? = some (122 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_27 Internal.SnakyRows011.named_envelope_605_28 (122 : ℤ) Internal.SnakyRows011.named_envelope_605_27_head
theorem Internal.SnakyRows011.named_envelope_605_26_last : (named_envelope_605_26.map Internal.SnakyRows011.namedCellKey).getLast? = some (140 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_27 Internal.SnakyRows011.named_envelope_605_28 (140 : ℤ) Internal.SnakyRows011.named_envelope_605_28_last
def Internal.SnakyRows011.named_envelope_605_30 : List Cell := ([(2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_30_chain : (named_envelope_605_30.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_30_head : (named_envelope_605_30.map Internal.SnakyRows011.namedCellKey).head? = some (250 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_30_last : (named_envelope_605_30.map Internal.SnakyRows011.namedCellKey).getLast? = some (258 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_31 : List Cell := ([(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_31_chain : (named_envelope_605_31.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_31_head : (named_envelope_605_31.map Internal.SnakyRows011.namedCellKey).head? = some (259 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_31_last : (named_envelope_605_31.map Internal.SnakyRows011.namedCellKey).getLast? = some (268 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_29 : List Cell := Internal.SnakyRows011.named_envelope_605_30 ++ Internal.SnakyRows011.named_envelope_605_31
theorem Internal.SnakyRows011.named_envelope_605_29_chain : (named_envelope_605_29.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_30 Internal.SnakyRows011.named_envelope_605_31 (258 : ℤ) (259 : ℤ)
    Internal.SnakyRows011.named_envelope_605_30_chain Internal.SnakyRows011.named_envelope_605_31_chain Internal.SnakyRows011.named_envelope_605_30_last Internal.SnakyRows011.named_envelope_605_31_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_29_head : (named_envelope_605_29.map Internal.SnakyRows011.namedCellKey).head? = some (250 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_30 Internal.SnakyRows011.named_envelope_605_31 (250 : ℤ) Internal.SnakyRows011.named_envelope_605_30_head
theorem Internal.SnakyRows011.named_envelope_605_29_last : (named_envelope_605_29.map Internal.SnakyRows011.namedCellKey).getLast? = some (268 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_30 Internal.SnakyRows011.named_envelope_605_31 (268 : ℤ) Internal.SnakyRows011.named_envelope_605_31_last
def Internal.SnakyRows011.named_envelope_605_25 : List Cell := Internal.SnakyRows011.named_envelope_605_26 ++ Internal.SnakyRows011.named_envelope_605_29
theorem Internal.SnakyRows011.named_envelope_605_25_chain : (named_envelope_605_25.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_26 Internal.SnakyRows011.named_envelope_605_29 (140 : ℤ) (250 : ℤ)
    Internal.SnakyRows011.named_envelope_605_26_chain Internal.SnakyRows011.named_envelope_605_29_chain Internal.SnakyRows011.named_envelope_605_26_last Internal.SnakyRows011.named_envelope_605_29_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_25_head : (named_envelope_605_25.map Internal.SnakyRows011.namedCellKey).head? = some (122 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_26 Internal.SnakyRows011.named_envelope_605_29 (122 : ℤ) Internal.SnakyRows011.named_envelope_605_26_head
theorem Internal.SnakyRows011.named_envelope_605_25_last : (named_envelope_605_25.map Internal.SnakyRows011.namedCellKey).getLast? = some (268 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_26 Internal.SnakyRows011.named_envelope_605_29 (268 : ℤ) Internal.SnakyRows011.named_envelope_605_29_last
def Internal.SnakyRows011.named_envelope_605_17 : List Cell := Internal.SnakyRows011.named_envelope_605_18 ++ Internal.SnakyRows011.named_envelope_605_25
theorem Internal.SnakyRows011.named_envelope_605_17_chain : (named_envelope_605_17.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_18 Internal.SnakyRows011.named_envelope_605_25 (121 : ℤ) (122 : ℤ)
    Internal.SnakyRows011.named_envelope_605_18_chain Internal.SnakyRows011.named_envelope_605_25_chain Internal.SnakyRows011.named_envelope_605_18_last Internal.SnakyRows011.named_envelope_605_25_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_17_head : (named_envelope_605_17.map Internal.SnakyRows011.namedCellKey).head? = some (-129 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_18 Internal.SnakyRows011.named_envelope_605_25 (-129 : ℤ) Internal.SnakyRows011.named_envelope_605_18_head
theorem Internal.SnakyRows011.named_envelope_605_17_last : (named_envelope_605_17.map Internal.SnakyRows011.namedCellKey).getLast? = some (268 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_18 Internal.SnakyRows011.named_envelope_605_25 (268 : ℤ) Internal.SnakyRows011.named_envelope_605_25_last
def Internal.SnakyRows011.named_envelope_605_1 : List Cell := Internal.SnakyRows011.named_envelope_605_2 ++ Internal.SnakyRows011.named_envelope_605_17
theorem Internal.SnakyRows011.named_envelope_605_1_chain : (named_envelope_605_1.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_2 Internal.SnakyRows011.named_envelope_605_17 (-130 : ℤ) (-129 : ℤ)
    Internal.SnakyRows011.named_envelope_605_2_chain Internal.SnakyRows011.named_envelope_605_17_chain Internal.SnakyRows011.named_envelope_605_2_last Internal.SnakyRows011.named_envelope_605_17_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_1_head : (named_envelope_605_1.map Internal.SnakyRows011.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_2 Internal.SnakyRows011.named_envelope_605_17 (-897 : ℤ) Internal.SnakyRows011.named_envelope_605_2_head
theorem Internal.SnakyRows011.named_envelope_605_1_last : (named_envelope_605_1.map Internal.SnakyRows011.namedCellKey).getLast? = some (268 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_2 Internal.SnakyRows011.named_envelope_605_17 (268 : ℤ) Internal.SnakyRows011.named_envelope_605_17_last
def Internal.SnakyRows011.named_envelope_605_36 : List Cell := ([(3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_36_chain : (named_envelope_605_36.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_36_head : (named_envelope_605_36.map Internal.SnakyRows011.namedCellKey).head? = some (379 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_36_last : (named_envelope_605_36.map Internal.SnakyRows011.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_37 : List Cell := ([(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_37_chain : (named_envelope_605_37.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_37_head : (named_envelope_605_37.map Internal.SnakyRows011.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_37_last : (named_envelope_605_37.map Internal.SnakyRows011.namedCellKey).getLast? = some (396 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_35 : List Cell := Internal.SnakyRows011.named_envelope_605_36 ++ Internal.SnakyRows011.named_envelope_605_37
theorem Internal.SnakyRows011.named_envelope_605_35_chain : (named_envelope_605_35.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_36 Internal.SnakyRows011.named_envelope_605_37 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows011.named_envelope_605_36_chain Internal.SnakyRows011.named_envelope_605_37_chain Internal.SnakyRows011.named_envelope_605_36_last Internal.SnakyRows011.named_envelope_605_37_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_35_head : (named_envelope_605_35.map Internal.SnakyRows011.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_36 Internal.SnakyRows011.named_envelope_605_37 (379 : ℤ) Internal.SnakyRows011.named_envelope_605_36_head
theorem Internal.SnakyRows011.named_envelope_605_35_last : (named_envelope_605_35.map Internal.SnakyRows011.namedCellKey).getLast? = some (396 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_36 Internal.SnakyRows011.named_envelope_605_37 (396 : ℤ) Internal.SnakyRows011.named_envelope_605_37_last
def Internal.SnakyRows011.named_envelope_605_39 : List Cell := ([(4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_39_chain : (named_envelope_605_39.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_39_head : (named_envelope_605_39.map Internal.SnakyRows011.namedCellKey).head? = some (506 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_39_last : (named_envelope_605_39.map Internal.SnakyRows011.namedCellKey).getLast? = some (514 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_40 : List Cell := ([(4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_40_chain : (named_envelope_605_40.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_40_head : (named_envelope_605_40.map Internal.SnakyRows011.namedCellKey).head? = some (515 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_40_last : (named_envelope_605_40.map Internal.SnakyRows011.namedCellKey).getLast? = some (524 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_38 : List Cell := Internal.SnakyRows011.named_envelope_605_39 ++ Internal.SnakyRows011.named_envelope_605_40
theorem Internal.SnakyRows011.named_envelope_605_38_chain : (named_envelope_605_38.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_39 Internal.SnakyRows011.named_envelope_605_40 (514 : ℤ) (515 : ℤ)
    Internal.SnakyRows011.named_envelope_605_39_chain Internal.SnakyRows011.named_envelope_605_40_chain Internal.SnakyRows011.named_envelope_605_39_last Internal.SnakyRows011.named_envelope_605_40_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_38_head : (named_envelope_605_38.map Internal.SnakyRows011.namedCellKey).head? = some (506 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_39 Internal.SnakyRows011.named_envelope_605_40 (506 : ℤ) Internal.SnakyRows011.named_envelope_605_39_head
theorem Internal.SnakyRows011.named_envelope_605_38_last : (named_envelope_605_38.map Internal.SnakyRows011.namedCellKey).getLast? = some (524 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_39 Internal.SnakyRows011.named_envelope_605_40 (524 : ℤ) Internal.SnakyRows011.named_envelope_605_40_last
def Internal.SnakyRows011.named_envelope_605_34 : List Cell := Internal.SnakyRows011.named_envelope_605_35 ++ Internal.SnakyRows011.named_envelope_605_38
theorem Internal.SnakyRows011.named_envelope_605_34_chain : (named_envelope_605_34.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_35 Internal.SnakyRows011.named_envelope_605_38 (396 : ℤ) (506 : ℤ)
    Internal.SnakyRows011.named_envelope_605_35_chain Internal.SnakyRows011.named_envelope_605_38_chain Internal.SnakyRows011.named_envelope_605_35_last Internal.SnakyRows011.named_envelope_605_38_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_34_head : (named_envelope_605_34.map Internal.SnakyRows011.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_35 Internal.SnakyRows011.named_envelope_605_38 (379 : ℤ) Internal.SnakyRows011.named_envelope_605_35_head
theorem Internal.SnakyRows011.named_envelope_605_34_last : (named_envelope_605_34.map Internal.SnakyRows011.namedCellKey).getLast? = some (524 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_35 Internal.SnakyRows011.named_envelope_605_38 (524 : ℤ) Internal.SnakyRows011.named_envelope_605_38_last
def Internal.SnakyRows011.named_envelope_605_43 : List Cell := ([(5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_43_chain : (named_envelope_605_43.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_43_head : (named_envelope_605_43.map Internal.SnakyRows011.namedCellKey).head? = some (636 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_43_last : (named_envelope_605_43.map Internal.SnakyRows011.namedCellKey).getLast? = some (644 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_44 : List Cell := ([(5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_44_chain : (named_envelope_605_44.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_44_head : (named_envelope_605_44.map Internal.SnakyRows011.namedCellKey).head? = some (645 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_44_last : (named_envelope_605_44.map Internal.SnakyRows011.namedCellKey).getLast? = some (764 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_42 : List Cell := Internal.SnakyRows011.named_envelope_605_43 ++ Internal.SnakyRows011.named_envelope_605_44
theorem Internal.SnakyRows011.named_envelope_605_42_chain : (named_envelope_605_42.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_43 Internal.SnakyRows011.named_envelope_605_44 (644 : ℤ) (645 : ℤ)
    Internal.SnakyRows011.named_envelope_605_43_chain Internal.SnakyRows011.named_envelope_605_44_chain Internal.SnakyRows011.named_envelope_605_43_last Internal.SnakyRows011.named_envelope_605_44_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_42_head : (named_envelope_605_42.map Internal.SnakyRows011.namedCellKey).head? = some (636 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_43 Internal.SnakyRows011.named_envelope_605_44 (636 : ℤ) Internal.SnakyRows011.named_envelope_605_43_head
theorem Internal.SnakyRows011.named_envelope_605_42_last : (named_envelope_605_42.map Internal.SnakyRows011.namedCellKey).getLast? = some (764 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_43 Internal.SnakyRows011.named_envelope_605_44 (764 : ℤ) Internal.SnakyRows011.named_envelope_605_44_last
def Internal.SnakyRows011.named_envelope_605_46 : List Cell := ([(6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_46_chain : (named_envelope_605_46.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_46_head : (named_envelope_605_46.map Internal.SnakyRows011.namedCellKey).head? = some (765 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_46_last : (named_envelope_605_46.map Internal.SnakyRows011.namedCellKey).getLast? = some (773 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_47 : List Cell := ([(6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_47_chain : (named_envelope_605_47.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_47_head : (named_envelope_605_47.map Internal.SnakyRows011.namedCellKey).head? = some (774 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_47_last : (named_envelope_605_47.map Internal.SnakyRows011.namedCellKey).getLast? = some (894 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_45 : List Cell := Internal.SnakyRows011.named_envelope_605_46 ++ Internal.SnakyRows011.named_envelope_605_47
theorem Internal.SnakyRows011.named_envelope_605_45_chain : (named_envelope_605_45.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_46 Internal.SnakyRows011.named_envelope_605_47 (773 : ℤ) (774 : ℤ)
    Internal.SnakyRows011.named_envelope_605_46_chain Internal.SnakyRows011.named_envelope_605_47_chain Internal.SnakyRows011.named_envelope_605_46_last Internal.SnakyRows011.named_envelope_605_47_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_45_head : (named_envelope_605_45.map Internal.SnakyRows011.namedCellKey).head? = some (765 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_46 Internal.SnakyRows011.named_envelope_605_47 (765 : ℤ) Internal.SnakyRows011.named_envelope_605_46_head
theorem Internal.SnakyRows011.named_envelope_605_45_last : (named_envelope_605_45.map Internal.SnakyRows011.namedCellKey).getLast? = some (894 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_46 Internal.SnakyRows011.named_envelope_605_47 (894 : ℤ) Internal.SnakyRows011.named_envelope_605_47_last
def Internal.SnakyRows011.named_envelope_605_41 : List Cell := Internal.SnakyRows011.named_envelope_605_42 ++ Internal.SnakyRows011.named_envelope_605_45
theorem Internal.SnakyRows011.named_envelope_605_41_chain : (named_envelope_605_41.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_42 Internal.SnakyRows011.named_envelope_605_45 (764 : ℤ) (765 : ℤ)
    Internal.SnakyRows011.named_envelope_605_42_chain Internal.SnakyRows011.named_envelope_605_45_chain Internal.SnakyRows011.named_envelope_605_42_last Internal.SnakyRows011.named_envelope_605_45_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_41_head : (named_envelope_605_41.map Internal.SnakyRows011.namedCellKey).head? = some (636 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_42 Internal.SnakyRows011.named_envelope_605_45 (636 : ℤ) Internal.SnakyRows011.named_envelope_605_42_head
theorem Internal.SnakyRows011.named_envelope_605_41_last : (named_envelope_605_41.map Internal.SnakyRows011.namedCellKey).getLast? = some (894 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_42 Internal.SnakyRows011.named_envelope_605_45 (894 : ℤ) Internal.SnakyRows011.named_envelope_605_45_last
def Internal.SnakyRows011.named_envelope_605_33 : List Cell := Internal.SnakyRows011.named_envelope_605_34 ++ Internal.SnakyRows011.named_envelope_605_41
theorem Internal.SnakyRows011.named_envelope_605_33_chain : (named_envelope_605_33.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_34 Internal.SnakyRows011.named_envelope_605_41 (524 : ℤ) (636 : ℤ)
    Internal.SnakyRows011.named_envelope_605_34_chain Internal.SnakyRows011.named_envelope_605_41_chain Internal.SnakyRows011.named_envelope_605_34_last Internal.SnakyRows011.named_envelope_605_41_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_33_head : (named_envelope_605_33.map Internal.SnakyRows011.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_34 Internal.SnakyRows011.named_envelope_605_41 (379 : ℤ) Internal.SnakyRows011.named_envelope_605_34_head
theorem Internal.SnakyRows011.named_envelope_605_33_last : (named_envelope_605_33.map Internal.SnakyRows011.namedCellKey).getLast? = some (894 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_34 Internal.SnakyRows011.named_envelope_605_41 (894 : ℤ) Internal.SnakyRows011.named_envelope_605_41_last
def Internal.SnakyRows011.named_envelope_605_51 : List Cell := ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_51_chain : (named_envelope_605_51.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_51_head : (named_envelope_605_51.map Internal.SnakyRows011.namedCellKey).head? = some (895 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_51_last : (named_envelope_605_51.map Internal.SnakyRows011.namedCellKey).getLast? = some (903 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_52 : List Cell := ([(7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_52_chain : (named_envelope_605_52.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_52_head : (named_envelope_605_52.map Internal.SnakyRows011.namedCellKey).head? = some (904 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_52_last : (named_envelope_605_52.map Internal.SnakyRows011.namedCellKey).getLast? = some (1024 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_50 : List Cell := Internal.SnakyRows011.named_envelope_605_51 ++ Internal.SnakyRows011.named_envelope_605_52
theorem Internal.SnakyRows011.named_envelope_605_50_chain : (named_envelope_605_50.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_51 Internal.SnakyRows011.named_envelope_605_52 (903 : ℤ) (904 : ℤ)
    Internal.SnakyRows011.named_envelope_605_51_chain Internal.SnakyRows011.named_envelope_605_52_chain Internal.SnakyRows011.named_envelope_605_51_last Internal.SnakyRows011.named_envelope_605_52_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_50_head : (named_envelope_605_50.map Internal.SnakyRows011.namedCellKey).head? = some (895 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_51 Internal.SnakyRows011.named_envelope_605_52 (895 : ℤ) Internal.SnakyRows011.named_envelope_605_51_head
theorem Internal.SnakyRows011.named_envelope_605_50_last : (named_envelope_605_50.map Internal.SnakyRows011.namedCellKey).getLast? = some (1024 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_51 Internal.SnakyRows011.named_envelope_605_52 (1024 : ℤ) Internal.SnakyRows011.named_envelope_605_52_last
def Internal.SnakyRows011.named_envelope_605_54 : List Cell := ([(8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_54_chain : (named_envelope_605_54.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_54_head : (named_envelope_605_54.map Internal.SnakyRows011.namedCellKey).head? = some (1025 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_54_last : (named_envelope_605_54.map Internal.SnakyRows011.namedCellKey).getLast? = some (1146 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_55 : List Cell := ([(9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_55_chain : (named_envelope_605_55.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_55_head : (named_envelope_605_55.map Internal.SnakyRows011.namedCellKey).head? = some (1147 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_55_last : (named_envelope_605_55.map Internal.SnakyRows011.namedCellKey).getLast? = some (1156 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_53 : List Cell := Internal.SnakyRows011.named_envelope_605_54 ++ Internal.SnakyRows011.named_envelope_605_55
theorem Internal.SnakyRows011.named_envelope_605_53_chain : (named_envelope_605_53.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_54 Internal.SnakyRows011.named_envelope_605_55 (1146 : ℤ) (1147 : ℤ)
    Internal.SnakyRows011.named_envelope_605_54_chain Internal.SnakyRows011.named_envelope_605_55_chain Internal.SnakyRows011.named_envelope_605_54_last Internal.SnakyRows011.named_envelope_605_55_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_53_head : (named_envelope_605_53.map Internal.SnakyRows011.namedCellKey).head? = some (1025 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_54 Internal.SnakyRows011.named_envelope_605_55 (1025 : ℤ) Internal.SnakyRows011.named_envelope_605_54_head
theorem Internal.SnakyRows011.named_envelope_605_53_last : (named_envelope_605_53.map Internal.SnakyRows011.namedCellKey).getLast? = some (1156 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_54 Internal.SnakyRows011.named_envelope_605_55 (1156 : ℤ) Internal.SnakyRows011.named_envelope_605_55_last
def Internal.SnakyRows011.named_envelope_605_49 : List Cell := Internal.SnakyRows011.named_envelope_605_50 ++ Internal.SnakyRows011.named_envelope_605_53
theorem Internal.SnakyRows011.named_envelope_605_49_chain : (named_envelope_605_49.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_50 Internal.SnakyRows011.named_envelope_605_53 (1024 : ℤ) (1025 : ℤ)
    Internal.SnakyRows011.named_envelope_605_50_chain Internal.SnakyRows011.named_envelope_605_53_chain Internal.SnakyRows011.named_envelope_605_50_last Internal.SnakyRows011.named_envelope_605_53_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_49_head : (named_envelope_605_49.map Internal.SnakyRows011.namedCellKey).head? = some (895 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_50 Internal.SnakyRows011.named_envelope_605_53 (895 : ℤ) Internal.SnakyRows011.named_envelope_605_50_head
theorem Internal.SnakyRows011.named_envelope_605_49_last : (named_envelope_605_49.map Internal.SnakyRows011.namedCellKey).getLast? = some (1156 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_50 Internal.SnakyRows011.named_envelope_605_53 (1156 : ℤ) Internal.SnakyRows011.named_envelope_605_53_last
def Internal.SnakyRows011.named_envelope_605_58 : List Cell := ([(9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_58_chain : (named_envelope_605_58.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_58_head : (named_envelope_605_58.map Internal.SnakyRows011.namedCellKey).head? = some (1157 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_58_last : (named_envelope_605_58.map Internal.SnakyRows011.namedCellKey).getLast? = some (1281 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_59 : List Cell := ([(10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_59_chain : (named_envelope_605_59.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_59_head : (named_envelope_605_59.map Internal.SnakyRows011.namedCellKey).head? = some (1282 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_59_last : (named_envelope_605_59.map Internal.SnakyRows011.namedCellKey).getLast? = some (1406 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_57 : List Cell := Internal.SnakyRows011.named_envelope_605_58 ++ Internal.SnakyRows011.named_envelope_605_59
theorem Internal.SnakyRows011.named_envelope_605_57_chain : (named_envelope_605_57.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_58 Internal.SnakyRows011.named_envelope_605_59 (1281 : ℤ) (1282 : ℤ)
    Internal.SnakyRows011.named_envelope_605_58_chain Internal.SnakyRows011.named_envelope_605_59_chain Internal.SnakyRows011.named_envelope_605_58_last Internal.SnakyRows011.named_envelope_605_59_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_57_head : (named_envelope_605_57.map Internal.SnakyRows011.namedCellKey).head? = some (1157 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_58 Internal.SnakyRows011.named_envelope_605_59 (1157 : ℤ) Internal.SnakyRows011.named_envelope_605_58_head
theorem Internal.SnakyRows011.named_envelope_605_57_last : (named_envelope_605_57.map Internal.SnakyRows011.namedCellKey).getLast? = some (1406 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_58 Internal.SnakyRows011.named_envelope_605_59 (1406 : ℤ) Internal.SnakyRows011.named_envelope_605_59_last
def Internal.SnakyRows011.named_envelope_605_61 : List Cell := ([(11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_61_chain : (named_envelope_605_61.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_61_head : (named_envelope_605_61.map Internal.SnakyRows011.namedCellKey).head? = some (1407 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_61_last : (named_envelope_605_61.map Internal.SnakyRows011.namedCellKey).getLast? = some (1535 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_62 : List Cell := ([(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)] : List Cell)
theorem Internal.SnakyRows011.named_envelope_605_62_chain : (named_envelope_605_62.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011.named_envelope_605_62_head : (named_envelope_605_62.map Internal.SnakyRows011.namedCellKey).head? = some (1536 : ℤ) := by decide
theorem Internal.SnakyRows011.named_envelope_605_62_last : (named_envelope_605_62.map Internal.SnakyRows011.namedCellKey).getLast? = some (1792 : ℤ) := by decide
def Internal.SnakyRows011.named_envelope_605_60 : List Cell := Internal.SnakyRows011.named_envelope_605_61 ++ Internal.SnakyRows011.named_envelope_605_62
theorem Internal.SnakyRows011.named_envelope_605_60_chain : (named_envelope_605_60.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_61 Internal.SnakyRows011.named_envelope_605_62 (1535 : ℤ) (1536 : ℤ)
    Internal.SnakyRows011.named_envelope_605_61_chain Internal.SnakyRows011.named_envelope_605_62_chain Internal.SnakyRows011.named_envelope_605_61_last Internal.SnakyRows011.named_envelope_605_62_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_60_head : (named_envelope_605_60.map Internal.SnakyRows011.namedCellKey).head? = some (1407 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_61 Internal.SnakyRows011.named_envelope_605_62 (1407 : ℤ) Internal.SnakyRows011.named_envelope_605_61_head
theorem Internal.SnakyRows011.named_envelope_605_60_last : (named_envelope_605_60.map Internal.SnakyRows011.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_61 Internal.SnakyRows011.named_envelope_605_62 (1792 : ℤ) Internal.SnakyRows011.named_envelope_605_62_last
def Internal.SnakyRows011.named_envelope_605_56 : List Cell := Internal.SnakyRows011.named_envelope_605_57 ++ Internal.SnakyRows011.named_envelope_605_60
theorem Internal.SnakyRows011.named_envelope_605_56_chain : (named_envelope_605_56.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_57 Internal.SnakyRows011.named_envelope_605_60 (1406 : ℤ) (1407 : ℤ)
    Internal.SnakyRows011.named_envelope_605_57_chain Internal.SnakyRows011.named_envelope_605_60_chain Internal.SnakyRows011.named_envelope_605_57_last Internal.SnakyRows011.named_envelope_605_60_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_56_head : (named_envelope_605_56.map Internal.SnakyRows011.namedCellKey).head? = some (1157 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_57 Internal.SnakyRows011.named_envelope_605_60 (1157 : ℤ) Internal.SnakyRows011.named_envelope_605_57_head
theorem Internal.SnakyRows011.named_envelope_605_56_last : (named_envelope_605_56.map Internal.SnakyRows011.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_57 Internal.SnakyRows011.named_envelope_605_60 (1792 : ℤ) Internal.SnakyRows011.named_envelope_605_60_last
def Internal.SnakyRows011.named_envelope_605_48 : List Cell := Internal.SnakyRows011.named_envelope_605_49 ++ Internal.SnakyRows011.named_envelope_605_56
theorem Internal.SnakyRows011.named_envelope_605_48_chain : (named_envelope_605_48.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_49 Internal.SnakyRows011.named_envelope_605_56 (1156 : ℤ) (1157 : ℤ)
    Internal.SnakyRows011.named_envelope_605_49_chain Internal.SnakyRows011.named_envelope_605_56_chain Internal.SnakyRows011.named_envelope_605_49_last Internal.SnakyRows011.named_envelope_605_56_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_48_head : (named_envelope_605_48.map Internal.SnakyRows011.namedCellKey).head? = some (895 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_49 Internal.SnakyRows011.named_envelope_605_56 (895 : ℤ) Internal.SnakyRows011.named_envelope_605_49_head
theorem Internal.SnakyRows011.named_envelope_605_48_last : (named_envelope_605_48.map Internal.SnakyRows011.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_49 Internal.SnakyRows011.named_envelope_605_56 (1792 : ℤ) Internal.SnakyRows011.named_envelope_605_56_last
def Internal.SnakyRows011.named_envelope_605_32 : List Cell := Internal.SnakyRows011.named_envelope_605_33 ++ Internal.SnakyRows011.named_envelope_605_48
theorem Internal.SnakyRows011.named_envelope_605_32_chain : (named_envelope_605_32.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_33 Internal.SnakyRows011.named_envelope_605_48 (894 : ℤ) (895 : ℤ)
    Internal.SnakyRows011.named_envelope_605_33_chain Internal.SnakyRows011.named_envelope_605_48_chain Internal.SnakyRows011.named_envelope_605_33_last Internal.SnakyRows011.named_envelope_605_48_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_32_head : (named_envelope_605_32.map Internal.SnakyRows011.namedCellKey).head? = some (379 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_33 Internal.SnakyRows011.named_envelope_605_48 (379 : ℤ) Internal.SnakyRows011.named_envelope_605_33_head
theorem Internal.SnakyRows011.named_envelope_605_32_last : (named_envelope_605_32.map Internal.SnakyRows011.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_33 Internal.SnakyRows011.named_envelope_605_48 (1792 : ℤ) Internal.SnakyRows011.named_envelope_605_48_last
def Internal.SnakyRows011.named_envelope_605_0 : List Cell := Internal.SnakyRows011.named_envelope_605_1 ++ Internal.SnakyRows011.named_envelope_605_32
theorem Internal.SnakyRows011.named_envelope_605_0_chain : (named_envelope_605_0.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011.named_chain_append Internal.SnakyRows011.named_envelope_605_1 Internal.SnakyRows011.named_envelope_605_32 (268 : ℤ) (379 : ℤ)
    Internal.SnakyRows011.named_envelope_605_1_chain Internal.SnakyRows011.named_envelope_605_32_chain Internal.SnakyRows011.named_envelope_605_1_last Internal.SnakyRows011.named_envelope_605_32_head (by decide)
theorem Internal.SnakyRows011.named_envelope_605_0_head : (named_envelope_605_0.map Internal.SnakyRows011.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows011.named_head_append Internal.SnakyRows011.named_envelope_605_1 Internal.SnakyRows011.named_envelope_605_32 (-897 : ℤ) Internal.SnakyRows011.named_envelope_605_1_head
theorem Internal.SnakyRows011.named_envelope_605_0_last : (named_envelope_605_0.map Internal.SnakyRows011.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows011.named_last_append Internal.SnakyRows011.named_envelope_605_1 Internal.SnakyRows011.named_envelope_605_32 (1792 : ℤ) Internal.SnakyRows011.named_envelope_605_32_last
theorem Internal.SnakyRows011.named_envelope_605_nodup : (Internal.SnakyRows011.named_envelope_605_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011.named_nodup_of_chain Internal.SnakyRows011.named_envelope_605_0 Internal.SnakyRows011.named_envelope_605_0_chain
def envelope_605 : Finset Cell := ⟨(Internal.SnakyRows011.named_envelope_605_0 : Multiset Cell), Internal.SnakyRows011.named_envelope_605_nodup⟩
def childrenC_605 : Fin 9 → Finset Cell := ![(placedSet 5 (0, -1) required_400), (placedSet 6 (-1, 0) required_383), (placedSet 4 (0, -1) required_530), (placedSet 1 (-1, 0) required_596), (placedSet 2 (0, -1) required_522), (placedSet 0 (0, -1) required_598), (placedSet 3 (-1, 0) required_537), (placedSet 1 (0, -1) required_520), (placedSet 4 (0, -1) required_550)]
def childrenD_605 : Fin 9 → Finset Cell := ![(placedSet 5 (0, -1) envelope_400), (placedSet 6 (-1, 0) envelope_383), (placedSet 4 (0, -1) envelope_530), (placedSet 1 (-1, 0) envelope_596), (placedSet 2 (0, -1) envelope_522), (placedSet 0 (0, -1) envelope_598), (placedSet 3 (-1, 0) envelope_537), (placedSet 1 (0, -1) envelope_520), (placedSet 4 (0, -1) envelope_550)]
theorem common_sub_605 : commonEnvelope childrenD_605 ⊆ insert (0, 0) required_605 := by decide
theorem child_required_sub_605 : ∀ j, childrenC_605 j ⊆ insert (0, 0) required_605 := by decide
theorem Internal.SnakyRows011.containment_605_0 :
    placedSet 5 (0, -1) envelope_400 ⊆ envelope_605 := by decide
theorem Internal.SnakyRows011.containment_605_1 :
    placedSet 6 (-1, 0) envelope_383 ⊆ envelope_605 := by decide
theorem Internal.SnakyRows011.containment_605_2 :
    placedSet 4 (0, -1) envelope_530 ⊆ envelope_605 := by decide
theorem Internal.SnakyRows011.containment_605_3 :
    placedSet 1 (-1, 0) envelope_596 ⊆ envelope_605 := by decide +kernel
theorem Internal.SnakyRows011.containment_605_4 :
    placedSet 2 (0, -1) envelope_522 ⊆ envelope_605 := by decide
theorem Internal.SnakyRows011.containment_605_5 :
    placedSet 0 (0, -1) envelope_598 ⊆ envelope_605 := by decide +kernel
theorem Internal.SnakyRows011.containment_605_6 :
    placedSet 3 (-1, 0) envelope_537 ⊆ envelope_605 := by decide
theorem Internal.SnakyRows011.containment_605_7 :
    placedSet 1 (0, -1) envelope_520 ⊆ envelope_605 := by decide
theorem Internal.SnakyRows011.containment_605_8 :
    placedSet 4 (0, -1) envelope_550 ⊆ envelope_605 := by decide
theorem child_envelope_sub_605 : ∀ j, childrenD_605 j ⊆ envelope_605 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011.containment_605_0
  · exact Internal.SnakyRows011.containment_605_1
  · exact Internal.SnakyRows011.containment_605_2
  · exact Internal.SnakyRows011.containment_605_3
  · exact Internal.SnakyRows011.containment_605_4
  · exact Internal.SnakyRows011.containment_605_5
  · exact Internal.SnakyRows011.containment_605_6
  · exact Internal.SnakyRows011.containment_605_7
  · exact Internal.SnakyRows011.containment_605_8
theorem pivot_mem_605 : (0, 0) ∈ envelope_605 := by decide
theorem children_work_605 : ∀ j, Template HasSnaky 29 (childrenC_605 j) (childrenD_605 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_400 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_383 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_530 4 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_596 1 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_522 2 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_598 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_537 3 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_520 1 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_550 4 (0, -1)).mono (by decide)
theorem row_works_605 : Template HasSnaky 30 required_605 envelope_605 := by
  refine compose HasSnaky 29 childrenC_605 childrenD_605 children_work_605 (0, 0)
    required_605 envelope_605 pivot_mem_605 child_required_sub_605 child_envelope_sub_605 ?_
  intro b hb; exact common_sub_605 (mem_commonEnvelope childrenD_605 b hb)
end SnakyConditional

end OAI
