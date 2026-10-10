import OAI.GameTheory.SnakyConditional.Templates.Level29Part01
import OAI.GameTheory.SnakyConditional.Templates.Level30Part01
import OAI.GameTheory.SnakyConditional.Templates.Level30Part03

namespace OAI

namespace SnakyConditional
def required_607 : Finset Cell := ⟨(([(-1, -2), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows012B.named_envelope_607_5 : List Cell := ([(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 6)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_5_chain : (named_envelope_607_5.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_5_head : (named_envelope_607_5.map Internal.SnakyRows012B.namedCellKey).head? = some (-897 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_5_last : (named_envelope_607_5.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-762 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_6 : List Cell := ([(-6, 7), (-6, 9), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_6_chain : (named_envelope_607_6.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_6_head : (named_envelope_607_6.map Internal.SnakyRows012B.namedCellKey).head? = some (-761 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_6_last : (named_envelope_607_6.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-634 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_4 : List Cell := Internal.SnakyRows012B.named_envelope_607_5 ++ Internal.SnakyRows012B.named_envelope_607_6
theorem Internal.SnakyRows012B.named_envelope_607_4_chain : (named_envelope_607_4.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_5 Internal.SnakyRows012B.named_envelope_607_6 (-762 : ℤ) (-761 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_5_chain Internal.SnakyRows012B.named_envelope_607_6_chain Internal.SnakyRows012B.named_envelope_607_5_last Internal.SnakyRows012B.named_envelope_607_6_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_4_head : (named_envelope_607_4.map Internal.SnakyRows012B.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_5 Internal.SnakyRows012B.named_envelope_607_6 (-897 : ℤ) Internal.SnakyRows012B.named_envelope_607_5_head
theorem Internal.SnakyRows012B.named_envelope_607_4_last : (named_envelope_607_4.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-634 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_5 Internal.SnakyRows012B.named_envelope_607_6 (-634 : ℤ) Internal.SnakyRows012B.named_envelope_607_6_last
def Internal.SnakyRows012B.named_envelope_607_8 : List Cell := ([(-5, 7), (-5, 8), (-5, 9), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_8_chain : (named_envelope_607_8.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_8_head : (named_envelope_607_8.map Internal.SnakyRows012B.namedCellKey).head? = some (-633 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_8_last : (named_envelope_607_8.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-512 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_9 : List Cell := ([(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_9_chain : (named_envelope_607_9.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_9_head : (named_envelope_607_9.map Internal.SnakyRows012B.namedCellKey).head? = some (-511 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_9_last : (named_envelope_607_9.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-502 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_7 : List Cell := Internal.SnakyRows012B.named_envelope_607_8 ++ Internal.SnakyRows012B.named_envelope_607_9
theorem Internal.SnakyRows012B.named_envelope_607_7_chain : (named_envelope_607_7.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_8 Internal.SnakyRows012B.named_envelope_607_9 (-512 : ℤ) (-511 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_8_chain Internal.SnakyRows012B.named_envelope_607_9_chain Internal.SnakyRows012B.named_envelope_607_8_last Internal.SnakyRows012B.named_envelope_607_9_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_7_head : (named_envelope_607_7.map Internal.SnakyRows012B.namedCellKey).head? = some (-633 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_8 Internal.SnakyRows012B.named_envelope_607_9 (-633 : ℤ) Internal.SnakyRows012B.named_envelope_607_8_head
theorem Internal.SnakyRows012B.named_envelope_607_7_last : (named_envelope_607_7.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-502 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_8 Internal.SnakyRows012B.named_envelope_607_9 (-502 : ℤ) Internal.SnakyRows012B.named_envelope_607_9_last
def Internal.SnakyRows012B.named_envelope_607_3 : List Cell := Internal.SnakyRows012B.named_envelope_607_4 ++ Internal.SnakyRows012B.named_envelope_607_7
theorem Internal.SnakyRows012B.named_envelope_607_3_chain : (named_envelope_607_3.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_4 Internal.SnakyRows012B.named_envelope_607_7 (-634 : ℤ) (-633 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_4_chain Internal.SnakyRows012B.named_envelope_607_7_chain Internal.SnakyRows012B.named_envelope_607_4_last Internal.SnakyRows012B.named_envelope_607_7_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_3_head : (named_envelope_607_3.map Internal.SnakyRows012B.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_4 Internal.SnakyRows012B.named_envelope_607_7 (-897 : ℤ) Internal.SnakyRows012B.named_envelope_607_4_head
theorem Internal.SnakyRows012B.named_envelope_607_3_last : (named_envelope_607_3.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-502 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_4 Internal.SnakyRows012B.named_envelope_607_7 (-502 : ℤ) Internal.SnakyRows012B.named_envelope_607_7_last
def Internal.SnakyRows012B.named_envelope_607_12 : List Cell := ([(-4, 11), (-4, 12), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_12_chain : (named_envelope_607_12.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_12_head : (named_envelope_607_12.map Internal.SnakyRows012B.namedCellKey).head? = some (-501 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_12_last : (named_envelope_607_12.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-382 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_13 : List Cell := ([(-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_13_chain : (named_envelope_607_13.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_13_head : (named_envelope_607_13.map Internal.SnakyRows012B.namedCellKey).head? = some (-381 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_13_last : (named_envelope_607_13.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-373 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_11 : List Cell := Internal.SnakyRows012B.named_envelope_607_12 ++ Internal.SnakyRows012B.named_envelope_607_13
theorem Internal.SnakyRows012B.named_envelope_607_11_chain : (named_envelope_607_11.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_12 Internal.SnakyRows012B.named_envelope_607_13 (-382 : ℤ) (-381 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_12_chain Internal.SnakyRows012B.named_envelope_607_13_chain Internal.SnakyRows012B.named_envelope_607_12_last Internal.SnakyRows012B.named_envelope_607_13_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_11_head : (named_envelope_607_11.map Internal.SnakyRows012B.namedCellKey).head? = some (-501 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_12 Internal.SnakyRows012B.named_envelope_607_13 (-501 : ℤ) Internal.SnakyRows012B.named_envelope_607_12_head
theorem Internal.SnakyRows012B.named_envelope_607_11_last : (named_envelope_607_11.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-373 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_12 Internal.SnakyRows012B.named_envelope_607_13 (-373 : ℤ) Internal.SnakyRows012B.named_envelope_607_13_last
def Internal.SnakyRows012B.named_envelope_607_15 : List Cell := ([(-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_15_chain : (named_envelope_607_15.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_15_head : (named_envelope_607_15.map Internal.SnakyRows012B.namedCellKey).head? = some (-259 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_15_last : (named_envelope_607_15.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-251 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_16 : List Cell := ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -2)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_16_chain : (named_envelope_607_16.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_16_head : (named_envelope_607_16.map Internal.SnakyRows012B.namedCellKey).head? = some (-250 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_16_last : (named_envelope_607_16.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-130 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_14 : List Cell := Internal.SnakyRows012B.named_envelope_607_15 ++ Internal.SnakyRows012B.named_envelope_607_16
theorem Internal.SnakyRows012B.named_envelope_607_14_chain : (named_envelope_607_14.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_15 Internal.SnakyRows012B.named_envelope_607_16 (-251 : ℤ) (-250 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_15_chain Internal.SnakyRows012B.named_envelope_607_16_chain Internal.SnakyRows012B.named_envelope_607_15_last Internal.SnakyRows012B.named_envelope_607_16_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_14_head : (named_envelope_607_14.map Internal.SnakyRows012B.namedCellKey).head? = some (-259 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_15 Internal.SnakyRows012B.named_envelope_607_16 (-259 : ℤ) Internal.SnakyRows012B.named_envelope_607_15_head
theorem Internal.SnakyRows012B.named_envelope_607_14_last : (named_envelope_607_14.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-130 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_15 Internal.SnakyRows012B.named_envelope_607_16 (-130 : ℤ) Internal.SnakyRows012B.named_envelope_607_16_last
def Internal.SnakyRows012B.named_envelope_607_10 : List Cell := Internal.SnakyRows012B.named_envelope_607_11 ++ Internal.SnakyRows012B.named_envelope_607_14
theorem Internal.SnakyRows012B.named_envelope_607_10_chain : (named_envelope_607_10.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_11 Internal.SnakyRows012B.named_envelope_607_14 (-373 : ℤ) (-259 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_11_chain Internal.SnakyRows012B.named_envelope_607_14_chain Internal.SnakyRows012B.named_envelope_607_11_last Internal.SnakyRows012B.named_envelope_607_14_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_10_head : (named_envelope_607_10.map Internal.SnakyRows012B.namedCellKey).head? = some (-501 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_11 Internal.SnakyRows012B.named_envelope_607_14 (-501 : ℤ) Internal.SnakyRows012B.named_envelope_607_11_head
theorem Internal.SnakyRows012B.named_envelope_607_10_last : (named_envelope_607_10.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-130 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_11 Internal.SnakyRows012B.named_envelope_607_14 (-130 : ℤ) Internal.SnakyRows012B.named_envelope_607_14_last
def Internal.SnakyRows012B.named_envelope_607_2 : List Cell := Internal.SnakyRows012B.named_envelope_607_3 ++ Internal.SnakyRows012B.named_envelope_607_10
theorem Internal.SnakyRows012B.named_envelope_607_2_chain : (named_envelope_607_2.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_3 Internal.SnakyRows012B.named_envelope_607_10 (-502 : ℤ) (-501 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_3_chain Internal.SnakyRows012B.named_envelope_607_10_chain Internal.SnakyRows012B.named_envelope_607_3_last Internal.SnakyRows012B.named_envelope_607_10_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_2_head : (named_envelope_607_2.map Internal.SnakyRows012B.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_3 Internal.SnakyRows012B.named_envelope_607_10 (-897 : ℤ) Internal.SnakyRows012B.named_envelope_607_3_head
theorem Internal.SnakyRows012B.named_envelope_607_2_last : (named_envelope_607_2.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-130 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_3 Internal.SnakyRows012B.named_envelope_607_10 (-130 : ℤ) Internal.SnakyRows012B.named_envelope_607_10_last
def Internal.SnakyRows012B.named_envelope_607_20 : List Cell := ([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_20_chain : (named_envelope_607_20.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_20_head : (named_envelope_607_20.map Internal.SnakyRows012B.namedCellKey).head? = some (-128 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_20_last : (named_envelope_607_20.map Internal.SnakyRows012B.namedCellKey).getLast? = some (-120 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_21 : List Cell := ([(-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -3), (0, -2), (0, -1), (0, 0)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_21_chain : (named_envelope_607_21.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_21_head : (named_envelope_607_21.map Internal.SnakyRows012B.namedCellKey).head? = some (-119 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_21_last : (named_envelope_607_21.map Internal.SnakyRows012B.namedCellKey).getLast? = some (0 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_19 : List Cell := Internal.SnakyRows012B.named_envelope_607_20 ++ Internal.SnakyRows012B.named_envelope_607_21
theorem Internal.SnakyRows012B.named_envelope_607_19_chain : (named_envelope_607_19.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_20 Internal.SnakyRows012B.named_envelope_607_21 (-120 : ℤ) (-119 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_20_chain Internal.SnakyRows012B.named_envelope_607_21_chain Internal.SnakyRows012B.named_envelope_607_20_last Internal.SnakyRows012B.named_envelope_607_21_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_19_head : (named_envelope_607_19.map Internal.SnakyRows012B.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_20 Internal.SnakyRows012B.named_envelope_607_21 (-128 : ℤ) Internal.SnakyRows012B.named_envelope_607_20_head
theorem Internal.SnakyRows012B.named_envelope_607_19_last : (named_envelope_607_19.map Internal.SnakyRows012B.namedCellKey).getLast? = some (0 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_20 Internal.SnakyRows012B.named_envelope_607_21 (0 : ℤ) Internal.SnakyRows012B.named_envelope_607_21_last
def Internal.SnakyRows012B.named_envelope_607_23 : List Cell := ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_23_chain : (named_envelope_607_23.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_23_head : (named_envelope_607_23.map Internal.SnakyRows012B.namedCellKey).head? = some (1 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_23_last : (named_envelope_607_23.map Internal.SnakyRows012B.namedCellKey).getLast? = some (9 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_24 : List Cell := ([(0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_24_chain : (named_envelope_607_24.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_24_head : (named_envelope_607_24.map Internal.SnakyRows012B.namedCellKey).head? = some (10 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_24_last : (named_envelope_607_24.map Internal.SnakyRows012B.namedCellKey).getLast? = some (129 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_22 : List Cell := Internal.SnakyRows012B.named_envelope_607_23 ++ Internal.SnakyRows012B.named_envelope_607_24
theorem Internal.SnakyRows012B.named_envelope_607_22_chain : (named_envelope_607_22.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_23 Internal.SnakyRows012B.named_envelope_607_24 (9 : ℤ) (10 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_23_chain Internal.SnakyRows012B.named_envelope_607_24_chain Internal.SnakyRows012B.named_envelope_607_23_last Internal.SnakyRows012B.named_envelope_607_24_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_22_head : (named_envelope_607_22.map Internal.SnakyRows012B.namedCellKey).head? = some (1 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_23 Internal.SnakyRows012B.named_envelope_607_24 (1 : ℤ) Internal.SnakyRows012B.named_envelope_607_23_head
theorem Internal.SnakyRows012B.named_envelope_607_22_last : (named_envelope_607_22.map Internal.SnakyRows012B.namedCellKey).getLast? = some (129 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_23 Internal.SnakyRows012B.named_envelope_607_24 (129 : ℤ) Internal.SnakyRows012B.named_envelope_607_24_last
def Internal.SnakyRows012B.named_envelope_607_18 : List Cell := Internal.SnakyRows012B.named_envelope_607_19 ++ Internal.SnakyRows012B.named_envelope_607_22
theorem Internal.SnakyRows012B.named_envelope_607_18_chain : (named_envelope_607_18.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_19 Internal.SnakyRows012B.named_envelope_607_22 (0 : ℤ) (1 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_19_chain Internal.SnakyRows012B.named_envelope_607_22_chain Internal.SnakyRows012B.named_envelope_607_19_last Internal.SnakyRows012B.named_envelope_607_22_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_18_head : (named_envelope_607_18.map Internal.SnakyRows012B.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_19 Internal.SnakyRows012B.named_envelope_607_22 (-128 : ℤ) Internal.SnakyRows012B.named_envelope_607_19_head
theorem Internal.SnakyRows012B.named_envelope_607_18_last : (named_envelope_607_18.map Internal.SnakyRows012B.namedCellKey).getLast? = some (129 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_19 Internal.SnakyRows012B.named_envelope_607_22 (129 : ℤ) Internal.SnakyRows012B.named_envelope_607_22_last
def Internal.SnakyRows012B.named_envelope_607_27 : List Cell := ([(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_27_chain : (named_envelope_607_27.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_27_head : (named_envelope_607_27.map Internal.SnakyRows012B.namedCellKey).head? = some (130 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_27_last : (named_envelope_607_27.map Internal.SnakyRows012B.namedCellKey).getLast? = some (138 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_28 : List Cell := ([(1, 11), (1, 12), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_28_chain : (named_envelope_607_28.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_28_head : (named_envelope_607_28.map Internal.SnakyRows012B.namedCellKey).head? = some (139 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_28_last : (named_envelope_607_28.map Internal.SnakyRows012B.namedCellKey).getLast? = some (257 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_26 : List Cell := Internal.SnakyRows012B.named_envelope_607_27 ++ Internal.SnakyRows012B.named_envelope_607_28
theorem Internal.SnakyRows012B.named_envelope_607_26_chain : (named_envelope_607_26.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_27 Internal.SnakyRows012B.named_envelope_607_28 (138 : ℤ) (139 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_27_chain Internal.SnakyRows012B.named_envelope_607_28_chain Internal.SnakyRows012B.named_envelope_607_27_last Internal.SnakyRows012B.named_envelope_607_28_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_26_head : (named_envelope_607_26.map Internal.SnakyRows012B.namedCellKey).head? = some (130 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_27 Internal.SnakyRows012B.named_envelope_607_28 (130 : ℤ) Internal.SnakyRows012B.named_envelope_607_27_head
theorem Internal.SnakyRows012B.named_envelope_607_26_last : (named_envelope_607_26.map Internal.SnakyRows012B.namedCellKey).getLast? = some (257 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_27 Internal.SnakyRows012B.named_envelope_607_28 (257 : ℤ) Internal.SnakyRows012B.named_envelope_607_28_last
def Internal.SnakyRows012B.named_envelope_607_30 : List Cell := ([(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_30_chain : (named_envelope_607_30.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_30_head : (named_envelope_607_30.map Internal.SnakyRows012B.namedCellKey).head? = some (258 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_30_last : (named_envelope_607_30.map Internal.SnakyRows012B.namedCellKey).getLast? = some (266 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_31 : List Cell := ([(2, 11), (2, 12), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_31_chain : (named_envelope_607_31.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_31_head : (named_envelope_607_31.map Internal.SnakyRows012B.namedCellKey).head? = some (267 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_31_last : (named_envelope_607_31.map Internal.SnakyRows012B.namedCellKey).getLast? = some (385 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_29 : List Cell := Internal.SnakyRows012B.named_envelope_607_30 ++ Internal.SnakyRows012B.named_envelope_607_31
theorem Internal.SnakyRows012B.named_envelope_607_29_chain : (named_envelope_607_29.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_30 Internal.SnakyRows012B.named_envelope_607_31 (266 : ℤ) (267 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_30_chain Internal.SnakyRows012B.named_envelope_607_31_chain Internal.SnakyRows012B.named_envelope_607_30_last Internal.SnakyRows012B.named_envelope_607_31_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_29_head : (named_envelope_607_29.map Internal.SnakyRows012B.namedCellKey).head? = some (258 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_30 Internal.SnakyRows012B.named_envelope_607_31 (258 : ℤ) Internal.SnakyRows012B.named_envelope_607_30_head
theorem Internal.SnakyRows012B.named_envelope_607_29_last : (named_envelope_607_29.map Internal.SnakyRows012B.namedCellKey).getLast? = some (385 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_30 Internal.SnakyRows012B.named_envelope_607_31 (385 : ℤ) Internal.SnakyRows012B.named_envelope_607_31_last
def Internal.SnakyRows012B.named_envelope_607_25 : List Cell := Internal.SnakyRows012B.named_envelope_607_26 ++ Internal.SnakyRows012B.named_envelope_607_29
theorem Internal.SnakyRows012B.named_envelope_607_25_chain : (named_envelope_607_25.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_26 Internal.SnakyRows012B.named_envelope_607_29 (257 : ℤ) (258 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_26_chain Internal.SnakyRows012B.named_envelope_607_29_chain Internal.SnakyRows012B.named_envelope_607_26_last Internal.SnakyRows012B.named_envelope_607_29_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_25_head : (named_envelope_607_25.map Internal.SnakyRows012B.namedCellKey).head? = some (130 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_26 Internal.SnakyRows012B.named_envelope_607_29 (130 : ℤ) Internal.SnakyRows012B.named_envelope_607_26_head
theorem Internal.SnakyRows012B.named_envelope_607_25_last : (named_envelope_607_25.map Internal.SnakyRows012B.namedCellKey).getLast? = some (385 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_26 Internal.SnakyRows012B.named_envelope_607_29 (385 : ℤ) Internal.SnakyRows012B.named_envelope_607_29_last
def Internal.SnakyRows012B.named_envelope_607_17 : List Cell := Internal.SnakyRows012B.named_envelope_607_18 ++ Internal.SnakyRows012B.named_envelope_607_25
theorem Internal.SnakyRows012B.named_envelope_607_17_chain : (named_envelope_607_17.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_18 Internal.SnakyRows012B.named_envelope_607_25 (129 : ℤ) (130 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_18_chain Internal.SnakyRows012B.named_envelope_607_25_chain Internal.SnakyRows012B.named_envelope_607_18_last Internal.SnakyRows012B.named_envelope_607_25_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_17_head : (named_envelope_607_17.map Internal.SnakyRows012B.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_18 Internal.SnakyRows012B.named_envelope_607_25 (-128 : ℤ) Internal.SnakyRows012B.named_envelope_607_18_head
theorem Internal.SnakyRows012B.named_envelope_607_17_last : (named_envelope_607_17.map Internal.SnakyRows012B.namedCellKey).getLast? = some (385 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_18 Internal.SnakyRows012B.named_envelope_607_25 (385 : ℤ) Internal.SnakyRows012B.named_envelope_607_25_last
def Internal.SnakyRows012B.named_envelope_607_1 : List Cell := Internal.SnakyRows012B.named_envelope_607_2 ++ Internal.SnakyRows012B.named_envelope_607_17
theorem Internal.SnakyRows012B.named_envelope_607_1_chain : (named_envelope_607_1.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_2 Internal.SnakyRows012B.named_envelope_607_17 (-130 : ℤ) (-128 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_2_chain Internal.SnakyRows012B.named_envelope_607_17_chain Internal.SnakyRows012B.named_envelope_607_2_last Internal.SnakyRows012B.named_envelope_607_17_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_1_head : (named_envelope_607_1.map Internal.SnakyRows012B.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_2 Internal.SnakyRows012B.named_envelope_607_17 (-897 : ℤ) Internal.SnakyRows012B.named_envelope_607_2_head
theorem Internal.SnakyRows012B.named_envelope_607_1_last : (named_envelope_607_1.map Internal.SnakyRows012B.namedCellKey).getLast? = some (385 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_2 Internal.SnakyRows012B.named_envelope_607_17 (385 : ℤ) Internal.SnakyRows012B.named_envelope_607_17_last
def Internal.SnakyRows012B.named_envelope_607_36 : List Cell := ([(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_36_chain : (named_envelope_607_36.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_36_head : (named_envelope_607_36.map Internal.SnakyRows012B.namedCellKey).head? = some (386 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_36_last : (named_envelope_607_36.map Internal.SnakyRows012B.namedCellKey).getLast? = some (394 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_37 : List Cell := ([(3, 11), (3, 12), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_37_chain : (named_envelope_607_37.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_37_head : (named_envelope_607_37.map Internal.SnakyRows012B.namedCellKey).head? = some (395 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_37_last : (named_envelope_607_37.map Internal.SnakyRows012B.namedCellKey).getLast? = some (511 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_35 : List Cell := Internal.SnakyRows012B.named_envelope_607_36 ++ Internal.SnakyRows012B.named_envelope_607_37
theorem Internal.SnakyRows012B.named_envelope_607_35_chain : (named_envelope_607_35.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_36 Internal.SnakyRows012B.named_envelope_607_37 (394 : ℤ) (395 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_36_chain Internal.SnakyRows012B.named_envelope_607_37_chain Internal.SnakyRows012B.named_envelope_607_36_last Internal.SnakyRows012B.named_envelope_607_37_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_35_head : (named_envelope_607_35.map Internal.SnakyRows012B.namedCellKey).head? = some (386 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_36 Internal.SnakyRows012B.named_envelope_607_37 (386 : ℤ) Internal.SnakyRows012B.named_envelope_607_36_head
theorem Internal.SnakyRows012B.named_envelope_607_35_last : (named_envelope_607_35.map Internal.SnakyRows012B.namedCellKey).getLast? = some (511 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_36 Internal.SnakyRows012B.named_envelope_607_37 (511 : ℤ) Internal.SnakyRows012B.named_envelope_607_37_last
def Internal.SnakyRows012B.named_envelope_607_39 : List Cell := ([(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_39_chain : (named_envelope_607_39.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_39_head : (named_envelope_607_39.map Internal.SnakyRows012B.namedCellKey).head? = some (512 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_39_last : (named_envelope_607_39.map Internal.SnakyRows012B.namedCellKey).getLast? = some (520 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_40 : List Cell := ([(4, 9), (4, 10), (4, 11), (4, 12), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_40_chain : (named_envelope_607_40.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_40_head : (named_envelope_607_40.map Internal.SnakyRows012B.namedCellKey).head? = some (521 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_40_last : (named_envelope_607_40.map Internal.SnakyRows012B.namedCellKey).getLast? = some (637 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_38 : List Cell := Internal.SnakyRows012B.named_envelope_607_39 ++ Internal.SnakyRows012B.named_envelope_607_40
theorem Internal.SnakyRows012B.named_envelope_607_38_chain : (named_envelope_607_38.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_39 Internal.SnakyRows012B.named_envelope_607_40 (520 : ℤ) (521 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_39_chain Internal.SnakyRows012B.named_envelope_607_40_chain Internal.SnakyRows012B.named_envelope_607_39_last Internal.SnakyRows012B.named_envelope_607_40_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_38_head : (named_envelope_607_38.map Internal.SnakyRows012B.namedCellKey).head? = some (512 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_39 Internal.SnakyRows012B.named_envelope_607_40 (512 : ℤ) Internal.SnakyRows012B.named_envelope_607_39_head
theorem Internal.SnakyRows012B.named_envelope_607_38_last : (named_envelope_607_38.map Internal.SnakyRows012B.namedCellKey).getLast? = some (637 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_39 Internal.SnakyRows012B.named_envelope_607_40 (637 : ℤ) Internal.SnakyRows012B.named_envelope_607_40_last
def Internal.SnakyRows012B.named_envelope_607_34 : List Cell := Internal.SnakyRows012B.named_envelope_607_35 ++ Internal.SnakyRows012B.named_envelope_607_38
theorem Internal.SnakyRows012B.named_envelope_607_34_chain : (named_envelope_607_34.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_35 Internal.SnakyRows012B.named_envelope_607_38 (511 : ℤ) (512 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_35_chain Internal.SnakyRows012B.named_envelope_607_38_chain Internal.SnakyRows012B.named_envelope_607_35_last Internal.SnakyRows012B.named_envelope_607_38_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_34_head : (named_envelope_607_34.map Internal.SnakyRows012B.namedCellKey).head? = some (386 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_35 Internal.SnakyRows012B.named_envelope_607_38 (386 : ℤ) Internal.SnakyRows012B.named_envelope_607_35_head
theorem Internal.SnakyRows012B.named_envelope_607_34_last : (named_envelope_607_34.map Internal.SnakyRows012B.namedCellKey).getLast? = some (637 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_35 Internal.SnakyRows012B.named_envelope_607_38 (637 : ℤ) Internal.SnakyRows012B.named_envelope_607_38_last
def Internal.SnakyRows012B.named_envelope_607_43 : List Cell := ([(5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_43_chain : (named_envelope_607_43.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_43_head : (named_envelope_607_43.map Internal.SnakyRows012B.namedCellKey).head? = some (638 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_43_last : (named_envelope_607_43.map Internal.SnakyRows012B.namedCellKey).getLast? = some (646 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_44 : List Cell := ([(5, 7), (5, 8), (5, 9), (5, 10), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_44_chain : (named_envelope_607_44.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_44_head : (named_envelope_607_44.map Internal.SnakyRows012B.namedCellKey).head? = some (647 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_44_last : (named_envelope_607_44.map Internal.SnakyRows012B.namedCellKey).getLast? = some (766 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_42 : List Cell := Internal.SnakyRows012B.named_envelope_607_43 ++ Internal.SnakyRows012B.named_envelope_607_44
theorem Internal.SnakyRows012B.named_envelope_607_42_chain : (named_envelope_607_42.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_43 Internal.SnakyRows012B.named_envelope_607_44 (646 : ℤ) (647 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_43_chain Internal.SnakyRows012B.named_envelope_607_44_chain Internal.SnakyRows012B.named_envelope_607_43_last Internal.SnakyRows012B.named_envelope_607_44_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_42_head : (named_envelope_607_42.map Internal.SnakyRows012B.namedCellKey).head? = some (638 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_43 Internal.SnakyRows012B.named_envelope_607_44 (638 : ℤ) Internal.SnakyRows012B.named_envelope_607_43_head
theorem Internal.SnakyRows012B.named_envelope_607_42_last : (named_envelope_607_42.map Internal.SnakyRows012B.namedCellKey).getLast? = some (766 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_43 Internal.SnakyRows012B.named_envelope_607_44 (766 : ℤ) Internal.SnakyRows012B.named_envelope_607_44_last
def Internal.SnakyRows012B.named_envelope_607_46 : List Cell := ([(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_46_chain : (named_envelope_607_46.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_46_head : (named_envelope_607_46.map Internal.SnakyRows012B.namedCellKey).head? = some (767 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_46_last : (named_envelope_607_46.map Internal.SnakyRows012B.namedCellKey).getLast? = some (775 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_47 : List Cell := ([(6, 8), (6, 9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_47_chain : (named_envelope_607_47.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_47_head : (named_envelope_607_47.map Internal.SnakyRows012B.namedCellKey).head? = some (776 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_47_last : (named_envelope_607_47.map Internal.SnakyRows012B.namedCellKey).getLast? = some (895 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_45 : List Cell := Internal.SnakyRows012B.named_envelope_607_46 ++ Internal.SnakyRows012B.named_envelope_607_47
theorem Internal.SnakyRows012B.named_envelope_607_45_chain : (named_envelope_607_45.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_46 Internal.SnakyRows012B.named_envelope_607_47 (775 : ℤ) (776 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_46_chain Internal.SnakyRows012B.named_envelope_607_47_chain Internal.SnakyRows012B.named_envelope_607_46_last Internal.SnakyRows012B.named_envelope_607_47_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_45_head : (named_envelope_607_45.map Internal.SnakyRows012B.namedCellKey).head? = some (767 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_46 Internal.SnakyRows012B.named_envelope_607_47 (767 : ℤ) Internal.SnakyRows012B.named_envelope_607_46_head
theorem Internal.SnakyRows012B.named_envelope_607_45_last : (named_envelope_607_45.map Internal.SnakyRows012B.namedCellKey).getLast? = some (895 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_46 Internal.SnakyRows012B.named_envelope_607_47 (895 : ℤ) Internal.SnakyRows012B.named_envelope_607_47_last
def Internal.SnakyRows012B.named_envelope_607_41 : List Cell := Internal.SnakyRows012B.named_envelope_607_42 ++ Internal.SnakyRows012B.named_envelope_607_45
theorem Internal.SnakyRows012B.named_envelope_607_41_chain : (named_envelope_607_41.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_42 Internal.SnakyRows012B.named_envelope_607_45 (766 : ℤ) (767 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_42_chain Internal.SnakyRows012B.named_envelope_607_45_chain Internal.SnakyRows012B.named_envelope_607_42_last Internal.SnakyRows012B.named_envelope_607_45_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_41_head : (named_envelope_607_41.map Internal.SnakyRows012B.namedCellKey).head? = some (638 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_42 Internal.SnakyRows012B.named_envelope_607_45 (638 : ℤ) Internal.SnakyRows012B.named_envelope_607_42_head
theorem Internal.SnakyRows012B.named_envelope_607_41_last : (named_envelope_607_41.map Internal.SnakyRows012B.namedCellKey).getLast? = some (895 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_42 Internal.SnakyRows012B.named_envelope_607_45 (895 : ℤ) Internal.SnakyRows012B.named_envelope_607_45_last
def Internal.SnakyRows012B.named_envelope_607_33 : List Cell := Internal.SnakyRows012B.named_envelope_607_34 ++ Internal.SnakyRows012B.named_envelope_607_41
theorem Internal.SnakyRows012B.named_envelope_607_33_chain : (named_envelope_607_33.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_34 Internal.SnakyRows012B.named_envelope_607_41 (637 : ℤ) (638 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_34_chain Internal.SnakyRows012B.named_envelope_607_41_chain Internal.SnakyRows012B.named_envelope_607_34_last Internal.SnakyRows012B.named_envelope_607_41_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_33_head : (named_envelope_607_33.map Internal.SnakyRows012B.namedCellKey).head? = some (386 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_34 Internal.SnakyRows012B.named_envelope_607_41 (386 : ℤ) Internal.SnakyRows012B.named_envelope_607_34_head
theorem Internal.SnakyRows012B.named_envelope_607_33_last : (named_envelope_607_33.map Internal.SnakyRows012B.namedCellKey).getLast? = some (895 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_34 Internal.SnakyRows012B.named_envelope_607_41 (895 : ℤ) Internal.SnakyRows012B.named_envelope_607_41_last
def Internal.SnakyRows012B.named_envelope_607_51 : List Cell := ([(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_51_chain : (named_envelope_607_51.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_51_head : (named_envelope_607_51.map Internal.SnakyRows012B.namedCellKey).head? = some (896 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_51_last : (named_envelope_607_51.map Internal.SnakyRows012B.namedCellKey).getLast? = some (904 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_52 : List Cell := ([(7, 9), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_52_chain : (named_envelope_607_52.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_52_head : (named_envelope_607_52.map Internal.SnakyRows012B.namedCellKey).head? = some (905 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_52_last : (named_envelope_607_52.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1025 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_50 : List Cell := Internal.SnakyRows012B.named_envelope_607_51 ++ Internal.SnakyRows012B.named_envelope_607_52
theorem Internal.SnakyRows012B.named_envelope_607_50_chain : (named_envelope_607_50.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_51 Internal.SnakyRows012B.named_envelope_607_52 (904 : ℤ) (905 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_51_chain Internal.SnakyRows012B.named_envelope_607_52_chain Internal.SnakyRows012B.named_envelope_607_51_last Internal.SnakyRows012B.named_envelope_607_52_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_50_head : (named_envelope_607_50.map Internal.SnakyRows012B.namedCellKey).head? = some (896 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_51 Internal.SnakyRows012B.named_envelope_607_52 (896 : ℤ) Internal.SnakyRows012B.named_envelope_607_51_head
theorem Internal.SnakyRows012B.named_envelope_607_50_last : (named_envelope_607_50.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1025 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_51 Internal.SnakyRows012B.named_envelope_607_52 (1025 : ℤ) Internal.SnakyRows012B.named_envelope_607_52_last
def Internal.SnakyRows012B.named_envelope_607_54 : List Cell := ([(8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_54_chain : (named_envelope_607_54.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_54_head : (named_envelope_607_54.map Internal.SnakyRows012B.namedCellKey).head? = some (1026 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_54_last : (named_envelope_607_54.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1147 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_55 : List Cell := ([(9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_55_chain : (named_envelope_607_55.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_55_head : (named_envelope_607_55.map Internal.SnakyRows012B.namedCellKey).head? = some (1148 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_55_last : (named_envelope_607_55.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1157 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_53 : List Cell := Internal.SnakyRows012B.named_envelope_607_54 ++ Internal.SnakyRows012B.named_envelope_607_55
theorem Internal.SnakyRows012B.named_envelope_607_53_chain : (named_envelope_607_53.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_54 Internal.SnakyRows012B.named_envelope_607_55 (1147 : ℤ) (1148 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_54_chain Internal.SnakyRows012B.named_envelope_607_55_chain Internal.SnakyRows012B.named_envelope_607_54_last Internal.SnakyRows012B.named_envelope_607_55_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_53_head : (named_envelope_607_53.map Internal.SnakyRows012B.namedCellKey).head? = some (1026 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_54 Internal.SnakyRows012B.named_envelope_607_55 (1026 : ℤ) Internal.SnakyRows012B.named_envelope_607_54_head
theorem Internal.SnakyRows012B.named_envelope_607_53_last : (named_envelope_607_53.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1157 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_54 Internal.SnakyRows012B.named_envelope_607_55 (1157 : ℤ) Internal.SnakyRows012B.named_envelope_607_55_last
def Internal.SnakyRows012B.named_envelope_607_49 : List Cell := Internal.SnakyRows012B.named_envelope_607_50 ++ Internal.SnakyRows012B.named_envelope_607_53
theorem Internal.SnakyRows012B.named_envelope_607_49_chain : (named_envelope_607_49.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_50 Internal.SnakyRows012B.named_envelope_607_53 (1025 : ℤ) (1026 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_50_chain Internal.SnakyRows012B.named_envelope_607_53_chain Internal.SnakyRows012B.named_envelope_607_50_last Internal.SnakyRows012B.named_envelope_607_53_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_49_head : (named_envelope_607_49.map Internal.SnakyRows012B.namedCellKey).head? = some (896 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_50 Internal.SnakyRows012B.named_envelope_607_53 (896 : ℤ) Internal.SnakyRows012B.named_envelope_607_50_head
theorem Internal.SnakyRows012B.named_envelope_607_49_last : (named_envelope_607_49.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1157 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_50 Internal.SnakyRows012B.named_envelope_607_53 (1157 : ℤ) Internal.SnakyRows012B.named_envelope_607_53_last
def Internal.SnakyRows012B.named_envelope_607_58 : List Cell := ([(9, 6), (9, 7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_58_chain : (named_envelope_607_58.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_58_head : (named_envelope_607_58.map Internal.SnakyRows012B.namedCellKey).head? = some (1158 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_58_last : (named_envelope_607_58.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1280 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_59 : List Cell := ([(10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -5), (11, -4), (11, -3)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_59_chain : (named_envelope_607_59.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_59_head : (named_envelope_607_59.map Internal.SnakyRows012B.namedCellKey).head? = some (1281 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_59_last : (named_envelope_607_59.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1405 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_57 : List Cell := Internal.SnakyRows012B.named_envelope_607_58 ++ Internal.SnakyRows012B.named_envelope_607_59
theorem Internal.SnakyRows012B.named_envelope_607_57_chain : (named_envelope_607_57.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_58 Internal.SnakyRows012B.named_envelope_607_59 (1280 : ℤ) (1281 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_58_chain Internal.SnakyRows012B.named_envelope_607_59_chain Internal.SnakyRows012B.named_envelope_607_58_last Internal.SnakyRows012B.named_envelope_607_59_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_57_head : (named_envelope_607_57.map Internal.SnakyRows012B.namedCellKey).head? = some (1158 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_58 Internal.SnakyRows012B.named_envelope_607_59 (1158 : ℤ) Internal.SnakyRows012B.named_envelope_607_58_head
theorem Internal.SnakyRows012B.named_envelope_607_57_last : (named_envelope_607_57.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1405 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_58 Internal.SnakyRows012B.named_envelope_607_59 (1405 : ℤ) Internal.SnakyRows012B.named_envelope_607_59_last
def Internal.SnakyRows012B.named_envelope_607_61 : List Cell := ([(11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (12, -4), (12, -3), (12, -2)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_61_chain : (named_envelope_607_61.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_61_head : (named_envelope_607_61.map Internal.SnakyRows012B.namedCellKey).head? = some (1406 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_61_last : (named_envelope_607_61.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1534 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_62 : List Cell := ([(12, -1), (12, 0), (12, 1), (12, 3), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1)] : List Cell)
theorem Internal.SnakyRows012B.named_envelope_607_62_chain : (named_envelope_607_62.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_62_head : (named_envelope_607_62.map Internal.SnakyRows012B.namedCellKey).head? = some (1535 : ℤ) := by decide
theorem Internal.SnakyRows012B.named_envelope_607_62_last : (named_envelope_607_62.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1665 : ℤ) := by decide
def Internal.SnakyRows012B.named_envelope_607_60 : List Cell := Internal.SnakyRows012B.named_envelope_607_61 ++ Internal.SnakyRows012B.named_envelope_607_62
theorem Internal.SnakyRows012B.named_envelope_607_60_chain : (named_envelope_607_60.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_61 Internal.SnakyRows012B.named_envelope_607_62 (1534 : ℤ) (1535 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_61_chain Internal.SnakyRows012B.named_envelope_607_62_chain Internal.SnakyRows012B.named_envelope_607_61_last Internal.SnakyRows012B.named_envelope_607_62_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_60_head : (named_envelope_607_60.map Internal.SnakyRows012B.namedCellKey).head? = some (1406 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_61 Internal.SnakyRows012B.named_envelope_607_62 (1406 : ℤ) Internal.SnakyRows012B.named_envelope_607_61_head
theorem Internal.SnakyRows012B.named_envelope_607_60_last : (named_envelope_607_60.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1665 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_61 Internal.SnakyRows012B.named_envelope_607_62 (1665 : ℤ) Internal.SnakyRows012B.named_envelope_607_62_last
def Internal.SnakyRows012B.named_envelope_607_56 : List Cell := Internal.SnakyRows012B.named_envelope_607_57 ++ Internal.SnakyRows012B.named_envelope_607_60
theorem Internal.SnakyRows012B.named_envelope_607_56_chain : (named_envelope_607_56.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_57 Internal.SnakyRows012B.named_envelope_607_60 (1405 : ℤ) (1406 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_57_chain Internal.SnakyRows012B.named_envelope_607_60_chain Internal.SnakyRows012B.named_envelope_607_57_last Internal.SnakyRows012B.named_envelope_607_60_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_56_head : (named_envelope_607_56.map Internal.SnakyRows012B.namedCellKey).head? = some (1158 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_57 Internal.SnakyRows012B.named_envelope_607_60 (1158 : ℤ) Internal.SnakyRows012B.named_envelope_607_57_head
theorem Internal.SnakyRows012B.named_envelope_607_56_last : (named_envelope_607_56.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1665 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_57 Internal.SnakyRows012B.named_envelope_607_60 (1665 : ℤ) Internal.SnakyRows012B.named_envelope_607_60_last
def Internal.SnakyRows012B.named_envelope_607_48 : List Cell := Internal.SnakyRows012B.named_envelope_607_49 ++ Internal.SnakyRows012B.named_envelope_607_56
theorem Internal.SnakyRows012B.named_envelope_607_48_chain : (named_envelope_607_48.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_49 Internal.SnakyRows012B.named_envelope_607_56 (1157 : ℤ) (1158 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_49_chain Internal.SnakyRows012B.named_envelope_607_56_chain Internal.SnakyRows012B.named_envelope_607_49_last Internal.SnakyRows012B.named_envelope_607_56_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_48_head : (named_envelope_607_48.map Internal.SnakyRows012B.namedCellKey).head? = some (896 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_49 Internal.SnakyRows012B.named_envelope_607_56 (896 : ℤ) Internal.SnakyRows012B.named_envelope_607_49_head
theorem Internal.SnakyRows012B.named_envelope_607_48_last : (named_envelope_607_48.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1665 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_49 Internal.SnakyRows012B.named_envelope_607_56 (1665 : ℤ) Internal.SnakyRows012B.named_envelope_607_56_last
def Internal.SnakyRows012B.named_envelope_607_32 : List Cell := Internal.SnakyRows012B.named_envelope_607_33 ++ Internal.SnakyRows012B.named_envelope_607_48
theorem Internal.SnakyRows012B.named_envelope_607_32_chain : (named_envelope_607_32.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_33 Internal.SnakyRows012B.named_envelope_607_48 (895 : ℤ) (896 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_33_chain Internal.SnakyRows012B.named_envelope_607_48_chain Internal.SnakyRows012B.named_envelope_607_33_last Internal.SnakyRows012B.named_envelope_607_48_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_32_head : (named_envelope_607_32.map Internal.SnakyRows012B.namedCellKey).head? = some (386 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_33 Internal.SnakyRows012B.named_envelope_607_48 (386 : ℤ) Internal.SnakyRows012B.named_envelope_607_33_head
theorem Internal.SnakyRows012B.named_envelope_607_32_last : (named_envelope_607_32.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1665 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_33 Internal.SnakyRows012B.named_envelope_607_48 (1665 : ℤ) Internal.SnakyRows012B.named_envelope_607_48_last
def Internal.SnakyRows012B.named_envelope_607_0 : List Cell := Internal.SnakyRows012B.named_envelope_607_1 ++ Internal.SnakyRows012B.named_envelope_607_32
theorem Internal.SnakyRows012B.named_envelope_607_0_chain : (named_envelope_607_0.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012B.named_chain_append Internal.SnakyRows012B.named_envelope_607_1 Internal.SnakyRows012B.named_envelope_607_32 (385 : ℤ) (386 : ℤ)
    Internal.SnakyRows012B.named_envelope_607_1_chain Internal.SnakyRows012B.named_envelope_607_32_chain Internal.SnakyRows012B.named_envelope_607_1_last Internal.SnakyRows012B.named_envelope_607_32_head (by decide)
theorem Internal.SnakyRows012B.named_envelope_607_0_head : (named_envelope_607_0.map Internal.SnakyRows012B.namedCellKey).head? = some (-897 : ℤ) :=
  Internal.SnakyRows012B.named_head_append Internal.SnakyRows012B.named_envelope_607_1 Internal.SnakyRows012B.named_envelope_607_32 (-897 : ℤ) Internal.SnakyRows012B.named_envelope_607_1_head
theorem Internal.SnakyRows012B.named_envelope_607_0_last : (named_envelope_607_0.map Internal.SnakyRows012B.namedCellKey).getLast? = some (1665 : ℤ) :=
  Internal.SnakyRows012B.named_last_append Internal.SnakyRows012B.named_envelope_607_1 Internal.SnakyRows012B.named_envelope_607_32 (1665 : ℤ) Internal.SnakyRows012B.named_envelope_607_32_last
theorem Internal.SnakyRows012B.named_envelope_607_nodup : (Internal.SnakyRows012B.named_envelope_607_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows012B.named_nodup_of_chain Internal.SnakyRows012B.named_envelope_607_0 Internal.SnakyRows012B.named_envelope_607_0_chain
def envelope_607 : Finset Cell := ⟨(Internal.SnakyRows012B.named_envelope_607_0 : Multiset Cell), Internal.SnakyRows012B.named_envelope_607_nodup⟩
def childrenC_607 : Fin 5 → Finset Cell := ![(placedSet 3 (-3, -2) required_420), (placedSet 3 (-3, 0) required_419), (placedSet 0 (1, 1) required_589), (placedSet 0 (-1, 0) required_314), (placedSet 1 (3, -1) required_571)]
def childrenD_607 : Fin 5 → Finset Cell := ![(placedSet 3 (-3, -2) envelope_420), (placedSet 3 (-3, 0) envelope_419), (placedSet 0 (1, 1) envelope_589), (placedSet 0 (-1, 0) envelope_314), (placedSet 1 (3, -1) envelope_571)]
theorem common_sub_607 : commonEnvelope childrenD_607 ⊆ insert (0, 0) required_607 := by decide
theorem child_required_sub_607 : ∀ j, childrenC_607 j ⊆ insert (0, 0) required_607 := by decide
theorem Internal.SnakyRows012B.containment_607_0 :
    placedSet 3 (-3, -2) envelope_420 ⊆ envelope_607 := by decide
theorem Internal.SnakyRows012B.containment_607_1 :
    placedSet 3 (-3, 0) envelope_419 ⊆ envelope_607 := by decide
theorem Internal.SnakyRows012B.containment_607_2 :
    placedSet 0 (1, 1) envelope_589 ⊆ envelope_607 := by decide +kernel
theorem Internal.SnakyRows012B.containment_607_3 :
    placedSet 0 (-1, 0) envelope_314 ⊆ envelope_607 := by decide
theorem Internal.SnakyRows012B.containment_607_4 :
    placedSet 1 (3, -1) envelope_571 ⊆ envelope_607 := by decide +kernel
theorem child_envelope_sub_607 : ∀ j, childrenD_607 j ⊆ envelope_607 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows012B.containment_607_0
  · exact Internal.SnakyRows012B.containment_607_1
  · exact Internal.SnakyRows012B.containment_607_2
  · exact Internal.SnakyRows012B.containment_607_3
  · exact Internal.SnakyRows012B.containment_607_4
theorem pivot_mem_607 : (0, 0) ∈ envelope_607 := by decide
theorem children_work_607 : ∀ j, Template HasSnaky 28 (childrenC_607 j) (childrenD_607 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_420 3 (-3, -2)).mono (by decide)
  · exact (placed_template_map row_works_419 3 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_589 0 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_314 0 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_571 1 (3, -1)).mono (by decide)
theorem row_works_607 : Template HasSnaky 29 required_607 envelope_607 := by
  refine compose HasSnaky 28 childrenC_607 childrenD_607 children_work_607 (0, 0)
    required_607 envelope_607 pivot_mem_607 child_required_sub_607 child_envelope_sub_607 ?_
  intro b hb; exact common_sub_607 (mem_commonEnvelope childrenD_607 b hb)
def required_611 : Finset Cell := ⟨(([(-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows013.named_envelope_611_5 : List Cell := ([(-16, 0), (-16, 2), (-15, 0), (-15, 1), (-15, 2), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_5_chain : (named_envelope_611_5.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_5_head : (named_envelope_611_5.map Internal.SnakyRows013.namedCellKey).head? = some (-2048 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_5_last : (named_envelope_611_5.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1790 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_6 : List Cell := ([(-14, 4), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_6_chain : (named_envelope_611_6.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_6_head : (named_envelope_611_6.map Internal.SnakyRows013.namedCellKey).head? = some (-1788 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_6_last : (named_envelope_611_6.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1539 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_4 : List Cell := Internal.SnakyRows013.named_envelope_611_5 ++ Internal.SnakyRows013.named_envelope_611_6
theorem Internal.SnakyRows013.named_envelope_611_4_chain : (named_envelope_611_4.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_5 Internal.SnakyRows013.named_envelope_611_6 (-1790 : ℤ) (-1788 : ℤ)
    Internal.SnakyRows013.named_envelope_611_5_chain Internal.SnakyRows013.named_envelope_611_6_chain Internal.SnakyRows013.named_envelope_611_5_last Internal.SnakyRows013.named_envelope_611_6_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_4_head : (named_envelope_611_4.map Internal.SnakyRows013.namedCellKey).head? = some (-2048 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_5 Internal.SnakyRows013.named_envelope_611_6 (-2048 : ℤ) Internal.SnakyRows013.named_envelope_611_5_head
theorem Internal.SnakyRows013.named_envelope_611_4_last : (named_envelope_611_4.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1539 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_5 Internal.SnakyRows013.named_envelope_611_6 (-1539 : ℤ) Internal.SnakyRows013.named_envelope_611_6_last
def Internal.SnakyRows013.named_envelope_611_8 : List Cell := ([(-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_8_chain : (named_envelope_611_8.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_8_head : (named_envelope_611_8.map Internal.SnakyRows013.namedCellKey).head? = some (-1538 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_8_last : (named_envelope_611_8.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1410 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_9 : List Cell := ([(-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_9_chain : (named_envelope_611_9.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_9_head : (named_envelope_611_9.map Internal.SnakyRows013.namedCellKey).head? = some (-1409 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_9_last : (named_envelope_611_9.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1284 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_7 : List Cell := Internal.SnakyRows013.named_envelope_611_8 ++ Internal.SnakyRows013.named_envelope_611_9
theorem Internal.SnakyRows013.named_envelope_611_7_chain : (named_envelope_611_7.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_8 Internal.SnakyRows013.named_envelope_611_9 (-1410 : ℤ) (-1409 : ℤ)
    Internal.SnakyRows013.named_envelope_611_8_chain Internal.SnakyRows013.named_envelope_611_9_chain Internal.SnakyRows013.named_envelope_611_8_last Internal.SnakyRows013.named_envelope_611_9_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_7_head : (named_envelope_611_7.map Internal.SnakyRows013.namedCellKey).head? = some (-1538 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_8 Internal.SnakyRows013.named_envelope_611_9 (-1538 : ℤ) Internal.SnakyRows013.named_envelope_611_8_head
theorem Internal.SnakyRows013.named_envelope_611_7_last : (named_envelope_611_7.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1284 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_8 Internal.SnakyRows013.named_envelope_611_9 (-1284 : ℤ) Internal.SnakyRows013.named_envelope_611_9_last
def Internal.SnakyRows013.named_envelope_611_3 : List Cell := Internal.SnakyRows013.named_envelope_611_4 ++ Internal.SnakyRows013.named_envelope_611_7
theorem Internal.SnakyRows013.named_envelope_611_3_chain : (named_envelope_611_3.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_4 Internal.SnakyRows013.named_envelope_611_7 (-1539 : ℤ) (-1538 : ℤ)
    Internal.SnakyRows013.named_envelope_611_4_chain Internal.SnakyRows013.named_envelope_611_7_chain Internal.SnakyRows013.named_envelope_611_4_last Internal.SnakyRows013.named_envelope_611_7_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_3_head : (named_envelope_611_3.map Internal.SnakyRows013.namedCellKey).head? = some (-2048 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_4 Internal.SnakyRows013.named_envelope_611_7 (-2048 : ℤ) Internal.SnakyRows013.named_envelope_611_4_head
theorem Internal.SnakyRows013.named_envelope_611_3_last : (named_envelope_611_3.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1284 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_4 Internal.SnakyRows013.named_envelope_611_7 (-1284 : ℤ) Internal.SnakyRows013.named_envelope_611_7_last
def Internal.SnakyRows013.named_envelope_611_12 : List Cell := ([(-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-9, -10), (-9, -9), (-9, -8)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_12_chain : (named_envelope_611_12.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_12_head : (named_envelope_611_12.map Internal.SnakyRows013.namedCellKey).head? = some (-1283 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_12_last : (named_envelope_611_12.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1160 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_13 : List Cell := ([(-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_13_chain : (named_envelope_611_13.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_13_head : (named_envelope_611_13.map Internal.SnakyRows013.namedCellKey).head? = some (-1159 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_13_last : (named_envelope_611_13.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1147 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_11 : List Cell := Internal.SnakyRows013.named_envelope_611_12 ++ Internal.SnakyRows013.named_envelope_611_13
theorem Internal.SnakyRows013.named_envelope_611_11_chain : (named_envelope_611_11.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_12 Internal.SnakyRows013.named_envelope_611_13 (-1160 : ℤ) (-1159 : ℤ)
    Internal.SnakyRows013.named_envelope_611_12_chain Internal.SnakyRows013.named_envelope_611_13_chain Internal.SnakyRows013.named_envelope_611_12_last Internal.SnakyRows013.named_envelope_611_13_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_11_head : (named_envelope_611_11.map Internal.SnakyRows013.namedCellKey).head? = some (-1283 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_12 Internal.SnakyRows013.named_envelope_611_13 (-1283 : ℤ) Internal.SnakyRows013.named_envelope_611_12_head
theorem Internal.SnakyRows013.named_envelope_611_11_last : (named_envelope_611_11.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1147 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_12 Internal.SnakyRows013.named_envelope_611_13 (-1147 : ℤ) Internal.SnakyRows013.named_envelope_611_13_last
def Internal.SnakyRows013.named_envelope_611_15 : List Cell := ([(-9, 6), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_15_chain : (named_envelope_611_15.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_15_head : (named_envelope_611_15.map Internal.SnakyRows013.namedCellKey).head? = some (-1146 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_15_last : (named_envelope_611_15.map Internal.SnakyRows013.namedCellKey).getLast? = some (-1023 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_16 : List Cell := ([(-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_16_chain : (named_envelope_611_16.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_16_head : (named_envelope_611_16.map Internal.SnakyRows013.namedCellKey).head? = some (-1022 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_16_last : (named_envelope_611_16.map Internal.SnakyRows013.namedCellKey).getLast? = some (-899 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_14 : List Cell := Internal.SnakyRows013.named_envelope_611_15 ++ Internal.SnakyRows013.named_envelope_611_16
theorem Internal.SnakyRows013.named_envelope_611_14_chain : (named_envelope_611_14.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_15 Internal.SnakyRows013.named_envelope_611_16 (-1023 : ℤ) (-1022 : ℤ)
    Internal.SnakyRows013.named_envelope_611_15_chain Internal.SnakyRows013.named_envelope_611_16_chain Internal.SnakyRows013.named_envelope_611_15_last Internal.SnakyRows013.named_envelope_611_16_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_14_head : (named_envelope_611_14.map Internal.SnakyRows013.namedCellKey).head? = some (-1146 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_15 Internal.SnakyRows013.named_envelope_611_16 (-1146 : ℤ) Internal.SnakyRows013.named_envelope_611_15_head
theorem Internal.SnakyRows013.named_envelope_611_14_last : (named_envelope_611_14.map Internal.SnakyRows013.namedCellKey).getLast? = some (-899 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_15 Internal.SnakyRows013.named_envelope_611_16 (-899 : ℤ) Internal.SnakyRows013.named_envelope_611_16_last
def Internal.SnakyRows013.named_envelope_611_10 : List Cell := Internal.SnakyRows013.named_envelope_611_11 ++ Internal.SnakyRows013.named_envelope_611_14
theorem Internal.SnakyRows013.named_envelope_611_10_chain : (named_envelope_611_10.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_11 Internal.SnakyRows013.named_envelope_611_14 (-1147 : ℤ) (-1146 : ℤ)
    Internal.SnakyRows013.named_envelope_611_11_chain Internal.SnakyRows013.named_envelope_611_14_chain Internal.SnakyRows013.named_envelope_611_11_last Internal.SnakyRows013.named_envelope_611_14_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_10_head : (named_envelope_611_10.map Internal.SnakyRows013.namedCellKey).head? = some (-1283 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_11 Internal.SnakyRows013.named_envelope_611_14 (-1283 : ℤ) Internal.SnakyRows013.named_envelope_611_11_head
theorem Internal.SnakyRows013.named_envelope_611_10_last : (named_envelope_611_10.map Internal.SnakyRows013.namedCellKey).getLast? = some (-899 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_11 Internal.SnakyRows013.named_envelope_611_14 (-899 : ℤ) Internal.SnakyRows013.named_envelope_611_14_last
def Internal.SnakyRows013.named_envelope_611_2 : List Cell := Internal.SnakyRows013.named_envelope_611_3 ++ Internal.SnakyRows013.named_envelope_611_10
theorem Internal.SnakyRows013.named_envelope_611_2_chain : (named_envelope_611_2.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_3 Internal.SnakyRows013.named_envelope_611_10 (-1284 : ℤ) (-1283 : ℤ)
    Internal.SnakyRows013.named_envelope_611_3_chain Internal.SnakyRows013.named_envelope_611_10_chain Internal.SnakyRows013.named_envelope_611_3_last Internal.SnakyRows013.named_envelope_611_10_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_2_head : (named_envelope_611_2.map Internal.SnakyRows013.namedCellKey).head? = some (-2048 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_3 Internal.SnakyRows013.named_envelope_611_10 (-2048 : ℤ) Internal.SnakyRows013.named_envelope_611_3_head
theorem Internal.SnakyRows013.named_envelope_611_2_last : (named_envelope_611_2.map Internal.SnakyRows013.namedCellKey).getLast? = some (-899 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_3 Internal.SnakyRows013.named_envelope_611_10 (-899 : ℤ) Internal.SnakyRows013.named_envelope_611_10_last
def Internal.SnakyRows013.named_envelope_611_20 : List Cell := ([(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_20_chain : (named_envelope_611_20.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_20_head : (named_envelope_611_20.map Internal.SnakyRows013.namedCellKey).head? = some (-898 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_20_last : (named_envelope_611_20.map Internal.SnakyRows013.namedCellKey).getLast? = some (-774 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_21 : List Cell := ([(-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -12), (-5, -11)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_21_chain : (named_envelope_611_21.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_21_head : (named_envelope_611_21.map Internal.SnakyRows013.namedCellKey).head? = some (-773 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_21_last : (named_envelope_611_21.map Internal.SnakyRows013.namedCellKey).getLast? = some (-651 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_19 : List Cell := Internal.SnakyRows013.named_envelope_611_20 ++ Internal.SnakyRows013.named_envelope_611_21
theorem Internal.SnakyRows013.named_envelope_611_19_chain : (named_envelope_611_19.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_20 Internal.SnakyRows013.named_envelope_611_21 (-774 : ℤ) (-773 : ℤ)
    Internal.SnakyRows013.named_envelope_611_20_chain Internal.SnakyRows013.named_envelope_611_21_chain Internal.SnakyRows013.named_envelope_611_20_last Internal.SnakyRows013.named_envelope_611_21_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_19_head : (named_envelope_611_19.map Internal.SnakyRows013.namedCellKey).head? = some (-898 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_20 Internal.SnakyRows013.named_envelope_611_21 (-898 : ℤ) Internal.SnakyRows013.named_envelope_611_20_head
theorem Internal.SnakyRows013.named_envelope_611_19_last : (named_envelope_611_19.map Internal.SnakyRows013.namedCellKey).getLast? = some (-651 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_20 Internal.SnakyRows013.named_envelope_611_21 (-651 : ℤ) Internal.SnakyRows013.named_envelope_611_21_last
def Internal.SnakyRows013.named_envelope_611_23 : List Cell := ([(-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_23_chain : (named_envelope_611_23.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_23_head : (named_envelope_611_23.map Internal.SnakyRows013.namedCellKey).head? = some (-650 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_23_last : (named_envelope_611_23.map Internal.SnakyRows013.namedCellKey).getLast? = some (-638 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_24 : List Cell := ([(-5, 3), (-5, 4), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_24_chain : (named_envelope_611_24.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_24_head : (named_envelope_611_24.map Internal.SnakyRows013.namedCellKey).head? = some (-637 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_24_last : (named_envelope_611_24.map Internal.SnakyRows013.namedCellKey).getLast? = some (-513 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_22 : List Cell := Internal.SnakyRows013.named_envelope_611_23 ++ Internal.SnakyRows013.named_envelope_611_24
theorem Internal.SnakyRows013.named_envelope_611_22_chain : (named_envelope_611_22.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_23 Internal.SnakyRows013.named_envelope_611_24 (-638 : ℤ) (-637 : ℤ)
    Internal.SnakyRows013.named_envelope_611_23_chain Internal.SnakyRows013.named_envelope_611_24_chain Internal.SnakyRows013.named_envelope_611_23_last Internal.SnakyRows013.named_envelope_611_24_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_22_head : (named_envelope_611_22.map Internal.SnakyRows013.namedCellKey).head? = some (-650 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_23 Internal.SnakyRows013.named_envelope_611_24 (-650 : ℤ) Internal.SnakyRows013.named_envelope_611_23_head
theorem Internal.SnakyRows013.named_envelope_611_22_last : (named_envelope_611_22.map Internal.SnakyRows013.namedCellKey).getLast? = some (-513 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_23 Internal.SnakyRows013.named_envelope_611_24 (-513 : ℤ) Internal.SnakyRows013.named_envelope_611_24_last
def Internal.SnakyRows013.named_envelope_611_18 : List Cell := Internal.SnakyRows013.named_envelope_611_19 ++ Internal.SnakyRows013.named_envelope_611_22
theorem Internal.SnakyRows013.named_envelope_611_18_chain : (named_envelope_611_18.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_19 Internal.SnakyRows013.named_envelope_611_22 (-651 : ℤ) (-650 : ℤ)
    Internal.SnakyRows013.named_envelope_611_19_chain Internal.SnakyRows013.named_envelope_611_22_chain Internal.SnakyRows013.named_envelope_611_19_last Internal.SnakyRows013.named_envelope_611_22_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_18_head : (named_envelope_611_18.map Internal.SnakyRows013.namedCellKey).head? = some (-898 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_19 Internal.SnakyRows013.named_envelope_611_22 (-898 : ℤ) Internal.SnakyRows013.named_envelope_611_19_head
theorem Internal.SnakyRows013.named_envelope_611_18_last : (named_envelope_611_18.map Internal.SnakyRows013.namedCellKey).getLast? = some (-513 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_19 Internal.SnakyRows013.named_envelope_611_22 (-513 : ℤ) Internal.SnakyRows013.named_envelope_611_22_last
def Internal.SnakyRows013.named_envelope_611_27 : List Cell := ([(-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_27_chain : (named_envelope_611_27.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_27_head : (named_envelope_611_27.map Internal.SnakyRows013.namedCellKey).head? = some (-512 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_27_last : (named_envelope_611_27.map Internal.SnakyRows013.namedCellKey).getLast? = some (-390 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_28 : List Cell := ([(-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_28_chain : (named_envelope_611_28.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_28_head : (named_envelope_611_28.map Internal.SnakyRows013.namedCellKey).head? = some (-389 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_28_last : (named_envelope_611_28.map Internal.SnakyRows013.namedCellKey).getLast? = some (-377 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_26 : List Cell := Internal.SnakyRows013.named_envelope_611_27 ++ Internal.SnakyRows013.named_envelope_611_28
theorem Internal.SnakyRows013.named_envelope_611_26_chain : (named_envelope_611_26.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_27 Internal.SnakyRows013.named_envelope_611_28 (-390 : ℤ) (-389 : ℤ)
    Internal.SnakyRows013.named_envelope_611_27_chain Internal.SnakyRows013.named_envelope_611_28_chain Internal.SnakyRows013.named_envelope_611_27_last Internal.SnakyRows013.named_envelope_611_28_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_26_head : (named_envelope_611_26.map Internal.SnakyRows013.namedCellKey).head? = some (-512 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_27 Internal.SnakyRows013.named_envelope_611_28 (-512 : ℤ) Internal.SnakyRows013.named_envelope_611_27_head
theorem Internal.SnakyRows013.named_envelope_611_26_last : (named_envelope_611_26.map Internal.SnakyRows013.namedCellKey).getLast? = some (-377 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_27 Internal.SnakyRows013.named_envelope_611_28 (-377 : ℤ) Internal.SnakyRows013.named_envelope_611_28_last
def Internal.SnakyRows013.named_envelope_611_30 : List Cell := ([(-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_30_chain : (named_envelope_611_30.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_30_head : (named_envelope_611_30.map Internal.SnakyRows013.namedCellKey).head? = some (-265 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_30_last : (named_envelope_611_30.map Internal.SnakyRows013.namedCellKey).getLast? = some (-252 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_31 : List Cell := ([(-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_31_chain : (named_envelope_611_31.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_31_head : (named_envelope_611_31.map Internal.SnakyRows013.namedCellKey).head? = some (-251 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_31_last : (named_envelope_611_31.map Internal.SnakyRows013.namedCellKey).getLast? = some (-129 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_29 : List Cell := Internal.SnakyRows013.named_envelope_611_30 ++ Internal.SnakyRows013.named_envelope_611_31
theorem Internal.SnakyRows013.named_envelope_611_29_chain : (named_envelope_611_29.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_30 Internal.SnakyRows013.named_envelope_611_31 (-252 : ℤ) (-251 : ℤ)
    Internal.SnakyRows013.named_envelope_611_30_chain Internal.SnakyRows013.named_envelope_611_31_chain Internal.SnakyRows013.named_envelope_611_30_last Internal.SnakyRows013.named_envelope_611_31_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_29_head : (named_envelope_611_29.map Internal.SnakyRows013.namedCellKey).head? = some (-265 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_30 Internal.SnakyRows013.named_envelope_611_31 (-265 : ℤ) Internal.SnakyRows013.named_envelope_611_30_head
theorem Internal.SnakyRows013.named_envelope_611_29_last : (named_envelope_611_29.map Internal.SnakyRows013.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_30 Internal.SnakyRows013.named_envelope_611_31 (-129 : ℤ) Internal.SnakyRows013.named_envelope_611_31_last
def Internal.SnakyRows013.named_envelope_611_25 : List Cell := Internal.SnakyRows013.named_envelope_611_26 ++ Internal.SnakyRows013.named_envelope_611_29
theorem Internal.SnakyRows013.named_envelope_611_25_chain : (named_envelope_611_25.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_26 Internal.SnakyRows013.named_envelope_611_29 (-377 : ℤ) (-265 : ℤ)
    Internal.SnakyRows013.named_envelope_611_26_chain Internal.SnakyRows013.named_envelope_611_29_chain Internal.SnakyRows013.named_envelope_611_26_last Internal.SnakyRows013.named_envelope_611_29_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_25_head : (named_envelope_611_25.map Internal.SnakyRows013.namedCellKey).head? = some (-512 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_26 Internal.SnakyRows013.named_envelope_611_29 (-512 : ℤ) Internal.SnakyRows013.named_envelope_611_26_head
theorem Internal.SnakyRows013.named_envelope_611_25_last : (named_envelope_611_25.map Internal.SnakyRows013.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_26 Internal.SnakyRows013.named_envelope_611_29 (-129 : ℤ) Internal.SnakyRows013.named_envelope_611_29_last
def Internal.SnakyRows013.named_envelope_611_17 : List Cell := Internal.SnakyRows013.named_envelope_611_18 ++ Internal.SnakyRows013.named_envelope_611_25
theorem Internal.SnakyRows013.named_envelope_611_17_chain : (named_envelope_611_17.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_18 Internal.SnakyRows013.named_envelope_611_25 (-513 : ℤ) (-512 : ℤ)
    Internal.SnakyRows013.named_envelope_611_18_chain Internal.SnakyRows013.named_envelope_611_25_chain Internal.SnakyRows013.named_envelope_611_18_last Internal.SnakyRows013.named_envelope_611_25_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_17_head : (named_envelope_611_17.map Internal.SnakyRows013.namedCellKey).head? = some (-898 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_18 Internal.SnakyRows013.named_envelope_611_25 (-898 : ℤ) Internal.SnakyRows013.named_envelope_611_18_head
theorem Internal.SnakyRows013.named_envelope_611_17_last : (named_envelope_611_17.map Internal.SnakyRows013.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_18 Internal.SnakyRows013.named_envelope_611_25 (-129 : ℤ) Internal.SnakyRows013.named_envelope_611_25_last
def Internal.SnakyRows013.named_envelope_611_1 : List Cell := Internal.SnakyRows013.named_envelope_611_2 ++ Internal.SnakyRows013.named_envelope_611_17
theorem Internal.SnakyRows013.named_envelope_611_1_chain : (named_envelope_611_1.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_2 Internal.SnakyRows013.named_envelope_611_17 (-899 : ℤ) (-898 : ℤ)
    Internal.SnakyRows013.named_envelope_611_2_chain Internal.SnakyRows013.named_envelope_611_17_chain Internal.SnakyRows013.named_envelope_611_2_last Internal.SnakyRows013.named_envelope_611_17_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_1_head : (named_envelope_611_1.map Internal.SnakyRows013.namedCellKey).head? = some (-2048 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_2 Internal.SnakyRows013.named_envelope_611_17 (-2048 : ℤ) Internal.SnakyRows013.named_envelope_611_2_head
theorem Internal.SnakyRows013.named_envelope_611_1_last : (named_envelope_611_1.map Internal.SnakyRows013.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_2 Internal.SnakyRows013.named_envelope_611_17 (-129 : ℤ) Internal.SnakyRows013.named_envelope_611_17_last
def Internal.SnakyRows013.named_envelope_611_36 : List Cell := ([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -9), (0, -8), (0, -7)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_36_chain : (named_envelope_611_36.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_36_head : (named_envelope_611_36.map Internal.SnakyRows013.namedCellKey).head? = some (-128 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_36_last : (named_envelope_611_36.map Internal.SnakyRows013.namedCellKey).getLast? = some (-7 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_37 : List Cell := ([(0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_37_chain : (named_envelope_611_37.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_37_head : (named_envelope_611_37.map Internal.SnakyRows013.namedCellKey).head? = some (-6 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_37_last : (named_envelope_611_37.map Internal.SnakyRows013.namedCellKey).getLast? = some (7 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_35 : List Cell := Internal.SnakyRows013.named_envelope_611_36 ++ Internal.SnakyRows013.named_envelope_611_37
theorem Internal.SnakyRows013.named_envelope_611_35_chain : (named_envelope_611_35.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_36 Internal.SnakyRows013.named_envelope_611_37 (-7 : ℤ) (-6 : ℤ)
    Internal.SnakyRows013.named_envelope_611_36_chain Internal.SnakyRows013.named_envelope_611_37_chain Internal.SnakyRows013.named_envelope_611_36_last Internal.SnakyRows013.named_envelope_611_37_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_35_head : (named_envelope_611_35.map Internal.SnakyRows013.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_36 Internal.SnakyRows013.named_envelope_611_37 (-128 : ℤ) Internal.SnakyRows013.named_envelope_611_36_head
theorem Internal.SnakyRows013.named_envelope_611_35_last : (named_envelope_611_35.map Internal.SnakyRows013.namedCellKey).getLast? = some (7 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_36 Internal.SnakyRows013.named_envelope_611_37 (7 : ℤ) Internal.SnakyRows013.named_envelope_611_37_last
def Internal.SnakyRows013.named_envelope_611_39 : List Cell := ([(0, 8), (0, 9), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_39_chain : (named_envelope_611_39.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_39_head : (named_envelope_611_39.map Internal.SnakyRows013.namedCellKey).head? = some (8 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_39_last : (named_envelope_611_39.map Internal.SnakyRows013.namedCellKey).getLast? = some (131 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_40 : List Cell := ([(1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_40_chain : (named_envelope_611_40.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_40_head : (named_envelope_611_40.map Internal.SnakyRows013.namedCellKey).head? = some (132 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_40_last : (named_envelope_611_40.map Internal.SnakyRows013.namedCellKey).getLast? = some (254 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_38 : List Cell := Internal.SnakyRows013.named_envelope_611_39 ++ Internal.SnakyRows013.named_envelope_611_40
theorem Internal.SnakyRows013.named_envelope_611_38_chain : (named_envelope_611_38.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_39 Internal.SnakyRows013.named_envelope_611_40 (131 : ℤ) (132 : ℤ)
    Internal.SnakyRows013.named_envelope_611_39_chain Internal.SnakyRows013.named_envelope_611_40_chain Internal.SnakyRows013.named_envelope_611_39_last Internal.SnakyRows013.named_envelope_611_40_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_38_head : (named_envelope_611_38.map Internal.SnakyRows013.namedCellKey).head? = some (8 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_39 Internal.SnakyRows013.named_envelope_611_40 (8 : ℤ) Internal.SnakyRows013.named_envelope_611_39_head
theorem Internal.SnakyRows013.named_envelope_611_38_last : (named_envelope_611_38.map Internal.SnakyRows013.namedCellKey).getLast? = some (254 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_39 Internal.SnakyRows013.named_envelope_611_40 (254 : ℤ) Internal.SnakyRows013.named_envelope_611_40_last
def Internal.SnakyRows013.named_envelope_611_34 : List Cell := Internal.SnakyRows013.named_envelope_611_35 ++ Internal.SnakyRows013.named_envelope_611_38
theorem Internal.SnakyRows013.named_envelope_611_34_chain : (named_envelope_611_34.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_35 Internal.SnakyRows013.named_envelope_611_38 (7 : ℤ) (8 : ℤ)
    Internal.SnakyRows013.named_envelope_611_35_chain Internal.SnakyRows013.named_envelope_611_38_chain Internal.SnakyRows013.named_envelope_611_35_last Internal.SnakyRows013.named_envelope_611_38_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_34_head : (named_envelope_611_34.map Internal.SnakyRows013.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_35 Internal.SnakyRows013.named_envelope_611_38 (-128 : ℤ) Internal.SnakyRows013.named_envelope_611_35_head
theorem Internal.SnakyRows013.named_envelope_611_34_last : (named_envelope_611_34.map Internal.SnakyRows013.namedCellKey).getLast? = some (254 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_35 Internal.SnakyRows013.named_envelope_611_38 (254 : ℤ) Internal.SnakyRows013.named_envelope_611_38_last
def Internal.SnakyRows013.named_envelope_611_43 : List Cell := ([(2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_43_chain : (named_envelope_611_43.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_43_head : (named_envelope_611_43.map Internal.SnakyRows013.namedCellKey).head? = some (255 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_43_last : (named_envelope_611_43.map Internal.SnakyRows013.namedCellKey).getLast? = some (267 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_44 : List Cell := ([(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_44_chain : (named_envelope_611_44.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_44_head : (named_envelope_611_44.map Internal.SnakyRows013.namedCellKey).head? = some (380 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_44_last : (named_envelope_611_44.map Internal.SnakyRows013.namedCellKey).getLast? = some (392 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_42 : List Cell := Internal.SnakyRows013.named_envelope_611_43 ++ Internal.SnakyRows013.named_envelope_611_44
theorem Internal.SnakyRows013.named_envelope_611_42_chain : (named_envelope_611_42.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_43 Internal.SnakyRows013.named_envelope_611_44 (267 : ℤ) (380 : ℤ)
    Internal.SnakyRows013.named_envelope_611_43_chain Internal.SnakyRows013.named_envelope_611_44_chain Internal.SnakyRows013.named_envelope_611_43_last Internal.SnakyRows013.named_envelope_611_44_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_42_head : (named_envelope_611_42.map Internal.SnakyRows013.namedCellKey).head? = some (255 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_43 Internal.SnakyRows013.named_envelope_611_44 (255 : ℤ) Internal.SnakyRows013.named_envelope_611_43_head
theorem Internal.SnakyRows013.named_envelope_611_42_last : (named_envelope_611_42.map Internal.SnakyRows013.namedCellKey).getLast? = some (392 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_43 Internal.SnakyRows013.named_envelope_611_44 (392 : ℤ) Internal.SnakyRows013.named_envelope_611_44_last
def Internal.SnakyRows013.named_envelope_611_46 : List Cell := ([(3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_46_chain : (named_envelope_611_46.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_46_head : (named_envelope_611_46.map Internal.SnakyRows013.namedCellKey).head? = some (393 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_46_last : (named_envelope_611_46.map Internal.SnakyRows013.namedCellKey).getLast? = some (515 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_47 : List Cell := ([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_47_chain : (named_envelope_611_47.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_47_head : (named_envelope_611_47.map Internal.SnakyRows013.namedCellKey).head? = some (516 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_47_last : (named_envelope_611_47.map Internal.SnakyRows013.namedCellKey).getLast? = some (641 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_45 : List Cell := Internal.SnakyRows013.named_envelope_611_46 ++ Internal.SnakyRows013.named_envelope_611_47
theorem Internal.SnakyRows013.named_envelope_611_45_chain : (named_envelope_611_45.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_46 Internal.SnakyRows013.named_envelope_611_47 (515 : ℤ) (516 : ℤ)
    Internal.SnakyRows013.named_envelope_611_46_chain Internal.SnakyRows013.named_envelope_611_47_chain Internal.SnakyRows013.named_envelope_611_46_last Internal.SnakyRows013.named_envelope_611_47_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_45_head : (named_envelope_611_45.map Internal.SnakyRows013.namedCellKey).head? = some (393 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_46 Internal.SnakyRows013.named_envelope_611_47 (393 : ℤ) Internal.SnakyRows013.named_envelope_611_46_head
theorem Internal.SnakyRows013.named_envelope_611_45_last : (named_envelope_611_45.map Internal.SnakyRows013.namedCellKey).getLast? = some (641 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_46 Internal.SnakyRows013.named_envelope_611_47 (641 : ℤ) Internal.SnakyRows013.named_envelope_611_47_last
def Internal.SnakyRows013.named_envelope_611_41 : List Cell := Internal.SnakyRows013.named_envelope_611_42 ++ Internal.SnakyRows013.named_envelope_611_45
theorem Internal.SnakyRows013.named_envelope_611_41_chain : (named_envelope_611_41.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_42 Internal.SnakyRows013.named_envelope_611_45 (392 : ℤ) (393 : ℤ)
    Internal.SnakyRows013.named_envelope_611_42_chain Internal.SnakyRows013.named_envelope_611_45_chain Internal.SnakyRows013.named_envelope_611_42_last Internal.SnakyRows013.named_envelope_611_45_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_41_head : (named_envelope_611_41.map Internal.SnakyRows013.namedCellKey).head? = some (255 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_42 Internal.SnakyRows013.named_envelope_611_45 (255 : ℤ) Internal.SnakyRows013.named_envelope_611_42_head
theorem Internal.SnakyRows013.named_envelope_611_41_last : (named_envelope_611_41.map Internal.SnakyRows013.namedCellKey).getLast? = some (641 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_42 Internal.SnakyRows013.named_envelope_611_45 (641 : ℤ) Internal.SnakyRows013.named_envelope_611_45_last
def Internal.SnakyRows013.named_envelope_611_33 : List Cell := Internal.SnakyRows013.named_envelope_611_34 ++ Internal.SnakyRows013.named_envelope_611_41
theorem Internal.SnakyRows013.named_envelope_611_33_chain : (named_envelope_611_33.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_34 Internal.SnakyRows013.named_envelope_611_41 (254 : ℤ) (255 : ℤ)
    Internal.SnakyRows013.named_envelope_611_34_chain Internal.SnakyRows013.named_envelope_611_41_chain Internal.SnakyRows013.named_envelope_611_34_last Internal.SnakyRows013.named_envelope_611_41_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_33_head : (named_envelope_611_33.map Internal.SnakyRows013.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_34 Internal.SnakyRows013.named_envelope_611_41 (-128 : ℤ) Internal.SnakyRows013.named_envelope_611_34_head
theorem Internal.SnakyRows013.named_envelope_611_33_last : (named_envelope_611_33.map Internal.SnakyRows013.namedCellKey).getLast? = some (641 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_34 Internal.SnakyRows013.named_envelope_611_41 (641 : ℤ) Internal.SnakyRows013.named_envelope_611_41_last
def Internal.SnakyRows013.named_envelope_611_51 : List Cell := ([(5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_51_chain : (named_envelope_611_51.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_51_head : (named_envelope_611_51.map Internal.SnakyRows013.namedCellKey).head? = some (642 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_51_last : (named_envelope_611_51.map Internal.SnakyRows013.namedCellKey).getLast? = some (764 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_52 : List Cell := ([(6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_52_chain : (named_envelope_611_52.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_52_head : (named_envelope_611_52.map Internal.SnakyRows013.namedCellKey).head? = some (765 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_52_last : (named_envelope_611_52.map Internal.SnakyRows013.namedCellKey).getLast? = some (777 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_50 : List Cell := Internal.SnakyRows013.named_envelope_611_51 ++ Internal.SnakyRows013.named_envelope_611_52
theorem Internal.SnakyRows013.named_envelope_611_50_chain : (named_envelope_611_50.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_51 Internal.SnakyRows013.named_envelope_611_52 (764 : ℤ) (765 : ℤ)
    Internal.SnakyRows013.named_envelope_611_51_chain Internal.SnakyRows013.named_envelope_611_52_chain Internal.SnakyRows013.named_envelope_611_51_last Internal.SnakyRows013.named_envelope_611_52_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_50_head : (named_envelope_611_50.map Internal.SnakyRows013.namedCellKey).head? = some (642 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_51 Internal.SnakyRows013.named_envelope_611_52 (642 : ℤ) Internal.SnakyRows013.named_envelope_611_51_head
theorem Internal.SnakyRows013.named_envelope_611_50_last : (named_envelope_611_50.map Internal.SnakyRows013.namedCellKey).getLast? = some (777 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_51 Internal.SnakyRows013.named_envelope_611_52 (777 : ℤ) Internal.SnakyRows013.named_envelope_611_52_last
def Internal.SnakyRows013.named_envelope_611_54 : List Cell := ([(6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_54_chain : (named_envelope_611_54.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_54_head : (named_envelope_611_54.map Internal.SnakyRows013.namedCellKey).head? = some (778 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_54_last : (named_envelope_611_54.map Internal.SnakyRows013.namedCellKey).getLast? = some (901 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_55 : List Cell := ([(7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_55_chain : (named_envelope_611_55.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_55_head : (named_envelope_611_55.map Internal.SnakyRows013.namedCellKey).head? = some (902 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_55_last : (named_envelope_611_55.map Internal.SnakyRows013.namedCellKey).getLast? = some (1026 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_53 : List Cell := Internal.SnakyRows013.named_envelope_611_54 ++ Internal.SnakyRows013.named_envelope_611_55
theorem Internal.SnakyRows013.named_envelope_611_53_chain : (named_envelope_611_53.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_54 Internal.SnakyRows013.named_envelope_611_55 (901 : ℤ) (902 : ℤ)
    Internal.SnakyRows013.named_envelope_611_54_chain Internal.SnakyRows013.named_envelope_611_55_chain Internal.SnakyRows013.named_envelope_611_54_last Internal.SnakyRows013.named_envelope_611_55_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_53_head : (named_envelope_611_53.map Internal.SnakyRows013.namedCellKey).head? = some (778 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_54 Internal.SnakyRows013.named_envelope_611_55 (778 : ℤ) Internal.SnakyRows013.named_envelope_611_54_head
theorem Internal.SnakyRows013.named_envelope_611_53_last : (named_envelope_611_53.map Internal.SnakyRows013.namedCellKey).getLast? = some (1026 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_54 Internal.SnakyRows013.named_envelope_611_55 (1026 : ℤ) Internal.SnakyRows013.named_envelope_611_55_last
def Internal.SnakyRows013.named_envelope_611_49 : List Cell := Internal.SnakyRows013.named_envelope_611_50 ++ Internal.SnakyRows013.named_envelope_611_53
theorem Internal.SnakyRows013.named_envelope_611_49_chain : (named_envelope_611_49.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_50 Internal.SnakyRows013.named_envelope_611_53 (777 : ℤ) (778 : ℤ)
    Internal.SnakyRows013.named_envelope_611_50_chain Internal.SnakyRows013.named_envelope_611_53_chain Internal.SnakyRows013.named_envelope_611_50_last Internal.SnakyRows013.named_envelope_611_53_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_49_head : (named_envelope_611_49.map Internal.SnakyRows013.namedCellKey).head? = some (642 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_50 Internal.SnakyRows013.named_envelope_611_53 (642 : ℤ) Internal.SnakyRows013.named_envelope_611_50_head
theorem Internal.SnakyRows013.named_envelope_611_49_last : (named_envelope_611_49.map Internal.SnakyRows013.namedCellKey).getLast? = some (1026 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_50 Internal.SnakyRows013.named_envelope_611_53 (1026 : ℤ) Internal.SnakyRows013.named_envelope_611_53_last
def Internal.SnakyRows013.named_envelope_611_58 : List Cell := ([(8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_58_chain : (named_envelope_611_58.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_58_head : (named_envelope_611_58.map Internal.SnakyRows013.namedCellKey).head? = some (1027 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_58_last : (named_envelope_611_58.map Internal.SnakyRows013.namedCellKey).getLast? = some (1152 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_59 : List Cell := ([(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_59_chain : (named_envelope_611_59.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_59_head : (named_envelope_611_59.map Internal.SnakyRows013.namedCellKey).head? = some (1153 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_59_last : (named_envelope_611_59.map Internal.SnakyRows013.namedCellKey).getLast? = some (1281 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_57 : List Cell := Internal.SnakyRows013.named_envelope_611_58 ++ Internal.SnakyRows013.named_envelope_611_59
theorem Internal.SnakyRows013.named_envelope_611_57_chain : (named_envelope_611_57.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_58 Internal.SnakyRows013.named_envelope_611_59 (1152 : ℤ) (1153 : ℤ)
    Internal.SnakyRows013.named_envelope_611_58_chain Internal.SnakyRows013.named_envelope_611_59_chain Internal.SnakyRows013.named_envelope_611_58_last Internal.SnakyRows013.named_envelope_611_59_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_57_head : (named_envelope_611_57.map Internal.SnakyRows013.namedCellKey).head? = some (1027 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_58 Internal.SnakyRows013.named_envelope_611_59 (1027 : ℤ) Internal.SnakyRows013.named_envelope_611_58_head
theorem Internal.SnakyRows013.named_envelope_611_57_last : (named_envelope_611_57.map Internal.SnakyRows013.namedCellKey).getLast? = some (1281 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_58 Internal.SnakyRows013.named_envelope_611_59 (1281 : ℤ) Internal.SnakyRows013.named_envelope_611_59_last
def Internal.SnakyRows013.named_envelope_611_61 : List Cell := ([(10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_61_chain : (named_envelope_611_61.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_61_head : (named_envelope_611_61.map Internal.SnakyRows013.namedCellKey).head? = some (1282 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_61_last : (named_envelope_611_61.map Internal.SnakyRows013.namedCellKey).getLast? = some (1412 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_62 : List Cell := ([(12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)] : List Cell)
theorem Internal.SnakyRows013.named_envelope_611_62_chain : (named_envelope_611_62.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows013.named_envelope_611_62_head : (named_envelope_611_62.map Internal.SnakyRows013.namedCellKey).head? = some (1532 : ℤ) := by decide
theorem Internal.SnakyRows013.named_envelope_611_62_last : (named_envelope_611_62.map Internal.SnakyRows013.namedCellKey).getLast? = some (1792 : ℤ) := by decide
def Internal.SnakyRows013.named_envelope_611_60 : List Cell := Internal.SnakyRows013.named_envelope_611_61 ++ Internal.SnakyRows013.named_envelope_611_62
theorem Internal.SnakyRows013.named_envelope_611_60_chain : (named_envelope_611_60.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_61 Internal.SnakyRows013.named_envelope_611_62 (1412 : ℤ) (1532 : ℤ)
    Internal.SnakyRows013.named_envelope_611_61_chain Internal.SnakyRows013.named_envelope_611_62_chain Internal.SnakyRows013.named_envelope_611_61_last Internal.SnakyRows013.named_envelope_611_62_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_60_head : (named_envelope_611_60.map Internal.SnakyRows013.namedCellKey).head? = some (1282 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_61 Internal.SnakyRows013.named_envelope_611_62 (1282 : ℤ) Internal.SnakyRows013.named_envelope_611_61_head
theorem Internal.SnakyRows013.named_envelope_611_60_last : (named_envelope_611_60.map Internal.SnakyRows013.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_61 Internal.SnakyRows013.named_envelope_611_62 (1792 : ℤ) Internal.SnakyRows013.named_envelope_611_62_last
def Internal.SnakyRows013.named_envelope_611_56 : List Cell := Internal.SnakyRows013.named_envelope_611_57 ++ Internal.SnakyRows013.named_envelope_611_60
theorem Internal.SnakyRows013.named_envelope_611_56_chain : (named_envelope_611_56.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_57 Internal.SnakyRows013.named_envelope_611_60 (1281 : ℤ) (1282 : ℤ)
    Internal.SnakyRows013.named_envelope_611_57_chain Internal.SnakyRows013.named_envelope_611_60_chain Internal.SnakyRows013.named_envelope_611_57_last Internal.SnakyRows013.named_envelope_611_60_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_56_head : (named_envelope_611_56.map Internal.SnakyRows013.namedCellKey).head? = some (1027 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_57 Internal.SnakyRows013.named_envelope_611_60 (1027 : ℤ) Internal.SnakyRows013.named_envelope_611_57_head
theorem Internal.SnakyRows013.named_envelope_611_56_last : (named_envelope_611_56.map Internal.SnakyRows013.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_57 Internal.SnakyRows013.named_envelope_611_60 (1792 : ℤ) Internal.SnakyRows013.named_envelope_611_60_last
def Internal.SnakyRows013.named_envelope_611_48 : List Cell := Internal.SnakyRows013.named_envelope_611_49 ++ Internal.SnakyRows013.named_envelope_611_56
theorem Internal.SnakyRows013.named_envelope_611_48_chain : (named_envelope_611_48.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_49 Internal.SnakyRows013.named_envelope_611_56 (1026 : ℤ) (1027 : ℤ)
    Internal.SnakyRows013.named_envelope_611_49_chain Internal.SnakyRows013.named_envelope_611_56_chain Internal.SnakyRows013.named_envelope_611_49_last Internal.SnakyRows013.named_envelope_611_56_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_48_head : (named_envelope_611_48.map Internal.SnakyRows013.namedCellKey).head? = some (642 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_49 Internal.SnakyRows013.named_envelope_611_56 (642 : ℤ) Internal.SnakyRows013.named_envelope_611_49_head
theorem Internal.SnakyRows013.named_envelope_611_48_last : (named_envelope_611_48.map Internal.SnakyRows013.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_49 Internal.SnakyRows013.named_envelope_611_56 (1792 : ℤ) Internal.SnakyRows013.named_envelope_611_56_last
def Internal.SnakyRows013.named_envelope_611_32 : List Cell := Internal.SnakyRows013.named_envelope_611_33 ++ Internal.SnakyRows013.named_envelope_611_48
theorem Internal.SnakyRows013.named_envelope_611_32_chain : (named_envelope_611_32.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_33 Internal.SnakyRows013.named_envelope_611_48 (641 : ℤ) (642 : ℤ)
    Internal.SnakyRows013.named_envelope_611_33_chain Internal.SnakyRows013.named_envelope_611_48_chain Internal.SnakyRows013.named_envelope_611_33_last Internal.SnakyRows013.named_envelope_611_48_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_32_head : (named_envelope_611_32.map Internal.SnakyRows013.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_33 Internal.SnakyRows013.named_envelope_611_48 (-128 : ℤ) Internal.SnakyRows013.named_envelope_611_33_head
theorem Internal.SnakyRows013.named_envelope_611_32_last : (named_envelope_611_32.map Internal.SnakyRows013.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_33 Internal.SnakyRows013.named_envelope_611_48 (1792 : ℤ) Internal.SnakyRows013.named_envelope_611_48_last
def Internal.SnakyRows013.named_envelope_611_0 : List Cell := Internal.SnakyRows013.named_envelope_611_1 ++ Internal.SnakyRows013.named_envelope_611_32
theorem Internal.SnakyRows013.named_envelope_611_0_chain : (named_envelope_611_0.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows013.named_chain_append Internal.SnakyRows013.named_envelope_611_1 Internal.SnakyRows013.named_envelope_611_32 (-129 : ℤ) (-128 : ℤ)
    Internal.SnakyRows013.named_envelope_611_1_chain Internal.SnakyRows013.named_envelope_611_32_chain Internal.SnakyRows013.named_envelope_611_1_last Internal.SnakyRows013.named_envelope_611_32_head (by decide)
theorem Internal.SnakyRows013.named_envelope_611_0_head : (named_envelope_611_0.map Internal.SnakyRows013.namedCellKey).head? = some (-2048 : ℤ) :=
  Internal.SnakyRows013.named_head_append Internal.SnakyRows013.named_envelope_611_1 Internal.SnakyRows013.named_envelope_611_32 (-2048 : ℤ) Internal.SnakyRows013.named_envelope_611_1_head
theorem Internal.SnakyRows013.named_envelope_611_0_last : (named_envelope_611_0.map Internal.SnakyRows013.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows013.named_last_append Internal.SnakyRows013.named_envelope_611_1 Internal.SnakyRows013.named_envelope_611_32 (1792 : ℤ) Internal.SnakyRows013.named_envelope_611_32_last
theorem Internal.SnakyRows013.named_envelope_611_nodup : (Internal.SnakyRows013.named_envelope_611_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows013.named_nodup_of_chain Internal.SnakyRows013.named_envelope_611_0 Internal.SnakyRows013.named_envelope_611_0_chain
def envelope_611 : Finset Cell := ⟨(Internal.SnakyRows013.named_envelope_611_0 : Multiset Cell), Internal.SnakyRows013.named_envelope_611_nodup⟩
def childrenC_611 : Fin 4 → Finset Cell := ![(placedSet 2 (1, 0) required_456), (placedSet 4 (-3, 0) required_456), (placedSet 7 (-3, -1) required_594), (placedSet 1 (1, 1) required_594)]
def childrenD_611 : Fin 4 → Finset Cell := ![(placedSet 2 (1, 0) envelope_456), (placedSet 4 (-3, 0) envelope_456), (placedSet 7 (-3, -1) envelope_594), (placedSet 1 (1, 1) envelope_594)]
theorem common_sub_611 : commonEnvelope childrenD_611 ⊆ insert (0, 0) required_611 := by decide
theorem child_required_sub_611 : ∀ j, childrenC_611 j ⊆ insert (0, 0) required_611 := by decide
theorem Internal.SnakyRows013.containment_611_0_points_0 :
    ∀ p ∈ ([(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 2 (1, 0) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_0_points_1 :
    ∀ p ∈ ([(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)] : List Cell), placement 2 (1, 0) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_0 :
    placedSet 2 (1, 0) envelope_456 ⊆ envelope_611 := by
  apply Internal.SnakyRows013.placedSet_subset_of_points
  change ∀ p ∈ ((([(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4)] : List Cell) ++ ([(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)] : List Cell))), placement 2 (1, 0) p ∈ envelope_611
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows013.containment_611_0_points_0, Internal.SnakyRows013.containment_611_0_points_1⟩
theorem Internal.SnakyRows013.containment_611_1_points_0 :
    ∀ p ∈ ([(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 4 (-3, 0) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_1_points_1 :
    ∀ p ∈ ([(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)] : List Cell), placement 4 (-3, 0) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_1 :
    placedSet 4 (-3, 0) envelope_456 ⊆ envelope_611 := by
  apply Internal.SnakyRows013.placedSet_subset_of_points
  change ∀ p ∈ ((([(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4)] : List Cell) ++ ([(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)] : List Cell))), placement 4 (-3, 0) p ∈ envelope_611
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows013.containment_611_1_points_0, Internal.SnakyRows013.containment_611_1_points_1⟩
theorem Internal.SnakyRows013.containment_611_2_points_0 :
    ∀ p ∈ ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_1 :
    ∀ p ∈ ([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_2 :
    ∀ p ∈ ([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_3 :
    ∀ p ∈ ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_4 :
    ∀ p ∈ ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_5 :
    ∀ p ∈ ([(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_6 :
    ∀ p ∈ ([(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_7 :
    ∀ p ∈ ([(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_8 :
    ∀ p ∈ ([(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_9 :
    ∀ p ∈ ([(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_10 :
    ∀ p ∈ ([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_11 :
    ∀ p ∈ ([(6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_12 :
    ∀ p ∈ ([(8, -3), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2_points_13 :
    ∀ p ∈ ([(10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell), placement 7 (-3, -1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_2 :
    placedSet 7 (-3, -1) envelope_594 ⊆ envelope_611 := by decide +kernel
theorem Internal.SnakyRows013.containment_611_3_points_0 :
    ∀ p ∈ ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_1 :
    ∀ p ∈ ([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_2 :
    ∀ p ∈ ([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_3 :
    ∀ p ∈ ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_4 :
    ∀ p ∈ ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_5 :
    ∀ p ∈ ([(0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_6 :
    ∀ p ∈ ([(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_7 :
    ∀ p ∈ ([(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_8 :
    ∀ p ∈ ([(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_9 :
    ∀ p ∈ ([(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_10 :
    ∀ p ∈ ([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_11 :
    ∀ p ∈ ([(6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_12 :
    ∀ p ∈ ([(8, -3), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3_points_13 :
    ∀ p ∈ ([(10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell), placement 1 (1, 1) p ∈ envelope_611 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem Internal.SnakyRows013.containment_611_3 :
    placedSet 1 (1, 1) envelope_594 ⊆ envelope_611 := by decide +kernel
theorem child_envelope_sub_611 : ∀ j, childrenD_611 j ⊆ envelope_611 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows013.containment_611_0
  · exact Internal.SnakyRows013.containment_611_1
  · exact Internal.SnakyRows013.containment_611_2
  · exact Internal.SnakyRows013.containment_611_3
theorem pivot_mem_611 : (0, 0) ∈ envelope_611 := by decide
theorem children_work_611 : ∀ j, Template HasSnaky 28 (childrenC_611 j) (childrenD_611 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_456 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_456 4 (-3, 0)).mono (by decide)
  · exact (placed_template_map row_works_594 7 (-3, -1)).mono (by decide)
  · exact (placed_template_map row_works_594 1 (1, 1)).mono (by decide)
theorem row_works_611 : Template HasSnaky 29 required_611 envelope_611 := by
  refine compose HasSnaky 28 childrenC_611 childrenD_611 children_work_611 (0, 0)
    required_611 envelope_611 pivot_mem_611 child_required_sub_611 child_envelope_sub_611 ?_
  intro b hb; exact common_sub_611 (mem_commonEnvelope childrenD_611 b hb)
end SnakyConditional

end OAI
