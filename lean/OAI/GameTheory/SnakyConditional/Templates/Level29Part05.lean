import OAI.GameTheory.SnakyConditional.Templates.Level27Part03
import OAI.GameTheory.SnakyConditional.Templates.Level27Part04
import OAI.GameTheory.SnakyConditional.Templates.Level28Part04

namespace OAI

namespace SnakyConditional
def required_599 : Finset Cell := ⟨(([(0, -3), (0, -1), (1, -4), (1, -3)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011D.named_envelope_599_4 : List Cell := ([(-11, -1), (-11, 1), (-10, -1), (-10, 0), (-10, 1), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-8, -2), (-8, -1)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_4_chain : (named_envelope_599_4.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_4_head : (named_envelope_599_4.map Internal.SnakyRows011D.namedCellKey).head? = some (-1409 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_4_last : (named_envelope_599_4.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-1025 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_5 : List Cell := ([(-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_5_chain : (named_envelope_599_5.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_5_head : (named_envelope_599_5.map Internal.SnakyRows011D.namedCellKey).head? = some (-1024 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_5_last : (named_envelope_599_5.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-892 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_3 : List Cell := Internal.SnakyRows011D.named_envelope_599_4 ++ Internal.SnakyRows011D.named_envelope_599_5
theorem Internal.SnakyRows011D.named_envelope_599_3_chain : (named_envelope_599_3.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_4 Internal.SnakyRows011D.named_envelope_599_5 (-1025 : ℤ) (-1024 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_4_chain Internal.SnakyRows011D.named_envelope_599_5_chain Internal.SnakyRows011D.named_envelope_599_4_last Internal.SnakyRows011D.named_envelope_599_5_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_3_head : (named_envelope_599_3.map Internal.SnakyRows011D.namedCellKey).head? = some (-1409 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_4 Internal.SnakyRows011D.named_envelope_599_5 (-1409 : ℤ) Internal.SnakyRows011D.named_envelope_599_4_head
theorem Internal.SnakyRows011D.named_envelope_599_3_last : (named_envelope_599_3.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-892 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_4 Internal.SnakyRows011D.named_envelope_599_5 (-892 : ℤ) Internal.SnakyRows011D.named_envelope_599_5_last
def Internal.SnakyRows011D.named_envelope_599_7 : List Cell := ([(-7, 5), (-7, 6), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, -4)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_7_chain : (named_envelope_599_7.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_7_head : (named_envelope_599_7.map Internal.SnakyRows011D.namedCellKey).head? = some (-891 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_7_last : (named_envelope_599_7.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-644 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_8 : List Cell := ([(-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -6), (-4, -5), (-4, -4), (-4, -3)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_8_chain : (named_envelope_599_8.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_8_head : (named_envelope_599_8.map Internal.SnakyRows011D.namedCellKey).head? = some (-643 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_8_last : (named_envelope_599_8.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-515 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_6 : List Cell := Internal.SnakyRows011D.named_envelope_599_7 ++ Internal.SnakyRows011D.named_envelope_599_8
theorem Internal.SnakyRows011D.named_envelope_599_6_chain : (named_envelope_599_6.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_7 Internal.SnakyRows011D.named_envelope_599_8 (-644 : ℤ) (-643 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_7_chain Internal.SnakyRows011D.named_envelope_599_8_chain Internal.SnakyRows011D.named_envelope_599_7_last Internal.SnakyRows011D.named_envelope_599_8_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_6_head : (named_envelope_599_6.map Internal.SnakyRows011D.namedCellKey).head? = some (-891 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_7 Internal.SnakyRows011D.named_envelope_599_8 (-891 : ℤ) Internal.SnakyRows011D.named_envelope_599_7_head
theorem Internal.SnakyRows011D.named_envelope_599_6_last : (named_envelope_599_6.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-515 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_7 Internal.SnakyRows011D.named_envelope_599_8 (-515 : ℤ) Internal.SnakyRows011D.named_envelope_599_8_last
def Internal.SnakyRows011D.named_envelope_599_2 : List Cell := Internal.SnakyRows011D.named_envelope_599_3 ++ Internal.SnakyRows011D.named_envelope_599_6
theorem Internal.SnakyRows011D.named_envelope_599_2_chain : (named_envelope_599_2.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_3 Internal.SnakyRows011D.named_envelope_599_6 (-892 : ℤ) (-891 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_3_chain Internal.SnakyRows011D.named_envelope_599_6_chain Internal.SnakyRows011D.named_envelope_599_3_last Internal.SnakyRows011D.named_envelope_599_6_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_2_head : (named_envelope_599_2.map Internal.SnakyRows011D.namedCellKey).head? = some (-1409 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_3 Internal.SnakyRows011D.named_envelope_599_6 (-1409 : ℤ) Internal.SnakyRows011D.named_envelope_599_3_head
theorem Internal.SnakyRows011D.named_envelope_599_2_last : (named_envelope_599_2.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-515 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_3 Internal.SnakyRows011D.named_envelope_599_6 (-515 : ℤ) Internal.SnakyRows011D.named_envelope_599_6_last
def Internal.SnakyRows011D.named_envelope_599_11 : List Cell := ([(-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -5), (-3, -4), (-3, -3)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_11_chain : (named_envelope_599_11.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_11_head : (named_envelope_599_11.map Internal.SnakyRows011D.namedCellKey).head? = some (-514 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_11_last : (named_envelope_599_11.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-387 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_12 : List Cell := ([(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, -6), (-2, -5)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_12_chain : (named_envelope_599_12.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_12_head : (named_envelope_599_12.map Internal.SnakyRows011D.namedCellKey).head? = some (-386 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_12_last : (named_envelope_599_12.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-261 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_10 : List Cell := Internal.SnakyRows011D.named_envelope_599_11 ++ Internal.SnakyRows011D.named_envelope_599_12
theorem Internal.SnakyRows011D.named_envelope_599_10_chain : (named_envelope_599_10.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_11 Internal.SnakyRows011D.named_envelope_599_12 (-387 : ℤ) (-386 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_11_chain Internal.SnakyRows011D.named_envelope_599_12_chain Internal.SnakyRows011D.named_envelope_599_11_last Internal.SnakyRows011D.named_envelope_599_12_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_10_head : (named_envelope_599_10.map Internal.SnakyRows011D.namedCellKey).head? = some (-514 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_11 Internal.SnakyRows011D.named_envelope_599_12 (-514 : ℤ) Internal.SnakyRows011D.named_envelope_599_11_head
theorem Internal.SnakyRows011D.named_envelope_599_10_last : (named_envelope_599_10.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-261 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_11 Internal.SnakyRows011D.named_envelope_599_12 (-261 : ℤ) Internal.SnakyRows011D.named_envelope_599_12_last
def Internal.SnakyRows011D.named_envelope_599_14 : List Cell := ([(-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_14_chain : (named_envelope_599_14.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_14_head : (named_envelope_599_14.map Internal.SnakyRows011D.namedCellKey).head? = some (-260 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_14_last : (named_envelope_599_14.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-246 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_15 : List Cell := ([(-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_15_chain : (named_envelope_599_15.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_15_head : (named_envelope_599_15.map Internal.SnakyRows011D.namedCellKey).head? = some (-133 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_15_last : (named_envelope_599_15.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-119 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_13 : List Cell := Internal.SnakyRows011D.named_envelope_599_14 ++ Internal.SnakyRows011D.named_envelope_599_15
theorem Internal.SnakyRows011D.named_envelope_599_13_chain : (named_envelope_599_13.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_14 Internal.SnakyRows011D.named_envelope_599_15 (-246 : ℤ) (-133 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_14_chain Internal.SnakyRows011D.named_envelope_599_15_chain Internal.SnakyRows011D.named_envelope_599_14_last Internal.SnakyRows011D.named_envelope_599_15_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_13_head : (named_envelope_599_13.map Internal.SnakyRows011D.namedCellKey).head? = some (-260 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_14 Internal.SnakyRows011D.named_envelope_599_15 (-260 : ℤ) Internal.SnakyRows011D.named_envelope_599_14_head
theorem Internal.SnakyRows011D.named_envelope_599_13_last : (named_envelope_599_13.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-119 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_14 Internal.SnakyRows011D.named_envelope_599_15 (-119 : ℤ) Internal.SnakyRows011D.named_envelope_599_15_last
def Internal.SnakyRows011D.named_envelope_599_9 : List Cell := Internal.SnakyRows011D.named_envelope_599_10 ++ Internal.SnakyRows011D.named_envelope_599_13
theorem Internal.SnakyRows011D.named_envelope_599_9_chain : (named_envelope_599_9.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_10 Internal.SnakyRows011D.named_envelope_599_13 (-261 : ℤ) (-260 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_10_chain Internal.SnakyRows011D.named_envelope_599_13_chain Internal.SnakyRows011D.named_envelope_599_10_last Internal.SnakyRows011D.named_envelope_599_13_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_9_head : (named_envelope_599_9.map Internal.SnakyRows011D.namedCellKey).head? = some (-514 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_10 Internal.SnakyRows011D.named_envelope_599_13 (-514 : ℤ) Internal.SnakyRows011D.named_envelope_599_10_head
theorem Internal.SnakyRows011D.named_envelope_599_9_last : (named_envelope_599_9.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-119 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_10 Internal.SnakyRows011D.named_envelope_599_13 (-119 : ℤ) Internal.SnakyRows011D.named_envelope_599_13_last
def Internal.SnakyRows011D.named_envelope_599_1 : List Cell := Internal.SnakyRows011D.named_envelope_599_2 ++ Internal.SnakyRows011D.named_envelope_599_9
theorem Internal.SnakyRows011D.named_envelope_599_1_chain : (named_envelope_599_1.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_2 Internal.SnakyRows011D.named_envelope_599_9 (-515 : ℤ) (-514 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_2_chain Internal.SnakyRows011D.named_envelope_599_9_chain Internal.SnakyRows011D.named_envelope_599_2_last Internal.SnakyRows011D.named_envelope_599_9_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_1_head : (named_envelope_599_1.map Internal.SnakyRows011D.namedCellKey).head? = some (-1409 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_2 Internal.SnakyRows011D.named_envelope_599_9 (-1409 : ℤ) Internal.SnakyRows011D.named_envelope_599_2_head
theorem Internal.SnakyRows011D.named_envelope_599_1_last : (named_envelope_599_1.map Internal.SnakyRows011D.namedCellKey).getLast? = some (-119 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_2 Internal.SnakyRows011D.named_envelope_599_9 (-119 : ℤ) Internal.SnakyRows011D.named_envelope_599_9_last
def Internal.SnakyRows011D.named_envelope_599_19 : List Cell := ([(-1, 10), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_19_chain : (named_envelope_599_19.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_19_head : (named_envelope_599_19.map Internal.SnakyRows011D.namedCellKey).head? = some (-118 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_19_last : (named_envelope_599_19.map Internal.SnakyRows011D.namedCellKey).getLast? = some (10 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_20 : List Cell := ([(1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_20_chain : (named_envelope_599_20.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_20_head : (named_envelope_599_20.map Internal.SnakyRows011D.namedCellKey).head? = some (124 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_20_last : (named_envelope_599_20.map Internal.SnakyRows011D.namedCellKey).getLast? = some (138 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_18 : List Cell := Internal.SnakyRows011D.named_envelope_599_19 ++ Internal.SnakyRows011D.named_envelope_599_20
theorem Internal.SnakyRows011D.named_envelope_599_18_chain : (named_envelope_599_18.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_19 Internal.SnakyRows011D.named_envelope_599_20 (10 : ℤ) (124 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_19_chain Internal.SnakyRows011D.named_envelope_599_20_chain Internal.SnakyRows011D.named_envelope_599_19_last Internal.SnakyRows011D.named_envelope_599_20_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_18_head : (named_envelope_599_18.map Internal.SnakyRows011D.namedCellKey).head? = some (-118 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_19 Internal.SnakyRows011D.named_envelope_599_20 (-118 : ℤ) Internal.SnakyRows011D.named_envelope_599_19_head
theorem Internal.SnakyRows011D.named_envelope_599_18_last : (named_envelope_599_18.map Internal.SnakyRows011D.namedCellKey).getLast? = some (138 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_19 Internal.SnakyRows011D.named_envelope_599_20 (138 : ℤ) Internal.SnakyRows011D.named_envelope_599_20_last
def Internal.SnakyRows011D.named_envelope_599_22 : List Cell := ([(1, 11), (1, 12), (2, -4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_22_chain : (named_envelope_599_22.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_22_head : (named_envelope_599_22.map Internal.SnakyRows011D.namedCellKey).head? = some (139 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_22_last : (named_envelope_599_22.map Internal.SnakyRows011D.namedCellKey).getLast? = some (265 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_23 : List Cell := ([(2, 10), (2, 11), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_23_chain : (named_envelope_599_23.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_23_head : (named_envelope_599_23.map Internal.SnakyRows011D.namedCellKey).head? = some (266 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_23_last : (named_envelope_599_23.map Internal.SnakyRows011D.namedCellKey).getLast? = some (393 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_21 : List Cell := Internal.SnakyRows011D.named_envelope_599_22 ++ Internal.SnakyRows011D.named_envelope_599_23
theorem Internal.SnakyRows011D.named_envelope_599_21_chain : (named_envelope_599_21.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_22 Internal.SnakyRows011D.named_envelope_599_23 (265 : ℤ) (266 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_22_chain Internal.SnakyRows011D.named_envelope_599_23_chain Internal.SnakyRows011D.named_envelope_599_22_last Internal.SnakyRows011D.named_envelope_599_23_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_21_head : (named_envelope_599_21.map Internal.SnakyRows011D.namedCellKey).head? = some (139 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_22 Internal.SnakyRows011D.named_envelope_599_23 (139 : ℤ) Internal.SnakyRows011D.named_envelope_599_22_head
theorem Internal.SnakyRows011D.named_envelope_599_21_last : (named_envelope_599_21.map Internal.SnakyRows011D.namedCellKey).getLast? = some (393 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_22 Internal.SnakyRows011D.named_envelope_599_23 (393 : ℤ) Internal.SnakyRows011D.named_envelope_599_23_last
def Internal.SnakyRows011D.named_envelope_599_17 : List Cell := Internal.SnakyRows011D.named_envelope_599_18 ++ Internal.SnakyRows011D.named_envelope_599_21
theorem Internal.SnakyRows011D.named_envelope_599_17_chain : (named_envelope_599_17.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_18 Internal.SnakyRows011D.named_envelope_599_21 (138 : ℤ) (139 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_18_chain Internal.SnakyRows011D.named_envelope_599_21_chain Internal.SnakyRows011D.named_envelope_599_18_last Internal.SnakyRows011D.named_envelope_599_21_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_17_head : (named_envelope_599_17.map Internal.SnakyRows011D.namedCellKey).head? = some (-118 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_18 Internal.SnakyRows011D.named_envelope_599_21 (-118 : ℤ) Internal.SnakyRows011D.named_envelope_599_18_head
theorem Internal.SnakyRows011D.named_envelope_599_17_last : (named_envelope_599_17.map Internal.SnakyRows011D.namedCellKey).getLast? = some (393 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_18 Internal.SnakyRows011D.named_envelope_599_21 (393 : ℤ) Internal.SnakyRows011D.named_envelope_599_21_last
def Internal.SnakyRows011D.named_envelope_599_26 : List Cell := ([(3, 10), (3, 11), (3, 12), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_26_chain : (named_envelope_599_26.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_26_head : (named_envelope_599_26.map Internal.SnakyRows011D.namedCellKey).head? = some (394 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_26_last : (named_envelope_599_26.map Internal.SnakyRows011D.namedCellKey).getLast? = some (519 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_27 : List Cell := ([(4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_27_chain : (named_envelope_599_27.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_27_head : (named_envelope_599_27.map Internal.SnakyRows011D.namedCellKey).head? = some (520 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_27_last : (named_envelope_599_27.map Internal.SnakyRows011D.namedCellKey).getLast? = some (649 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_25 : List Cell := Internal.SnakyRows011D.named_envelope_599_26 ++ Internal.SnakyRows011D.named_envelope_599_27
theorem Internal.SnakyRows011D.named_envelope_599_25_chain : (named_envelope_599_25.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_26 Internal.SnakyRows011D.named_envelope_599_27 (519 : ℤ) (520 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_26_chain Internal.SnakyRows011D.named_envelope_599_27_chain Internal.SnakyRows011D.named_envelope_599_26_last Internal.SnakyRows011D.named_envelope_599_27_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_25_head : (named_envelope_599_25.map Internal.SnakyRows011D.namedCellKey).head? = some (394 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_26 Internal.SnakyRows011D.named_envelope_599_27 (394 : ℤ) Internal.SnakyRows011D.named_envelope_599_26_head
theorem Internal.SnakyRows011D.named_envelope_599_25_last : (named_envelope_599_25.map Internal.SnakyRows011D.namedCellKey).getLast? = some (649 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_26 Internal.SnakyRows011D.named_envelope_599_27 (649 : ℤ) Internal.SnakyRows011D.named_envelope_599_27_last
def Internal.SnakyRows011D.named_envelope_599_29 : List Cell := ([(5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -2), (7, -1)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_29_chain : (named_envelope_599_29.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_29_head : (named_envelope_599_29.map Internal.SnakyRows011D.namedCellKey).head? = some (650 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_29_last : (named_envelope_599_29.map Internal.SnakyRows011D.namedCellKey).getLast? = some (895 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_30 : List Cell := ([(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -2), (9, 0), (9, 2)] : List Cell)
theorem Internal.SnakyRows011D.named_envelope_599_30_chain : (named_envelope_599_30.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_30_head : (named_envelope_599_30.map Internal.SnakyRows011D.namedCellKey).head? = some (896 : ℤ) := by decide
theorem Internal.SnakyRows011D.named_envelope_599_30_last : (named_envelope_599_30.map Internal.SnakyRows011D.namedCellKey).getLast? = some (1154 : ℤ) := by decide
def Internal.SnakyRows011D.named_envelope_599_28 : List Cell := Internal.SnakyRows011D.named_envelope_599_29 ++ Internal.SnakyRows011D.named_envelope_599_30
theorem Internal.SnakyRows011D.named_envelope_599_28_chain : (named_envelope_599_28.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_29 Internal.SnakyRows011D.named_envelope_599_30 (895 : ℤ) (896 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_29_chain Internal.SnakyRows011D.named_envelope_599_30_chain Internal.SnakyRows011D.named_envelope_599_29_last Internal.SnakyRows011D.named_envelope_599_30_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_28_head : (named_envelope_599_28.map Internal.SnakyRows011D.namedCellKey).head? = some (650 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_29 Internal.SnakyRows011D.named_envelope_599_30 (650 : ℤ) Internal.SnakyRows011D.named_envelope_599_29_head
theorem Internal.SnakyRows011D.named_envelope_599_28_last : (named_envelope_599_28.map Internal.SnakyRows011D.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_29 Internal.SnakyRows011D.named_envelope_599_30 (1154 : ℤ) Internal.SnakyRows011D.named_envelope_599_30_last
def Internal.SnakyRows011D.named_envelope_599_24 : List Cell := Internal.SnakyRows011D.named_envelope_599_25 ++ Internal.SnakyRows011D.named_envelope_599_28
theorem Internal.SnakyRows011D.named_envelope_599_24_chain : (named_envelope_599_24.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_25 Internal.SnakyRows011D.named_envelope_599_28 (649 : ℤ) (650 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_25_chain Internal.SnakyRows011D.named_envelope_599_28_chain Internal.SnakyRows011D.named_envelope_599_25_last Internal.SnakyRows011D.named_envelope_599_28_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_24_head : (named_envelope_599_24.map Internal.SnakyRows011D.namedCellKey).head? = some (394 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_25 Internal.SnakyRows011D.named_envelope_599_28 (394 : ℤ) Internal.SnakyRows011D.named_envelope_599_25_head
theorem Internal.SnakyRows011D.named_envelope_599_24_last : (named_envelope_599_24.map Internal.SnakyRows011D.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_25 Internal.SnakyRows011D.named_envelope_599_28 (1154 : ℤ) Internal.SnakyRows011D.named_envelope_599_28_last
def Internal.SnakyRows011D.named_envelope_599_16 : List Cell := Internal.SnakyRows011D.named_envelope_599_17 ++ Internal.SnakyRows011D.named_envelope_599_24
theorem Internal.SnakyRows011D.named_envelope_599_16_chain : (named_envelope_599_16.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_17 Internal.SnakyRows011D.named_envelope_599_24 (393 : ℤ) (394 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_17_chain Internal.SnakyRows011D.named_envelope_599_24_chain Internal.SnakyRows011D.named_envelope_599_17_last Internal.SnakyRows011D.named_envelope_599_24_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_16_head : (named_envelope_599_16.map Internal.SnakyRows011D.namedCellKey).head? = some (-118 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_17 Internal.SnakyRows011D.named_envelope_599_24 (-118 : ℤ) Internal.SnakyRows011D.named_envelope_599_17_head
theorem Internal.SnakyRows011D.named_envelope_599_16_last : (named_envelope_599_16.map Internal.SnakyRows011D.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_17 Internal.SnakyRows011D.named_envelope_599_24 (1154 : ℤ) Internal.SnakyRows011D.named_envelope_599_24_last
def Internal.SnakyRows011D.named_envelope_599_0 : List Cell := Internal.SnakyRows011D.named_envelope_599_1 ++ Internal.SnakyRows011D.named_envelope_599_16
theorem Internal.SnakyRows011D.named_envelope_599_0_chain : (named_envelope_599_0.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011D.named_chain_append Internal.SnakyRows011D.named_envelope_599_1 Internal.SnakyRows011D.named_envelope_599_16 (-119 : ℤ) (-118 : ℤ)
    Internal.SnakyRows011D.named_envelope_599_1_chain Internal.SnakyRows011D.named_envelope_599_16_chain Internal.SnakyRows011D.named_envelope_599_1_last Internal.SnakyRows011D.named_envelope_599_16_head (by decide)
theorem Internal.SnakyRows011D.named_envelope_599_0_head : (named_envelope_599_0.map Internal.SnakyRows011D.namedCellKey).head? = some (-1409 : ℤ) :=
  Internal.SnakyRows011D.named_head_append Internal.SnakyRows011D.named_envelope_599_1 Internal.SnakyRows011D.named_envelope_599_16 (-1409 : ℤ) Internal.SnakyRows011D.named_envelope_599_1_head
theorem Internal.SnakyRows011D.named_envelope_599_0_last : (named_envelope_599_0.map Internal.SnakyRows011D.namedCellKey).getLast? = some (1154 : ℤ) :=
  Internal.SnakyRows011D.named_last_append Internal.SnakyRows011D.named_envelope_599_1 Internal.SnakyRows011D.named_envelope_599_16 (1154 : ℤ) Internal.SnakyRows011D.named_envelope_599_16_last
theorem Internal.SnakyRows011D.named_envelope_599_nodup : (Internal.SnakyRows011D.named_envelope_599_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011D.named_nodup_of_chain Internal.SnakyRows011D.named_envelope_599_0 Internal.SnakyRows011D.named_envelope_599_0_chain
def envelope_599 : Finset Cell := ⟨(Internal.SnakyRows011D.named_envelope_599_0 : Multiset Cell), Internal.SnakyRows011D.named_envelope_599_nodup⟩
def childrenC_599 : Fin 6 → Finset Cell := ![(placedSet 4 (1, -1) required_578), (placedSet 0 (-1, -3) required_492), (placedSet 4 (-1, -3) required_512), (placedSet 4 (0, 1) required_586), (placedSet 0 (1, -1) required_485), (placedSet 4 (1, -1) required_579)]
def childrenD_599 : Fin 6 → Finset Cell := ![(placedSet 4 (1, -1) envelope_578), (placedSet 0 (-1, -3) envelope_492), (placedSet 4 (-1, -3) envelope_512), (placedSet 4 (0, 1) envelope_586), (placedSet 0 (1, -1) envelope_485), (placedSet 4 (1, -1) envelope_579)]
theorem common_sub_599 : commonEnvelope childrenD_599 ⊆ insert (0, 0) required_599 := by decide
theorem child_required_sub_599 : ∀ j, childrenC_599 j ⊆ insert (0, 0) required_599 := by decide
theorem Internal.SnakyRows011D.containment_599_0 :
    placedSet 4 (1, -1) envelope_578 ⊆ envelope_599 := by decide +kernel
theorem Internal.SnakyRows011D.containment_599_1 :
    placedSet 0 (-1, -3) envelope_492 ⊆ envelope_599 := by decide
theorem Internal.SnakyRows011D.containment_599_2 :
    placedSet 4 (-1, -3) envelope_512 ⊆ envelope_599 := by decide
theorem Internal.SnakyRows011D.containment_599_3 :
    placedSet 4 (0, 1) envelope_586 ⊆ envelope_599 := by decide +kernel
theorem Internal.SnakyRows011D.containment_599_4 :
    placedSet 0 (1, -1) envelope_485 ⊆ envelope_599 := by decide
theorem Internal.SnakyRows011D.containment_599_5 :
    placedSet 4 (1, -1) envelope_579 ⊆ envelope_599 := by decide +kernel
theorem child_envelope_sub_599 : ∀ j, childrenD_599 j ⊆ envelope_599 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011D.containment_599_0
  · exact Internal.SnakyRows011D.containment_599_1
  · exact Internal.SnakyRows011D.containment_599_2
  · exact Internal.SnakyRows011D.containment_599_3
  · exact Internal.SnakyRows011D.containment_599_4
  · exact Internal.SnakyRows011D.containment_599_5
theorem pivot_mem_599 : (0, 0) ∈ envelope_599 := by decide
theorem children_work_599 : ∀ j, Template HasSnaky 26 (childrenC_599 j) (childrenD_599 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_578 4 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_492 0 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_512 4 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_586 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_485 0 (1, -1)).mono (by decide)
  · exact (placed_template_map row_works_579 4 (1, -1)).mono (by decide)
theorem row_works_599 : Template HasSnaky 27 required_599 envelope_599 := by
  refine compose HasSnaky 26 childrenC_599 childrenD_599 children_work_599 (0, 0)
    required_599 envelope_599 pivot_mem_599 child_required_sub_599 child_envelope_sub_599 ?_
  intro b hb; exact common_sub_599 (mem_commonEnvelope childrenD_599 b hb)
end SnakyConditional

end OAI
