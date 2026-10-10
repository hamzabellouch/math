import OAI.GameTheory.SnakyConditional.Templates.Level30Part01

namespace OAI

namespace SnakyConditional
def required_612 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows014.named_envelope_612_5 : List Cell := ([(-17, 0), (-17, 2), (-16, 0), (-16, 1), (-16, 2), (-15, -4), (-15, -3), (-15, -2), (-15, -1), (-15, 0), (-15, 1), (-15, 2)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_5_chain : (named_envelope_612_5.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_5_head : (named_envelope_612_5.map Internal.SnakyRows014.namedCellKey).head? = some (-2176 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_5_last : (named_envelope_612_5.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1918 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_6 : List Cell := ([(-15, 4), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 3), (-14, 4), (-13, -5), (-13, -4), (-13, -3)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_6_chain : (named_envelope_612_6.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_6_head : (named_envelope_612_6.map Internal.SnakyRows014.namedCellKey).head? = some (-1916 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_6_last : (named_envelope_612_6.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1667 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_4 : List Cell := Internal.SnakyRows014.named_envelope_612_5 ++ Internal.SnakyRows014.named_envelope_612_6
theorem Internal.SnakyRows014.named_envelope_612_4_chain : (named_envelope_612_4.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_5 Internal.SnakyRows014.named_envelope_612_6 (-1918 : ℤ) (-1916 : ℤ)
    Internal.SnakyRows014.named_envelope_612_5_chain Internal.SnakyRows014.named_envelope_612_6_chain Internal.SnakyRows014.named_envelope_612_5_last Internal.SnakyRows014.named_envelope_612_6_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_4_head : (named_envelope_612_4.map Internal.SnakyRows014.namedCellKey).head? = some (-2176 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_5 Internal.SnakyRows014.named_envelope_612_6 (-2176 : ℤ) Internal.SnakyRows014.named_envelope_612_5_head
theorem Internal.SnakyRows014.named_envelope_612_4_last : (named_envelope_612_4.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1667 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_5 Internal.SnakyRows014.named_envelope_612_6 (-1667 : ℤ) Internal.SnakyRows014.named_envelope_612_6_last
def Internal.SnakyRows014.named_envelope_612_8 : List Cell := ([(-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -7), (-12, -6), (-12, -5), (-12, -4), (-12, -3)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_8_chain : (named_envelope_612_8.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_8_head : (named_envelope_612_8.map Internal.SnakyRows014.namedCellKey).head? = some (-1666 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_8_last : (named_envelope_612_8.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1539 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_9 : List Cell := ([(-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-11, -8), (-11, -7), (-11, -6), (-11, -5)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_9_chain : (named_envelope_612_9.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_9_head : (named_envelope_612_9.map Internal.SnakyRows014.namedCellKey).head? = some (-1538 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_9_last : (named_envelope_612_9.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1413 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_7 : List Cell := Internal.SnakyRows014.named_envelope_612_8 ++ Internal.SnakyRows014.named_envelope_612_9
theorem Internal.SnakyRows014.named_envelope_612_7_chain : (named_envelope_612_7.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_8 Internal.SnakyRows014.named_envelope_612_9 (-1539 : ℤ) (-1538 : ℤ)
    Internal.SnakyRows014.named_envelope_612_8_chain Internal.SnakyRows014.named_envelope_612_9_chain Internal.SnakyRows014.named_envelope_612_8_last Internal.SnakyRows014.named_envelope_612_9_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_7_head : (named_envelope_612_7.map Internal.SnakyRows014.namedCellKey).head? = some (-1666 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_8 Internal.SnakyRows014.named_envelope_612_9 (-1666 : ℤ) Internal.SnakyRows014.named_envelope_612_8_head
theorem Internal.SnakyRows014.named_envelope_612_7_last : (named_envelope_612_7.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1413 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_8 Internal.SnakyRows014.named_envelope_612_9 (-1413 : ℤ) Internal.SnakyRows014.named_envelope_612_9_last
def Internal.SnakyRows014.named_envelope_612_3 : List Cell := Internal.SnakyRows014.named_envelope_612_4 ++ Internal.SnakyRows014.named_envelope_612_7
theorem Internal.SnakyRows014.named_envelope_612_3_chain : (named_envelope_612_3.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_4 Internal.SnakyRows014.named_envelope_612_7 (-1667 : ℤ) (-1666 : ℤ)
    Internal.SnakyRows014.named_envelope_612_4_chain Internal.SnakyRows014.named_envelope_612_7_chain Internal.SnakyRows014.named_envelope_612_4_last Internal.SnakyRows014.named_envelope_612_7_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_3_head : (named_envelope_612_3.map Internal.SnakyRows014.namedCellKey).head? = some (-2176 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_4 Internal.SnakyRows014.named_envelope_612_7 (-2176 : ℤ) Internal.SnakyRows014.named_envelope_612_4_head
theorem Internal.SnakyRows014.named_envelope_612_3_last : (named_envelope_612_3.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1413 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_4 Internal.SnakyRows014.named_envelope_612_7 (-1413 : ℤ) Internal.SnakyRows014.named_envelope_612_7_last
def Internal.SnakyRows014.named_envelope_612_12 : List Cell := ([(-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -10), (-10, -9)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_12_chain : (named_envelope_612_12.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_12_head : (named_envelope_612_12.map Internal.SnakyRows014.namedCellKey).head? = some (-1412 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_12_last : (named_envelope_612_12.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1289 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_13 : List Cell := ([(-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_13_chain : (named_envelope_612_13.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_13_head : (named_envelope_612_13.map Internal.SnakyRows014.namedCellKey).head? = some (-1288 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_13_last : (named_envelope_612_13.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1276 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_11 : List Cell := Internal.SnakyRows014.named_envelope_612_12 ++ Internal.SnakyRows014.named_envelope_612_13
theorem Internal.SnakyRows014.named_envelope_612_11_chain : (named_envelope_612_11.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_12 Internal.SnakyRows014.named_envelope_612_13 (-1289 : ℤ) (-1288 : ℤ)
    Internal.SnakyRows014.named_envelope_612_12_chain Internal.SnakyRows014.named_envelope_612_13_chain Internal.SnakyRows014.named_envelope_612_12_last Internal.SnakyRows014.named_envelope_612_13_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_11_head : (named_envelope_612_11.map Internal.SnakyRows014.namedCellKey).head? = some (-1412 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_12 Internal.SnakyRows014.named_envelope_612_13 (-1412 : ℤ) Internal.SnakyRows014.named_envelope_612_12_head
theorem Internal.SnakyRows014.named_envelope_612_11_last : (named_envelope_612_11.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1276 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_12 Internal.SnakyRows014.named_envelope_612_13 (-1276 : ℤ) Internal.SnakyRows014.named_envelope_612_13_last
def Internal.SnakyRows014.named_envelope_612_15 : List Cell := ([(-10, 5), (-10, 6), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_15_chain : (named_envelope_612_15.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_15_head : (named_envelope_612_15.map Internal.SnakyRows014.namedCellKey).head? = some (-1275 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_15_last : (named_envelope_612_15.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1152 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_16 : List Cell := ([(-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_16_chain : (named_envelope_612_16.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_16_head : (named_envelope_612_16.map Internal.SnakyRows014.namedCellKey).head? = some (-1151 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_16_last : (named_envelope_612_16.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1028 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_14 : List Cell := Internal.SnakyRows014.named_envelope_612_15 ++ Internal.SnakyRows014.named_envelope_612_16
theorem Internal.SnakyRows014.named_envelope_612_14_chain : (named_envelope_612_14.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_15 Internal.SnakyRows014.named_envelope_612_16 (-1152 : ℤ) (-1151 : ℤ)
    Internal.SnakyRows014.named_envelope_612_15_chain Internal.SnakyRows014.named_envelope_612_16_chain Internal.SnakyRows014.named_envelope_612_15_last Internal.SnakyRows014.named_envelope_612_16_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_14_head : (named_envelope_612_14.map Internal.SnakyRows014.namedCellKey).head? = some (-1275 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_15 Internal.SnakyRows014.named_envelope_612_16 (-1275 : ℤ) Internal.SnakyRows014.named_envelope_612_15_head
theorem Internal.SnakyRows014.named_envelope_612_14_last : (named_envelope_612_14.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1028 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_15 Internal.SnakyRows014.named_envelope_612_16 (-1028 : ℤ) Internal.SnakyRows014.named_envelope_612_16_last
def Internal.SnakyRows014.named_envelope_612_10 : List Cell := Internal.SnakyRows014.named_envelope_612_11 ++ Internal.SnakyRows014.named_envelope_612_14
theorem Internal.SnakyRows014.named_envelope_612_10_chain : (named_envelope_612_10.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_11 Internal.SnakyRows014.named_envelope_612_14 (-1276 : ℤ) (-1275 : ℤ)
    Internal.SnakyRows014.named_envelope_612_11_chain Internal.SnakyRows014.named_envelope_612_14_chain Internal.SnakyRows014.named_envelope_612_11_last Internal.SnakyRows014.named_envelope_612_14_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_10_head : (named_envelope_612_10.map Internal.SnakyRows014.namedCellKey).head? = some (-1412 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_11 Internal.SnakyRows014.named_envelope_612_14 (-1412 : ℤ) Internal.SnakyRows014.named_envelope_612_11_head
theorem Internal.SnakyRows014.named_envelope_612_10_last : (named_envelope_612_10.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1028 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_11 Internal.SnakyRows014.named_envelope_612_14 (-1028 : ℤ) Internal.SnakyRows014.named_envelope_612_14_last
def Internal.SnakyRows014.named_envelope_612_2 : List Cell := Internal.SnakyRows014.named_envelope_612_3 ++ Internal.SnakyRows014.named_envelope_612_10
theorem Internal.SnakyRows014.named_envelope_612_2_chain : (named_envelope_612_2.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_3 Internal.SnakyRows014.named_envelope_612_10 (-1413 : ℤ) (-1412 : ℤ)
    Internal.SnakyRows014.named_envelope_612_3_chain Internal.SnakyRows014.named_envelope_612_10_chain Internal.SnakyRows014.named_envelope_612_3_last Internal.SnakyRows014.named_envelope_612_10_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_2_head : (named_envelope_612_2.map Internal.SnakyRows014.namedCellKey).head? = some (-2176 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_3 Internal.SnakyRows014.named_envelope_612_10 (-2176 : ℤ) Internal.SnakyRows014.named_envelope_612_3_head
theorem Internal.SnakyRows014.named_envelope_612_2_last : (named_envelope_612_2.map Internal.SnakyRows014.namedCellKey).getLast? = some (-1028 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_3 Internal.SnakyRows014.named_envelope_612_10 (-1028 : ℤ) Internal.SnakyRows014.named_envelope_612_10_last
def Internal.SnakyRows014.named_envelope_612_20 : List Cell := ([(-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-7, -10), (-7, -9), (-7, -8), (-7, -7)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_20_chain : (named_envelope_612_20.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_20_head : (named_envelope_612_20.map Internal.SnakyRows014.namedCellKey).head? = some (-1027 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_20_last : (named_envelope_612_20.map Internal.SnakyRows014.namedCellKey).getLast? = some (-903 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_21 : List Cell := ([(-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -12)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_21_chain : (named_envelope_612_21.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_21_head : (named_envelope_612_21.map Internal.SnakyRows014.namedCellKey).head? = some (-902 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_21_last : (named_envelope_612_21.map Internal.SnakyRows014.namedCellKey).getLast? = some (-780 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_19 : List Cell := Internal.SnakyRows014.named_envelope_612_20 ++ Internal.SnakyRows014.named_envelope_612_21
theorem Internal.SnakyRows014.named_envelope_612_19_chain : (named_envelope_612_19.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_20 Internal.SnakyRows014.named_envelope_612_21 (-903 : ℤ) (-902 : ℤ)
    Internal.SnakyRows014.named_envelope_612_20_chain Internal.SnakyRows014.named_envelope_612_21_chain Internal.SnakyRows014.named_envelope_612_20_last Internal.SnakyRows014.named_envelope_612_21_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_19_head : (named_envelope_612_19.map Internal.SnakyRows014.namedCellKey).head? = some (-1027 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_20 Internal.SnakyRows014.named_envelope_612_21 (-1027 : ℤ) Internal.SnakyRows014.named_envelope_612_20_head
theorem Internal.SnakyRows014.named_envelope_612_19_last : (named_envelope_612_19.map Internal.SnakyRows014.namedCellKey).getLast? = some (-780 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_20 Internal.SnakyRows014.named_envelope_612_21 (-780 : ℤ) Internal.SnakyRows014.named_envelope_612_21_last
def Internal.SnakyRows014.named_envelope_612_23 : List Cell := ([(-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_23_chain : (named_envelope_612_23.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_23_head : (named_envelope_612_23.map Internal.SnakyRows014.namedCellKey).head? = some (-779 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_23_last : (named_envelope_612_23.map Internal.SnakyRows014.namedCellKey).getLast? = some (-768 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_24 : List Cell := ([(-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_24_chain : (named_envelope_612_24.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_24_head : (named_envelope_612_24.map Internal.SnakyRows014.namedCellKey).head? = some (-767 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_24_last : (named_envelope_612_24.map Internal.SnakyRows014.namedCellKey).getLast? = some (-643 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_22 : List Cell := Internal.SnakyRows014.named_envelope_612_23 ++ Internal.SnakyRows014.named_envelope_612_24
theorem Internal.SnakyRows014.named_envelope_612_22_chain : (named_envelope_612_22.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_23 Internal.SnakyRows014.named_envelope_612_24 (-768 : ℤ) (-767 : ℤ)
    Internal.SnakyRows014.named_envelope_612_23_chain Internal.SnakyRows014.named_envelope_612_24_chain Internal.SnakyRows014.named_envelope_612_23_last Internal.SnakyRows014.named_envelope_612_24_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_22_head : (named_envelope_612_22.map Internal.SnakyRows014.namedCellKey).head? = some (-779 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_23 Internal.SnakyRows014.named_envelope_612_24 (-779 : ℤ) Internal.SnakyRows014.named_envelope_612_23_head
theorem Internal.SnakyRows014.named_envelope_612_22_last : (named_envelope_612_22.map Internal.SnakyRows014.namedCellKey).getLast? = some (-643 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_23 Internal.SnakyRows014.named_envelope_612_24 (-643 : ℤ) Internal.SnakyRows014.named_envelope_612_24_last
def Internal.SnakyRows014.named_envelope_612_18 : List Cell := Internal.SnakyRows014.named_envelope_612_19 ++ Internal.SnakyRows014.named_envelope_612_22
theorem Internal.SnakyRows014.named_envelope_612_18_chain : (named_envelope_612_18.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_19 Internal.SnakyRows014.named_envelope_612_22 (-780 : ℤ) (-779 : ℤ)
    Internal.SnakyRows014.named_envelope_612_19_chain Internal.SnakyRows014.named_envelope_612_22_chain Internal.SnakyRows014.named_envelope_612_19_last Internal.SnakyRows014.named_envelope_612_22_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_18_head : (named_envelope_612_18.map Internal.SnakyRows014.namedCellKey).head? = some (-1027 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_19 Internal.SnakyRows014.named_envelope_612_22 (-1027 : ℤ) Internal.SnakyRows014.named_envelope_612_19_head
theorem Internal.SnakyRows014.named_envelope_612_18_last : (named_envelope_612_18.map Internal.SnakyRows014.namedCellKey).getLast? = some (-643 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_19 Internal.SnakyRows014.named_envelope_612_22 (-643 : ℤ) Internal.SnakyRows014.named_envelope_612_22_last
def Internal.SnakyRows014.named_envelope_612_27 : List Cell := ([(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_27_chain : (named_envelope_612_27.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_27_head : (named_envelope_612_27.map Internal.SnakyRows014.namedCellKey).head? = some (-642 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_27_last : (named_envelope_612_27.map Internal.SnakyRows014.namedCellKey).getLast? = some (-520 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_28 : List Cell := ([(-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 3), (-4, 5), (-3, -8), (-3, -7)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_28_chain : (named_envelope_612_28.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_28_head : (named_envelope_612_28.map Internal.SnakyRows014.namedCellKey).head? = some (-519 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_28_last : (named_envelope_612_28.map Internal.SnakyRows014.namedCellKey).getLast? = some (-391 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_26 : List Cell := Internal.SnakyRows014.named_envelope_612_27 ++ Internal.SnakyRows014.named_envelope_612_28
theorem Internal.SnakyRows014.named_envelope_612_26_chain : (named_envelope_612_26.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_27 Internal.SnakyRows014.named_envelope_612_28 (-520 : ℤ) (-519 : ℤ)
    Internal.SnakyRows014.named_envelope_612_27_chain Internal.SnakyRows014.named_envelope_612_28_chain Internal.SnakyRows014.named_envelope_612_27_last Internal.SnakyRows014.named_envelope_612_28_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_26_head : (named_envelope_612_26.map Internal.SnakyRows014.namedCellKey).head? = some (-642 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_27 Internal.SnakyRows014.named_envelope_612_28 (-642 : ℤ) Internal.SnakyRows014.named_envelope_612_27_head
theorem Internal.SnakyRows014.named_envelope_612_26_last : (named_envelope_612_26.map Internal.SnakyRows014.namedCellKey).getLast? = some (-391 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_27 Internal.SnakyRows014.named_envelope_612_28 (-391 : ℤ) Internal.SnakyRows014.named_envelope_612_28_last
def Internal.SnakyRows014.named_envelope_612_30 : List Cell := ([(-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -8), (-2, -7)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_30_chain : (named_envelope_612_30.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_30_head : (named_envelope_612_30.map Internal.SnakyRows014.namedCellKey).head? = some (-390 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_30_last : (named_envelope_612_30.map Internal.SnakyRows014.namedCellKey).getLast? = some (-263 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_31 : List Cell := ([(-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_31_chain : (named_envelope_612_31.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_31_head : (named_envelope_612_31.map Internal.SnakyRows014.namedCellKey).head? = some (-262 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_31_last : (named_envelope_612_31.map Internal.SnakyRows014.namedCellKey).getLast? = some (-248 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_29 : List Cell := Internal.SnakyRows014.named_envelope_612_30 ++ Internal.SnakyRows014.named_envelope_612_31
theorem Internal.SnakyRows014.named_envelope_612_29_chain : (named_envelope_612_29.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_30 Internal.SnakyRows014.named_envelope_612_31 (-263 : ℤ) (-262 : ℤ)
    Internal.SnakyRows014.named_envelope_612_30_chain Internal.SnakyRows014.named_envelope_612_31_chain Internal.SnakyRows014.named_envelope_612_30_last Internal.SnakyRows014.named_envelope_612_31_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_29_head : (named_envelope_612_29.map Internal.SnakyRows014.namedCellKey).head? = some (-390 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_30 Internal.SnakyRows014.named_envelope_612_31 (-390 : ℤ) Internal.SnakyRows014.named_envelope_612_30_head
theorem Internal.SnakyRows014.named_envelope_612_29_last : (named_envelope_612_29.map Internal.SnakyRows014.namedCellKey).getLast? = some (-248 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_30 Internal.SnakyRows014.named_envelope_612_31 (-248 : ℤ) Internal.SnakyRows014.named_envelope_612_31_last
def Internal.SnakyRows014.named_envelope_612_25 : List Cell := Internal.SnakyRows014.named_envelope_612_26 ++ Internal.SnakyRows014.named_envelope_612_29
theorem Internal.SnakyRows014.named_envelope_612_25_chain : (named_envelope_612_25.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_26 Internal.SnakyRows014.named_envelope_612_29 (-391 : ℤ) (-390 : ℤ)
    Internal.SnakyRows014.named_envelope_612_26_chain Internal.SnakyRows014.named_envelope_612_29_chain Internal.SnakyRows014.named_envelope_612_26_last Internal.SnakyRows014.named_envelope_612_29_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_25_head : (named_envelope_612_25.map Internal.SnakyRows014.namedCellKey).head? = some (-642 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_26 Internal.SnakyRows014.named_envelope_612_29 (-642 : ℤ) Internal.SnakyRows014.named_envelope_612_26_head
theorem Internal.SnakyRows014.named_envelope_612_25_last : (named_envelope_612_25.map Internal.SnakyRows014.namedCellKey).getLast? = some (-248 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_26 Internal.SnakyRows014.named_envelope_612_29 (-248 : ℤ) Internal.SnakyRows014.named_envelope_612_29_last
def Internal.SnakyRows014.named_envelope_612_17 : List Cell := Internal.SnakyRows014.named_envelope_612_18 ++ Internal.SnakyRows014.named_envelope_612_25
theorem Internal.SnakyRows014.named_envelope_612_17_chain : (named_envelope_612_17.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_18 Internal.SnakyRows014.named_envelope_612_25 (-643 : ℤ) (-642 : ℤ)
    Internal.SnakyRows014.named_envelope_612_18_chain Internal.SnakyRows014.named_envelope_612_25_chain Internal.SnakyRows014.named_envelope_612_18_last Internal.SnakyRows014.named_envelope_612_25_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_17_head : (named_envelope_612_17.map Internal.SnakyRows014.namedCellKey).head? = some (-1027 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_18 Internal.SnakyRows014.named_envelope_612_25 (-1027 : ℤ) Internal.SnakyRows014.named_envelope_612_18_head
theorem Internal.SnakyRows014.named_envelope_612_17_last : (named_envelope_612_17.map Internal.SnakyRows014.namedCellKey).getLast? = some (-248 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_18 Internal.SnakyRows014.named_envelope_612_25 (-248 : ℤ) Internal.SnakyRows014.named_envelope_612_25_last
def Internal.SnakyRows014.named_envelope_612_1 : List Cell := Internal.SnakyRows014.named_envelope_612_2 ++ Internal.SnakyRows014.named_envelope_612_17
theorem Internal.SnakyRows014.named_envelope_612_1_chain : (named_envelope_612_1.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_2 Internal.SnakyRows014.named_envelope_612_17 (-1028 : ℤ) (-1027 : ℤ)
    Internal.SnakyRows014.named_envelope_612_2_chain Internal.SnakyRows014.named_envelope_612_17_chain Internal.SnakyRows014.named_envelope_612_2_last Internal.SnakyRows014.named_envelope_612_17_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_1_head : (named_envelope_612_1.map Internal.SnakyRows014.namedCellKey).head? = some (-2176 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_2 Internal.SnakyRows014.named_envelope_612_17 (-2176 : ℤ) Internal.SnakyRows014.named_envelope_612_2_head
theorem Internal.SnakyRows014.named_envelope_612_1_last : (named_envelope_612_1.map Internal.SnakyRows014.namedCellKey).getLast? = some (-248 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_2 Internal.SnakyRows014.named_envelope_612_17 (-248 : ℤ) Internal.SnakyRows014.named_envelope_612_17_last
def Internal.SnakyRows014.named_envelope_612_36 : List Cell := ([(-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_36_chain : (named_envelope_612_36.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_36_head : (named_envelope_612_36.map Internal.SnakyRows014.namedCellKey).head? = some (-136 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_36_last : (named_envelope_612_36.map Internal.SnakyRows014.namedCellKey).getLast? = some (-123 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_37 : List Cell := ([(-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_37_chain : (named_envelope_612_37.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_37_head : (named_envelope_612_37.map Internal.SnakyRows014.namedCellKey).head? = some (-122 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_37_last : (named_envelope_612_37.map Internal.SnakyRows014.namedCellKey).getLast? = some (5 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_35 : List Cell := Internal.SnakyRows014.named_envelope_612_36 ++ Internal.SnakyRows014.named_envelope_612_37
theorem Internal.SnakyRows014.named_envelope_612_35_chain : (named_envelope_612_35.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_36 Internal.SnakyRows014.named_envelope_612_37 (-123 : ℤ) (-122 : ℤ)
    Internal.SnakyRows014.named_envelope_612_36_chain Internal.SnakyRows014.named_envelope_612_37_chain Internal.SnakyRows014.named_envelope_612_36_last Internal.SnakyRows014.named_envelope_612_37_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_35_head : (named_envelope_612_35.map Internal.SnakyRows014.namedCellKey).head? = some (-136 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_36 Internal.SnakyRows014.named_envelope_612_37 (-136 : ℤ) Internal.SnakyRows014.named_envelope_612_36_head
theorem Internal.SnakyRows014.named_envelope_612_35_last : (named_envelope_612_35.map Internal.SnakyRows014.namedCellKey).getLast? = some (5 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_36 Internal.SnakyRows014.named_envelope_612_37 (5 : ℤ) Internal.SnakyRows014.named_envelope_612_37_last
def Internal.SnakyRows014.named_envelope_612_39 : List Cell := ([(0, 6), (0, 7), (0, 8), (1, -5), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_39_chain : (named_envelope_612_39.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_39_head : (named_envelope_612_39.map Internal.SnakyRows014.namedCellKey).head? = some (6 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_39_last : (named_envelope_612_39.map Internal.SnakyRows014.namedCellKey).getLast? = some (133 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_40 : List Cell := ([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_40_chain : (named_envelope_612_40.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_40_head : (named_envelope_612_40.map Internal.SnakyRows014.namedCellKey).head? = some (134 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_40_last : (named_envelope_612_40.map Internal.SnakyRows014.namedCellKey).getLast? = some (257 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_38 : List Cell := Internal.SnakyRows014.named_envelope_612_39 ++ Internal.SnakyRows014.named_envelope_612_40
theorem Internal.SnakyRows014.named_envelope_612_38_chain : (named_envelope_612_38.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_39 Internal.SnakyRows014.named_envelope_612_40 (133 : ℤ) (134 : ℤ)
    Internal.SnakyRows014.named_envelope_612_39_chain Internal.SnakyRows014.named_envelope_612_40_chain Internal.SnakyRows014.named_envelope_612_39_last Internal.SnakyRows014.named_envelope_612_40_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_38_head : (named_envelope_612_38.map Internal.SnakyRows014.namedCellKey).head? = some (6 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_39 Internal.SnakyRows014.named_envelope_612_40 (6 : ℤ) Internal.SnakyRows014.named_envelope_612_39_head
theorem Internal.SnakyRows014.named_envelope_612_38_last : (named_envelope_612_38.map Internal.SnakyRows014.namedCellKey).getLast? = some (257 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_39 Internal.SnakyRows014.named_envelope_612_40 (257 : ℤ) Internal.SnakyRows014.named_envelope_612_40_last
def Internal.SnakyRows014.named_envelope_612_34 : List Cell := Internal.SnakyRows014.named_envelope_612_35 ++ Internal.SnakyRows014.named_envelope_612_38
theorem Internal.SnakyRows014.named_envelope_612_34_chain : (named_envelope_612_34.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_35 Internal.SnakyRows014.named_envelope_612_38 (5 : ℤ) (6 : ℤ)
    Internal.SnakyRows014.named_envelope_612_35_chain Internal.SnakyRows014.named_envelope_612_38_chain Internal.SnakyRows014.named_envelope_612_35_last Internal.SnakyRows014.named_envelope_612_38_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_34_head : (named_envelope_612_34.map Internal.SnakyRows014.namedCellKey).head? = some (-136 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_35 Internal.SnakyRows014.named_envelope_612_38 (-136 : ℤ) Internal.SnakyRows014.named_envelope_612_35_head
theorem Internal.SnakyRows014.named_envelope_612_34_last : (named_envelope_612_34.map Internal.SnakyRows014.namedCellKey).getLast? = some (257 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_35 Internal.SnakyRows014.named_envelope_612_38 (257 : ℤ) Internal.SnakyRows014.named_envelope_612_38_last
def Internal.SnakyRows014.named_envelope_612_43 : List Cell := ([(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_43_chain : (named_envelope_612_43.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_43_head : (named_envelope_612_43.map Internal.SnakyRows014.namedCellKey).head? = some (258 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_43_last : (named_envelope_612_43.map Internal.SnakyRows014.namedCellKey).getLast? = some (381 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_44 : List Cell := ([(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_44_chain : (named_envelope_612_44.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_44_head : (named_envelope_612_44.map Internal.SnakyRows014.namedCellKey).head? = some (382 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_44_last : (named_envelope_612_44.map Internal.SnakyRows014.namedCellKey).getLast? = some (394 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_42 : List Cell := Internal.SnakyRows014.named_envelope_612_43 ++ Internal.SnakyRows014.named_envelope_612_44
theorem Internal.SnakyRows014.named_envelope_612_42_chain : (named_envelope_612_42.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_43 Internal.SnakyRows014.named_envelope_612_44 (381 : ℤ) (382 : ℤ)
    Internal.SnakyRows014.named_envelope_612_43_chain Internal.SnakyRows014.named_envelope_612_44_chain Internal.SnakyRows014.named_envelope_612_43_last Internal.SnakyRows014.named_envelope_612_44_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_42_head : (named_envelope_612_42.map Internal.SnakyRows014.namedCellKey).head? = some (258 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_43 Internal.SnakyRows014.named_envelope_612_44 (258 : ℤ) Internal.SnakyRows014.named_envelope_612_43_head
theorem Internal.SnakyRows014.named_envelope_612_42_last : (named_envelope_612_42.map Internal.SnakyRows014.namedCellKey).getLast? = some (394 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_43 Internal.SnakyRows014.named_envelope_612_44 (394 : ℤ) Internal.SnakyRows014.named_envelope_612_44_last
def Internal.SnakyRows014.named_envelope_612_46 : List Cell := ([(3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_46_chain : (named_envelope_612_46.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_46_head : (named_envelope_612_46.map Internal.SnakyRows014.namedCellKey).head? = some (395 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_46_last : (named_envelope_612_46.map Internal.SnakyRows014.namedCellKey).getLast? = some (517 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_47 : List Cell := ([(4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_47_chain : (named_envelope_612_47.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_47_head : (named_envelope_612_47.map Internal.SnakyRows014.namedCellKey).head? = some (518 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_47_last : (named_envelope_612_47.map Internal.SnakyRows014.namedCellKey).getLast? = some (643 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_45 : List Cell := Internal.SnakyRows014.named_envelope_612_46 ++ Internal.SnakyRows014.named_envelope_612_47
theorem Internal.SnakyRows014.named_envelope_612_45_chain : (named_envelope_612_45.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_46 Internal.SnakyRows014.named_envelope_612_47 (517 : ℤ) (518 : ℤ)
    Internal.SnakyRows014.named_envelope_612_46_chain Internal.SnakyRows014.named_envelope_612_47_chain Internal.SnakyRows014.named_envelope_612_46_last Internal.SnakyRows014.named_envelope_612_47_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_45_head : (named_envelope_612_45.map Internal.SnakyRows014.namedCellKey).head? = some (395 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_46 Internal.SnakyRows014.named_envelope_612_47 (395 : ℤ) Internal.SnakyRows014.named_envelope_612_46_head
theorem Internal.SnakyRows014.named_envelope_612_45_last : (named_envelope_612_45.map Internal.SnakyRows014.namedCellKey).getLast? = some (643 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_46 Internal.SnakyRows014.named_envelope_612_47 (643 : ℤ) Internal.SnakyRows014.named_envelope_612_47_last
def Internal.SnakyRows014.named_envelope_612_41 : List Cell := Internal.SnakyRows014.named_envelope_612_42 ++ Internal.SnakyRows014.named_envelope_612_45
theorem Internal.SnakyRows014.named_envelope_612_41_chain : (named_envelope_612_41.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_42 Internal.SnakyRows014.named_envelope_612_45 (394 : ℤ) (395 : ℤ)
    Internal.SnakyRows014.named_envelope_612_42_chain Internal.SnakyRows014.named_envelope_612_45_chain Internal.SnakyRows014.named_envelope_612_42_last Internal.SnakyRows014.named_envelope_612_45_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_41_head : (named_envelope_612_41.map Internal.SnakyRows014.namedCellKey).head? = some (258 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_42 Internal.SnakyRows014.named_envelope_612_45 (258 : ℤ) Internal.SnakyRows014.named_envelope_612_42_head
theorem Internal.SnakyRows014.named_envelope_612_41_last : (named_envelope_612_41.map Internal.SnakyRows014.namedCellKey).getLast? = some (643 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_42 Internal.SnakyRows014.named_envelope_612_45 (643 : ℤ) Internal.SnakyRows014.named_envelope_612_45_last
def Internal.SnakyRows014.named_envelope_612_33 : List Cell := Internal.SnakyRows014.named_envelope_612_34 ++ Internal.SnakyRows014.named_envelope_612_41
theorem Internal.SnakyRows014.named_envelope_612_33_chain : (named_envelope_612_33.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_34 Internal.SnakyRows014.named_envelope_612_41 (257 : ℤ) (258 : ℤ)
    Internal.SnakyRows014.named_envelope_612_34_chain Internal.SnakyRows014.named_envelope_612_41_chain Internal.SnakyRows014.named_envelope_612_34_last Internal.SnakyRows014.named_envelope_612_41_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_33_head : (named_envelope_612_33.map Internal.SnakyRows014.namedCellKey).head? = some (-136 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_34 Internal.SnakyRows014.named_envelope_612_41 (-136 : ℤ) Internal.SnakyRows014.named_envelope_612_34_head
theorem Internal.SnakyRows014.named_envelope_612_33_last : (named_envelope_612_33.map Internal.SnakyRows014.namedCellKey).getLast? = some (643 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_34 Internal.SnakyRows014.named_envelope_612_41 (643 : ℤ) Internal.SnakyRows014.named_envelope_612_41_last
def Internal.SnakyRows014.named_envelope_612_51 : List Cell := ([(5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_51_chain : (named_envelope_612_51.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_51_head : (named_envelope_612_51.map Internal.SnakyRows014.namedCellKey).head? = some (644 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_51_last : (named_envelope_612_51.map Internal.SnakyRows014.namedCellKey).getLast? = some (766 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_52 : List Cell := ([(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_52_chain : (named_envelope_612_52.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_52_head : (named_envelope_612_52.map Internal.SnakyRows014.namedCellKey).head? = some (767 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_52_last : (named_envelope_612_52.map Internal.SnakyRows014.namedCellKey).getLast? = some (890 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_50 : List Cell := Internal.SnakyRows014.named_envelope_612_51 ++ Internal.SnakyRows014.named_envelope_612_52
theorem Internal.SnakyRows014.named_envelope_612_50_chain : (named_envelope_612_50.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_51 Internal.SnakyRows014.named_envelope_612_52 (766 : ℤ) (767 : ℤ)
    Internal.SnakyRows014.named_envelope_612_51_chain Internal.SnakyRows014.named_envelope_612_52_chain Internal.SnakyRows014.named_envelope_612_51_last Internal.SnakyRows014.named_envelope_612_52_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_50_head : (named_envelope_612_50.map Internal.SnakyRows014.namedCellKey).head? = some (644 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_51 Internal.SnakyRows014.named_envelope_612_52 (644 : ℤ) Internal.SnakyRows014.named_envelope_612_51_head
theorem Internal.SnakyRows014.named_envelope_612_50_last : (named_envelope_612_50.map Internal.SnakyRows014.namedCellKey).getLast? = some (890 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_51 Internal.SnakyRows014.named_envelope_612_52 (890 : ℤ) Internal.SnakyRows014.named_envelope_612_52_last
def Internal.SnakyRows014.named_envelope_612_54 : List Cell := ([(7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_54_chain : (named_envelope_612_54.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_54_head : (named_envelope_612_54.map Internal.SnakyRows014.namedCellKey).head? = some (891 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_54_last : (named_envelope_612_54.map Internal.SnakyRows014.namedCellKey).getLast? = some (902 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_55 : List Cell := ([(7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_55_chain : (named_envelope_612_55.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_55_head : (named_envelope_612_55.map Internal.SnakyRows014.namedCellKey).head? = some (903 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_55_last : (named_envelope_612_55.map Internal.SnakyRows014.namedCellKey).getLast? = some (1027 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_53 : List Cell := Internal.SnakyRows014.named_envelope_612_54 ++ Internal.SnakyRows014.named_envelope_612_55
theorem Internal.SnakyRows014.named_envelope_612_53_chain : (named_envelope_612_53.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_54 Internal.SnakyRows014.named_envelope_612_55 (902 : ℤ) (903 : ℤ)
    Internal.SnakyRows014.named_envelope_612_54_chain Internal.SnakyRows014.named_envelope_612_55_chain Internal.SnakyRows014.named_envelope_612_54_last Internal.SnakyRows014.named_envelope_612_55_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_53_head : (named_envelope_612_53.map Internal.SnakyRows014.namedCellKey).head? = some (891 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_54 Internal.SnakyRows014.named_envelope_612_55 (891 : ℤ) Internal.SnakyRows014.named_envelope_612_54_head
theorem Internal.SnakyRows014.named_envelope_612_53_last : (named_envelope_612_53.map Internal.SnakyRows014.namedCellKey).getLast? = some (1027 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_54 Internal.SnakyRows014.named_envelope_612_55 (1027 : ℤ) Internal.SnakyRows014.named_envelope_612_55_last
def Internal.SnakyRows014.named_envelope_612_49 : List Cell := Internal.SnakyRows014.named_envelope_612_50 ++ Internal.SnakyRows014.named_envelope_612_53
theorem Internal.SnakyRows014.named_envelope_612_49_chain : (named_envelope_612_49.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_50 Internal.SnakyRows014.named_envelope_612_53 (890 : ℤ) (891 : ℤ)
    Internal.SnakyRows014.named_envelope_612_50_chain Internal.SnakyRows014.named_envelope_612_53_chain Internal.SnakyRows014.named_envelope_612_50_last Internal.SnakyRows014.named_envelope_612_53_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_49_head : (named_envelope_612_49.map Internal.SnakyRows014.namedCellKey).head? = some (644 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_50 Internal.SnakyRows014.named_envelope_612_53 (644 : ℤ) Internal.SnakyRows014.named_envelope_612_50_head
theorem Internal.SnakyRows014.named_envelope_612_49_last : (named_envelope_612_49.map Internal.SnakyRows014.namedCellKey).getLast? = some (1027 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_50 Internal.SnakyRows014.named_envelope_612_53 (1027 : ℤ) Internal.SnakyRows014.named_envelope_612_53_last
def Internal.SnakyRows014.named_envelope_612_58 : List Cell := ([(8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_58_chain : (named_envelope_612_58.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_58_head : (named_envelope_612_58.map Internal.SnakyRows014.namedCellKey).head? = some (1028 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_58_last : (named_envelope_612_58.map Internal.SnakyRows014.namedCellKey).getLast? = some (1152 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_59 : List Cell := ([(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_59_chain : (named_envelope_612_59.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_59_head : (named_envelope_612_59.map Internal.SnakyRows014.namedCellKey).head? = some (1153 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_59_last : (named_envelope_612_59.map Internal.SnakyRows014.namedCellKey).getLast? = some (1281 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_57 : List Cell := Internal.SnakyRows014.named_envelope_612_58 ++ Internal.SnakyRows014.named_envelope_612_59
theorem Internal.SnakyRows014.named_envelope_612_57_chain : (named_envelope_612_57.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_58 Internal.SnakyRows014.named_envelope_612_59 (1152 : ℤ) (1153 : ℤ)
    Internal.SnakyRows014.named_envelope_612_58_chain Internal.SnakyRows014.named_envelope_612_59_chain Internal.SnakyRows014.named_envelope_612_58_last Internal.SnakyRows014.named_envelope_612_59_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_57_head : (named_envelope_612_57.map Internal.SnakyRows014.namedCellKey).head? = some (1028 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_58 Internal.SnakyRows014.named_envelope_612_59 (1028 : ℤ) Internal.SnakyRows014.named_envelope_612_58_head
theorem Internal.SnakyRows014.named_envelope_612_57_last : (named_envelope_612_57.map Internal.SnakyRows014.namedCellKey).getLast? = some (1281 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_58 Internal.SnakyRows014.named_envelope_612_59 (1281 : ℤ) Internal.SnakyRows014.named_envelope_612_59_last
def Internal.SnakyRows014.named_envelope_612_61 : List Cell := ([(10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_61_chain : (named_envelope_612_61.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_61_head : (named_envelope_612_61.map Internal.SnakyRows014.namedCellKey).head? = some (1282 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_61_last : (named_envelope_612_61.map Internal.SnakyRows014.namedCellKey).getLast? = some (1412 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_62 : List Cell := ([(12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)] : List Cell)
theorem Internal.SnakyRows014.named_envelope_612_62_chain : (named_envelope_612_62.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows014.named_envelope_612_62_head : (named_envelope_612_62.map Internal.SnakyRows014.namedCellKey).head? = some (1532 : ℤ) := by decide
theorem Internal.SnakyRows014.named_envelope_612_62_last : (named_envelope_612_62.map Internal.SnakyRows014.namedCellKey).getLast? = some (1792 : ℤ) := by decide
def Internal.SnakyRows014.named_envelope_612_60 : List Cell := Internal.SnakyRows014.named_envelope_612_61 ++ Internal.SnakyRows014.named_envelope_612_62
theorem Internal.SnakyRows014.named_envelope_612_60_chain : (named_envelope_612_60.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_61 Internal.SnakyRows014.named_envelope_612_62 (1412 : ℤ) (1532 : ℤ)
    Internal.SnakyRows014.named_envelope_612_61_chain Internal.SnakyRows014.named_envelope_612_62_chain Internal.SnakyRows014.named_envelope_612_61_last Internal.SnakyRows014.named_envelope_612_62_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_60_head : (named_envelope_612_60.map Internal.SnakyRows014.namedCellKey).head? = some (1282 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_61 Internal.SnakyRows014.named_envelope_612_62 (1282 : ℤ) Internal.SnakyRows014.named_envelope_612_61_head
theorem Internal.SnakyRows014.named_envelope_612_60_last : (named_envelope_612_60.map Internal.SnakyRows014.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_61 Internal.SnakyRows014.named_envelope_612_62 (1792 : ℤ) Internal.SnakyRows014.named_envelope_612_62_last
def Internal.SnakyRows014.named_envelope_612_56 : List Cell := Internal.SnakyRows014.named_envelope_612_57 ++ Internal.SnakyRows014.named_envelope_612_60
theorem Internal.SnakyRows014.named_envelope_612_56_chain : (named_envelope_612_56.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_57 Internal.SnakyRows014.named_envelope_612_60 (1281 : ℤ) (1282 : ℤ)
    Internal.SnakyRows014.named_envelope_612_57_chain Internal.SnakyRows014.named_envelope_612_60_chain Internal.SnakyRows014.named_envelope_612_57_last Internal.SnakyRows014.named_envelope_612_60_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_56_head : (named_envelope_612_56.map Internal.SnakyRows014.namedCellKey).head? = some (1028 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_57 Internal.SnakyRows014.named_envelope_612_60 (1028 : ℤ) Internal.SnakyRows014.named_envelope_612_57_head
theorem Internal.SnakyRows014.named_envelope_612_56_last : (named_envelope_612_56.map Internal.SnakyRows014.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_57 Internal.SnakyRows014.named_envelope_612_60 (1792 : ℤ) Internal.SnakyRows014.named_envelope_612_60_last
def Internal.SnakyRows014.named_envelope_612_48 : List Cell := Internal.SnakyRows014.named_envelope_612_49 ++ Internal.SnakyRows014.named_envelope_612_56
theorem Internal.SnakyRows014.named_envelope_612_48_chain : (named_envelope_612_48.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_49 Internal.SnakyRows014.named_envelope_612_56 (1027 : ℤ) (1028 : ℤ)
    Internal.SnakyRows014.named_envelope_612_49_chain Internal.SnakyRows014.named_envelope_612_56_chain Internal.SnakyRows014.named_envelope_612_49_last Internal.SnakyRows014.named_envelope_612_56_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_48_head : (named_envelope_612_48.map Internal.SnakyRows014.namedCellKey).head? = some (644 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_49 Internal.SnakyRows014.named_envelope_612_56 (644 : ℤ) Internal.SnakyRows014.named_envelope_612_49_head
theorem Internal.SnakyRows014.named_envelope_612_48_last : (named_envelope_612_48.map Internal.SnakyRows014.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_49 Internal.SnakyRows014.named_envelope_612_56 (1792 : ℤ) Internal.SnakyRows014.named_envelope_612_56_last
def Internal.SnakyRows014.named_envelope_612_32 : List Cell := Internal.SnakyRows014.named_envelope_612_33 ++ Internal.SnakyRows014.named_envelope_612_48
theorem Internal.SnakyRows014.named_envelope_612_32_chain : (named_envelope_612_32.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_33 Internal.SnakyRows014.named_envelope_612_48 (643 : ℤ) (644 : ℤ)
    Internal.SnakyRows014.named_envelope_612_33_chain Internal.SnakyRows014.named_envelope_612_48_chain Internal.SnakyRows014.named_envelope_612_33_last Internal.SnakyRows014.named_envelope_612_48_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_32_head : (named_envelope_612_32.map Internal.SnakyRows014.namedCellKey).head? = some (-136 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_33 Internal.SnakyRows014.named_envelope_612_48 (-136 : ℤ) Internal.SnakyRows014.named_envelope_612_33_head
theorem Internal.SnakyRows014.named_envelope_612_32_last : (named_envelope_612_32.map Internal.SnakyRows014.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_33 Internal.SnakyRows014.named_envelope_612_48 (1792 : ℤ) Internal.SnakyRows014.named_envelope_612_48_last
def Internal.SnakyRows014.named_envelope_612_0 : List Cell := Internal.SnakyRows014.named_envelope_612_1 ++ Internal.SnakyRows014.named_envelope_612_32
theorem Internal.SnakyRows014.named_envelope_612_0_chain : (named_envelope_612_0.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows014.named_chain_append Internal.SnakyRows014.named_envelope_612_1 Internal.SnakyRows014.named_envelope_612_32 (-248 : ℤ) (-136 : ℤ)
    Internal.SnakyRows014.named_envelope_612_1_chain Internal.SnakyRows014.named_envelope_612_32_chain Internal.SnakyRows014.named_envelope_612_1_last Internal.SnakyRows014.named_envelope_612_32_head (by decide)
theorem Internal.SnakyRows014.named_envelope_612_0_head : (named_envelope_612_0.map Internal.SnakyRows014.namedCellKey).head? = some (-2176 : ℤ) :=
  Internal.SnakyRows014.named_head_append Internal.SnakyRows014.named_envelope_612_1 Internal.SnakyRows014.named_envelope_612_32 (-2176 : ℤ) Internal.SnakyRows014.named_envelope_612_1_head
theorem Internal.SnakyRows014.named_envelope_612_0_last : (named_envelope_612_0.map Internal.SnakyRows014.namedCellKey).getLast? = some (1792 : ℤ) :=
  Internal.SnakyRows014.named_last_append Internal.SnakyRows014.named_envelope_612_1 Internal.SnakyRows014.named_envelope_612_32 (1792 : ℤ) Internal.SnakyRows014.named_envelope_612_32_last
theorem Internal.SnakyRows014.named_envelope_612_nodup : (Internal.SnakyRows014.named_envelope_612_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows014.named_nodup_of_chain Internal.SnakyRows014.named_envelope_612_0 Internal.SnakyRows014.named_envelope_612_0_chain
def envelope_612 : Finset Cell := ⟨(Internal.SnakyRows014.named_envelope_612_0 : Multiset Cell), Internal.SnakyRows014.named_envelope_612_nodup⟩
def childrenC_612 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) required_589), (placedSet 7 (-4, -1) required_589)]
def childrenD_612 : Fin 2 → Finset Cell := ![(placedSet 1 (1, 1) envelope_589), (placedSet 7 (-4, -1) envelope_589)]
theorem Internal.SnakyRows014.commonEnvelope_subset_of_child_escape {n : ℕ}
    (D : Fin (n + 1) → Finset Cell) (H : Finset Cell) (j0 : Fin (n + 1))
    (h : ∀ q ∈ D j0, q ∈ H ∨ ∃ j, q ∉ D j) :
    commonEnvelope D ⊆ H := by
  intro q hq
  have hq' : q ∈ D 0 ∧ ∀ j, q ∈ D j := Finset.mem_filter.mp hq
  rcases h q (hq'.2 j0) with howned | ⟨j, hmissing⟩
  · exact howned
  · exact False.elim (hmissing (hq'.2 j))
theorem Internal.SnakyRows014.commonEnvelope_subset_of_placed_child_escape {n : ℕ}
    (D : Fin (n + 1) → Finset Cell) (H A : Finset Cell)
    (j0 : Fin (n + 1)) (r : Fin 8) (t : Cell)
    (h0 : D j0 = placedSet r t A)
    (h : ∀ p ∈ A,
      placement r t p ∈ H ∨ ∃ j, placement r t p ∉ D j) :
    commonEnvelope D ⊆ H := by
  apply Internal.SnakyRows014.commonEnvelope_subset_of_child_escape D H j0
  intro q hq
  rw [h0] at hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  change placement r t p = q at hpq
  rw [← hpq]
  exact h p hp
theorem Internal.SnakyRows014.common_auto_612_point_000 :
    placement 1 (1, 1) (-7, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-7, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_001 :
    placement 1 (1, 1) (-7, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-7, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_002 :
    placement 1 (1, 1) (-7, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-7, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_003 :
    placement 1 (1, 1) (-6, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-6, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_004 :
    placement 1 (1, 1) (-6, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-6, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_005 :
    placement 1 (1, 1) (-6, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-6, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_006 :
    placement 1 (1, 1) (-6, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-6, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_007 :
    placement 1 (1, 1) (-6, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-6, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_008 :
    placement 1 (1, 1) (-5, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_009 :
    placement 1 (1, 1) (-5, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_010 :
    placement 1 (1, 1) (-5, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_011 :
    placement 1 (1, 1) (-5, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_012 :
    placement 1 (1, 1) (-5, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_013 :
    placement 1 (1, 1) (-5, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_014 :
    placement 1 (1, 1) (-5, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_015 :
    placement 1 (1, 1) (-5, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_016 :
    placement 1 (1, 1) (-5, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_017 :
    placement 1 (1, 1) (-5, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_018 :
    placement 1 (1, 1) (-5, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-5, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_019 :
    placement 1 (1, 1) (-4, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_020 :
    placement 1 (1, 1) (-4, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_021 :
    placement 1 (1, 1) (-4, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_022 :
    placement 1 (1, 1) (-4, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_023 :
    placement 1 (1, 1) (-4, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_024 :
    placement 1 (1, 1) (-4, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_025 :
    placement 1 (1, 1) (-4, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_026 :
    placement 1 (1, 1) (-4, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_027 :
    placement 1 (1, 1) (-4, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_028 :
    placement 1 (1, 1) (-4, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-4, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_029 :
    placement 1 (1, 1) (-3, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_030 :
    placement 1 (1, 1) (-3, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_031 :
    placement 1 (1, 1) (-3, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_032 :
    placement 1 (1, 1) (-3, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_033 :
    placement 1 (1, 1) (-3, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_034 :
    placement 1 (1, 1) (-3, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_035 :
    placement 1 (1, 1) (-3, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_036 :
    placement 1 (1, 1) (-3, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_037 :
    placement 1 (1, 1) (-3, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_038 :
    placement 1 (1, 1) (-3, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_039 :
    placement 1 (1, 1) (-3, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_040 :
    placement 1 (1, 1) (-3, 12) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 12) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_041 :
    placement 1 (1, 1) (-3, 13) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-3, 13) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_042 :
    placement 1 (1, 1) (-2, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_043 :
    placement 1 (1, 1) (-2, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_044 :
    placement 1 (1, 1) (-2, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_045 :
    placement 1 (1, 1) (-2, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_046 :
    placement 1 (1, 1) (-2, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_047 :
    placement 1 (1, 1) (-2, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_048 :
    placement 1 (1, 1) (-2, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_049 :
    placement 1 (1, 1) (-2, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_050 :
    placement 1 (1, 1) (-2, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_051 :
    placement 1 (1, 1) (-2, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_052 :
    placement 1 (1, 1) (-2, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_053 :
    placement 1 (1, 1) (-2, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_054 :
    placement 1 (1, 1) (-2, 12) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-2, 12) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_055 :
    placement 1 (1, 1) (-1, -4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, -4) ∉ childrenD_612 j := by
  exact Or.inl (by decide)
theorem Internal.SnakyRows014.common_auto_612_point_056 :
    placement 1 (1, 1) (-1, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, -3) ∉ childrenD_612 j := by
  exact Or.inl (by decide)
theorem Internal.SnakyRows014.common_auto_612_point_057 :
    placement 1 (1, 1) (-1, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, -2) ∉ childrenD_612 j := by
  exact Or.inl (by decide)
theorem Internal.SnakyRows014.common_auto_612_point_058 :
    placement 1 (1, 1) (-1, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, -1) ∉ childrenD_612 j := by
  exact Or.inl (by decide)
theorem Internal.SnakyRows014.common_auto_612_point_059 :
    placement 1 (1, 1) (-1, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_060 :
    placement 1 (1, 1) (-1, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_061 :
    placement 1 (1, 1) (-1, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_062 :
    placement 1 (1, 1) (-1, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_063 :
    placement 1 (1, 1) (-1, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_064 :
    placement 1 (1, 1) (-1, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_065 :
    placement 1 (1, 1) (-1, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_066 :
    placement 1 (1, 1) (-1, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_067 :
    placement 1 (1, 1) (-1, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_068 :
    placement 1 (1, 1) (-1, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_069 :
    placement 1 (1, 1) (-1, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_070 :
    placement 1 (1, 1) (-1, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_071 :
    placement 1 (1, 1) (-1, 12) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 12) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_072 :
    placement 1 (1, 1) (-1, 13) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (-1, 13) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_073 :
    placement 1 (1, 1) (0, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_074 :
    placement 1 (1, 1) (0, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_075 :
    placement 1 (1, 1) (0, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_076 :
    placement 1 (1, 1) (0, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_077 :
    placement 1 (1, 1) (0, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_078 :
    placement 1 (1, 1) (0, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_079 :
    placement 1 (1, 1) (0, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_080 :
    placement 1 (1, 1) (0, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_081 :
    placement 1 (1, 1) (0, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_082 :
    placement 1 (1, 1) (0, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_083 :
    placement 1 (1, 1) (0, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_084 :
    placement 1 (1, 1) (0, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_085 :
    placement 1 (1, 1) (0, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (0, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_086 :
    placement 1 (1, 1) (1, -4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, -4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_087 :
    placement 1 (1, 1) (1, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, -3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_088 :
    placement 1 (1, 1) (1, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, -2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_089 :
    placement 1 (1, 1) (1, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_090 :
    placement 1 (1, 1) (1, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_091 :
    placement 1 (1, 1) (1, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_092 :
    placement 1 (1, 1) (1, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_093 :
    placement 1 (1, 1) (1, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_094 :
    placement 1 (1, 1) (1, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_095 :
    placement 1 (1, 1) (1, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_096 :
    placement 1 (1, 1) (1, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_097 :
    placement 1 (1, 1) (1, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_098 :
    placement 1 (1, 1) (1, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_099 :
    placement 1 (1, 1) (1, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_100 :
    placement 1 (1, 1) (1, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_101 :
    placement 1 (1, 1) (1, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (1, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_102 :
    placement 1 (1, 1) (2, -5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, -5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_103 :
    placement 1 (1, 1) (2, -4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, -4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_104 :
    placement 1 (1, 1) (2, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, -3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_105 :
    placement 1 (1, 1) (2, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, -2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_106 :
    placement 1 (1, 1) (2, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_107 :
    placement 1 (1, 1) (2, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_108 :
    placement 1 (1, 1) (2, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_109 :
    placement 1 (1, 1) (2, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_110 :
    placement 1 (1, 1) (2, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_111 :
    placement 1 (1, 1) (2, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_112 :
    placement 1 (1, 1) (2, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_113 :
    placement 1 (1, 1) (2, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_114 :
    placement 1 (1, 1) (2, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_115 :
    placement 1 (1, 1) (2, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_116 :
    placement 1 (1, 1) (2, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_117 :
    placement 1 (1, 1) (2, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_118 :
    placement 1 (1, 1) (2, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (2, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_119 :
    placement 1 (1, 1) (3, -4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, -4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_120 :
    placement 1 (1, 1) (3, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, -3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_121 :
    placement 1 (1, 1) (3, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, -2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_122 :
    placement 1 (1, 1) (3, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_123 :
    placement 1 (1, 1) (3, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_124 :
    placement 1 (1, 1) (3, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_125 :
    placement 1 (1, 1) (3, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_126 :
    placement 1 (1, 1) (3, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_127 :
    placement 1 (1, 1) (3, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_128 :
    placement 1 (1, 1) (3, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_129 :
    placement 1 (1, 1) (3, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_130 :
    placement 1 (1, 1) (3, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_131 :
    placement 1 (1, 1) (3, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_132 :
    placement 1 (1, 1) (3, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_133 :
    placement 1 (1, 1) (3, 10) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 10) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_134 :
    placement 1 (1, 1) (3, 11) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (3, 11) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_135 :
    placement 1 (1, 1) (4, -5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, -5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_136 :
    placement 1 (1, 1) (4, -4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, -4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_137 :
    placement 1 (1, 1) (4, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, -3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_138 :
    placement 1 (1, 1) (4, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, -2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_139 :
    placement 1 (1, 1) (4, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_140 :
    placement 1 (1, 1) (4, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_141 :
    placement 1 (1, 1) (4, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_142 :
    placement 1 (1, 1) (4, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_143 :
    placement 1 (1, 1) (4, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_144 :
    placement 1 (1, 1) (4, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_145 :
    placement 1 (1, 1) (4, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_146 :
    placement 1 (1, 1) (4, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_147 :
    placement 1 (1, 1) (4, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_148 :
    placement 1 (1, 1) (4, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_149 :
    placement 1 (1, 1) (4, 9) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (4, 9) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_150 :
    placement 1 (1, 1) (5, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, -3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_151 :
    placement 1 (1, 1) (5, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, -2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_152 :
    placement 1 (1, 1) (5, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_153 :
    placement 1 (1, 1) (5, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_154 :
    placement 1 (1, 1) (5, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_155 :
    placement 1 (1, 1) (5, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_156 :
    placement 1 (1, 1) (5, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_157 :
    placement 1 (1, 1) (5, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_158 :
    placement 1 (1, 1) (5, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_159 :
    placement 1 (1, 1) (5, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_160 :
    placement 1 (1, 1) (5, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_161 :
    placement 1 (1, 1) (5, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (5, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_162 :
    placement 1 (1, 1) (6, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, -3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_163 :
    placement 1 (1, 1) (6, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, -2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_164 :
    placement 1 (1, 1) (6, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_165 :
    placement 1 (1, 1) (6, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_166 :
    placement 1 (1, 1) (6, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_167 :
    placement 1 (1, 1) (6, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_168 :
    placement 1 (1, 1) (6, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_169 :
    placement 1 (1, 1) (6, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_170 :
    placement 1 (1, 1) (6, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_171 :
    placement 1 (1, 1) (6, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_172 :
    placement 1 (1, 1) (6, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_173 :
    placement 1 (1, 1) (6, 8) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (6, 8) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_174 :
    placement 1 (1, 1) (7, -3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, -3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_175 :
    placement 1 (1, 1) (7, -2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, -2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_176 :
    placement 1 (1, 1) (7, -1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, -1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_177 :
    placement 1 (1, 1) (7, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_178 :
    placement 1 (1, 1) (7, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_179 :
    placement 1 (1, 1) (7, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_180 :
    placement 1 (1, 1) (7, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_181 :
    placement 1 (1, 1) (7, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_182 :
    placement 1 (1, 1) (7, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_183 :
    placement 1 (1, 1) (7, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_184 :
    placement 1 (1, 1) (7, 7) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (7, 7) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_185 :
    placement 1 (1, 1) (8, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (8, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_186 :
    placement 1 (1, 1) (8, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (8, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_187 :
    placement 1 (1, 1) (8, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (8, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_188 :
    placement 1 (1, 1) (8, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (8, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_189 :
    placement 1 (1, 1) (8, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (8, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_190 :
    placement 1 (1, 1) (8, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (8, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_191 :
    placement 1 (1, 1) (8, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (8, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_192 :
    placement 1 (1, 1) (9, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (9, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_193 :
    placement 1 (1, 1) (9, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (9, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_194 :
    placement 1 (1, 1) (9, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (9, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_195 :
    placement 1 (1, 1) (9, 3) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (9, 3) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_196 :
    placement 1 (1, 1) (9, 4) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (9, 4) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_197 :
    placement 1 (1, 1) (9, 5) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (9, 5) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_198 :
    placement 1 (1, 1) (9, 6) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (9, 6) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_199 :
    placement 1 (1, 1) (10, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (10, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_200 :
    placement 1 (1, 1) (10, 1) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (10, 1) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_201 :
    placement 1 (1, 1) (10, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (10, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_202 :
    placement 1 (1, 1) (11, 0) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (11, 0) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_point_203 :
    placement 1 (1, 1) (11, 2) ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) (11, 2) ∉ childrenD_612 j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_000 :
    ∀ p ∈ ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_000, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_001, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_002, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_003, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_004, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_005, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_006, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_007, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_008, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_009, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_010, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_011, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_012, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_013, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_014, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_015, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_001 :
    ∀ p ∈ ([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_016, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_017, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_018, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_019, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_020, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_021, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_022, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_023, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_024, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_025, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_026, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_027, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_028, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_029, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_030, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_031, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_002 :
    ∀ p ∈ ([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_032, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_033, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_034, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_035, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_036, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_037, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_038, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_039, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_040, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_041, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_042, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_043, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_044, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_045, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_046, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_047, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_003 :
    ∀ p ∈ ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_048, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_049, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_050, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_051, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_052, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_053, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_054, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_055, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_056, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_057, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_058, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_059, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_060, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_061, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_062, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_063, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_004 :
    ∀ p ∈ ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_064, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_065, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_066, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_067, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_068, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_069, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_070, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_071, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_072, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_073, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_074, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_075, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_076, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_077, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_078, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_079, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_005 :
    ∀ p ∈ ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_080, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_081, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_082, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_083, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_084, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_085, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_086, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_087, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_088, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_089, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_090, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_091, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_092, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_093, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_094, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_095, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_006 :
    ∀ p ∈ ([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_096, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_097, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_098, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_099, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_100, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_101, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_102, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_103, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_104, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_105, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_106, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_107, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_108, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_109, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_110, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_111, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_007 :
    ∀ p ∈ ([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_112, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_113, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_114, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_115, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_116, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_117, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_118, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_119, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_120, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_121, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_122, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_123, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_124, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_125, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_126, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_008 :
    ∀ p ∈ ([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_128, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_129, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_130, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_131, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_132, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_133, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_134, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_135, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_136, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_137, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_138, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_139, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_140, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_141, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_142, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_143, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_009 :
    ∀ p ∈ ([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_144, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_145, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_146, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_147, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_148, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_149, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_150, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_151, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_152, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_153, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_154, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_155, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_156, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_157, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_158, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_010 :
    ∀ p ∈ ([(5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_160, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_161, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_162, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_163, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_164, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_165, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_166, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_167, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_168, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_169, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_170, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_171, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_172, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_173, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_174, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_175, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_011 :
    ∀ p ∈ ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_176, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_177, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_178, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_179, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_180, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_181, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_182, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_183, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_184, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_185, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_186, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_187, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_188, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_189, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_190, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_chunk_012 :
    ∀ p ∈ ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_192, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_193, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_194, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_195, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_196, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_197, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_198, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_199, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_200, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_201, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_202, List.forall_mem_cons.mpr ⟨Internal.SnakyRows014.common_auto_612_point_203, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.common_auto_612_source :
    ∀ p ∈ envelope_589, placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j := by
  change ∀ p ∈ (([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell) ++ (([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell) ++ (([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell) ++ (([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell) ++ (([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell) ++ (([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) ++ (([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell) ++ (([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) ++ (([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) ++ (([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) ++ (([(5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2)] : List Cell) ++ (([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell) ++ ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell))))))))))))), placement 1 (1, 1) p ∈ insert (0, 0) required_612 ∨ ∃ j : Fin 2, placement 1 (1, 1) p ∉ childrenD_612 j
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_000, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_001, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_002, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_003, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_004, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_005, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_006, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_007, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_008, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_009, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_010, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.common_auto_612_chunk_011, Internal.SnakyRows014.common_auto_612_chunk_012⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem common_sub_612 : commonEnvelope childrenD_612 ⊆ insert (0, 0) required_612 := by
  exact Internal.SnakyRows014.commonEnvelope_subset_of_placed_child_escape childrenD_612
    (insert (0, 0) required_612) envelope_589 0 1 (1, 1) rfl Internal.SnakyRows014.common_auto_612_source
theorem child_required_sub_612 : ∀ j, childrenC_612 j ⊆ insert (0, 0) required_612 := by decide
theorem Internal.SnakyRows014.containment_612_0_points_0 :
    ∀ p ∈ ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_1 :
    ∀ p ∈ ([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_2 :
    ∀ p ∈ ([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_3 :
    ∀ p ∈ ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_4 :
    ∀ p ∈ ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_5 :
    ∀ p ∈ ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_6 :
    ∀ p ∈ ([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_7 :
    ∀ p ∈ ([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_8 :
    ∀ p ∈ ([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_9 :
    ∀ p ∈ ([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_10 :
    ∀ p ∈ ([(5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_11 :
    ∀ p ∈ ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0_points_12 :
    ∀ p ∈ ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell), placement 1 (1, 1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_0 :
    placedSet 1 (1, 1) envelope_589 ⊆ envelope_612 := by
  apply Internal.SnakyRows014.placedSet_subset_of_points
  change ∀ p ∈ ((([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell) ++ (([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell) ++ (([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell) ++ (([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell) ++ (([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell) ++ (([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) ++ (([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell) ++ (([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) ++ (([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) ++ (([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) ++ (([(5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2)] : List Cell) ++ (([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell) ++ ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell)))))))))))))), placement 1 (1, 1) p ∈ envelope_612
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_3, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_4, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_5, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_6, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_7, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_8, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_9, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_10, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_0_points_11, Internal.SnakyRows014.containment_612_0_points_12⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_0 :
    ∀ p ∈ ([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_1 :
    ∀ p ∈ ([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_2 :
    ∀ p ∈ ([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_3 :
    ∀ p ∈ ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_4 :
    ∀ p ∈ ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_5 :
    ∀ p ∈ ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_6 :
    ∀ p ∈ ([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_7 :
    ∀ p ∈ ([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_8 :
    ∀ p ∈ ([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_9 :
    ∀ p ∈ ([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_10 :
    ∀ p ∈ ([(5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_11 :
    ∀ p ∈ ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1_points_12 :
    ∀ p ∈ ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell), placement 7 (-4, -1) p ∈ envelope_612 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows014.containment_612_1 :
    placedSet 7 (-4, -1) envelope_589 ⊆ envelope_612 := by
  apply Internal.SnakyRows014.placedSet_subset_of_points
  change ∀ p ∈ ((([(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8)] : List Cell) ++ (([(-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3)] : List Cell) ++ (([(-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell) ++ (([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell) ++ (([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell) ++ (([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) ++ (([(1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell) ++ (([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) ++ (([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) ++ (([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) ++ (([(5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2)] : List Cell) ++ (([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell) ++ ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)] : List Cell)))))))))))))), placement 7 (-4, -1) p ∈ envelope_612
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_3, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_4, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_5, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_6, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_7, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_8, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_9, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_10, List.forall_mem_append.mpr ⟨Internal.SnakyRows014.containment_612_1_points_11, Internal.SnakyRows014.containment_612_1_points_12⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem child_envelope_sub_612 : ∀ j, childrenD_612 j ⊆ envelope_612 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows014.containment_612_0
  · exact Internal.SnakyRows014.containment_612_1
theorem pivot_mem_612 : (0, 0) ∈ envelope_612 := by decide
theorem children_work_612 : ∀ j, Template HasSnaky 28 (childrenC_612 j) (childrenD_612 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_589 1 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_589 7 (-4, -1)).mono (by decide)
theorem row_works_612 : Template HasSnaky 29 required_612 envelope_612 := by
  refine compose HasSnaky 28 childrenC_612 childrenD_612 children_work_612 (0, 0)
    required_612 envelope_612 pivot_mem_612 child_required_sub_612 child_envelope_sub_612 ?_
  intro b hb; exact common_sub_612 (mem_commonEnvelope childrenD_612 b hb)
end SnakyConditional

end OAI
