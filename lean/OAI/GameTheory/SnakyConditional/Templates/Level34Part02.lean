import OAI.GameTheory.SnakyConditional.Templates.Level17Part05
import OAI.GameTheory.SnakyConditional.Templates.Level19Part05
import OAI.GameTheory.SnakyConditional.Templates.Level33Part02

namespace OAI

namespace SnakyConditional
def required_610 : Finset Cell := ⟨(([(-2, 0), (-2, 1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows012.named_envelope_610_5 : List Cell := ([(-12, 0), (-12, 1), (-12, 2), (-12, 3), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-10, 0), (-10, 1)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_5_chain : (named_envelope_610_5.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_5_head : (named_envelope_610_5.map Internal.SnakyRows012.namedCellKey).head? = some (-1536 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_5_last : (named_envelope_610_5.map Internal.SnakyRows012.namedCellKey).getLast? = some (-1279 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_6 : List Cell := ([(-10, 2), (-10, 3), (-10, 4), (-10, 6), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_6_chain : (named_envelope_610_6.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_6_head : (named_envelope_610_6.map Internal.SnakyRows012.namedCellKey).head? = some (-1278 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_6_last : (named_envelope_610_6.map Internal.SnakyRows012.namedCellKey).getLast? = some (-1148 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_4 : List Cell := Internal.SnakyRows012.named_envelope_610_5 ++ Internal.SnakyRows012.named_envelope_610_6
theorem Internal.SnakyRows012.named_envelope_610_4_chain : (named_envelope_610_4.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_5 Internal.SnakyRows012.named_envelope_610_6 (-1279 : ℤ) (-1278 : ℤ)
    Internal.SnakyRows012.named_envelope_610_5_chain Internal.SnakyRows012.named_envelope_610_6_chain Internal.SnakyRows012.named_envelope_610_5_last Internal.SnakyRows012.named_envelope_610_6_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_4_head : (named_envelope_610_4.map Internal.SnakyRows012.namedCellKey).head? = some (-1536 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_5 Internal.SnakyRows012.named_envelope_610_6 (-1536 : ℤ) Internal.SnakyRows012.named_envelope_610_5_head
theorem Internal.SnakyRows012.named_envelope_610_4_last : (named_envelope_610_4.map Internal.SnakyRows012.namedCellKey).getLast? = some (-1148 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_5 Internal.SnakyRows012.named_envelope_610_6 (-1148 : ℤ) Internal.SnakyRows012.named_envelope_610_6_last
def Internal.SnakyRows012.named_envelope_610_8 : List Cell := ([(-9, 5), (-9, 6), (-9, 7), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_8_chain : (named_envelope_610_8.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_8_head : (named_envelope_610_8.map Internal.SnakyRows012.namedCellKey).head? = some (-1147 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_8_last : (named_envelope_610_8.map Internal.SnakyRows012.namedCellKey).getLast? = some (-1020 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_9 : List Cell := ([(-8, 5), (-8, 6), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_9_chain : (named_envelope_610_9.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_9_head : (named_envelope_610_9.map Internal.SnakyRows012.namedCellKey).head? = some (-1019 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_9_last : (named_envelope_610_9.map Internal.SnakyRows012.namedCellKey).getLast? = some (-890 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_7 : List Cell := Internal.SnakyRows012.named_envelope_610_8 ++ Internal.SnakyRows012.named_envelope_610_9
theorem Internal.SnakyRows012.named_envelope_610_7_chain : (named_envelope_610_7.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_8 Internal.SnakyRows012.named_envelope_610_9 (-1020 : ℤ) (-1019 : ℤ)
    Internal.SnakyRows012.named_envelope_610_8_chain Internal.SnakyRows012.named_envelope_610_9_chain Internal.SnakyRows012.named_envelope_610_8_last Internal.SnakyRows012.named_envelope_610_9_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_7_head : (named_envelope_610_7.map Internal.SnakyRows012.namedCellKey).head? = some (-1147 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_8 Internal.SnakyRows012.named_envelope_610_9 (-1147 : ℤ) Internal.SnakyRows012.named_envelope_610_8_head
theorem Internal.SnakyRows012.named_envelope_610_7_last : (named_envelope_610_7.map Internal.SnakyRows012.namedCellKey).getLast? = some (-890 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_8 Internal.SnakyRows012.named_envelope_610_9 (-890 : ℤ) Internal.SnakyRows012.named_envelope_610_9_last
def Internal.SnakyRows012.named_envelope_610_3 : List Cell := Internal.SnakyRows012.named_envelope_610_4 ++ Internal.SnakyRows012.named_envelope_610_7
theorem Internal.SnakyRows012.named_envelope_610_3_chain : (named_envelope_610_3.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_4 Internal.SnakyRows012.named_envelope_610_7 (-1148 : ℤ) (-1147 : ℤ)
    Internal.SnakyRows012.named_envelope_610_4_chain Internal.SnakyRows012.named_envelope_610_7_chain Internal.SnakyRows012.named_envelope_610_4_last Internal.SnakyRows012.named_envelope_610_7_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_3_head : (named_envelope_610_3.map Internal.SnakyRows012.namedCellKey).head? = some (-1536 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_4 Internal.SnakyRows012.named_envelope_610_7 (-1536 : ℤ) Internal.SnakyRows012.named_envelope_610_4_head
theorem Internal.SnakyRows012.named_envelope_610_3_last : (named_envelope_610_3.map Internal.SnakyRows012.namedCellKey).getLast? = some (-890 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_4 Internal.SnakyRows012.named_envelope_610_7 (-890 : ℤ) Internal.SnakyRows012.named_envelope_610_7_last
def Internal.SnakyRows012.named_envelope_610_12 : List Cell := ([(-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 8)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_12_chain : (named_envelope_610_12.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_12_head : (named_envelope_610_12.map Internal.SnakyRows012.namedCellKey).head? = some (-770 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_12_last : (named_envelope_610_12.map Internal.SnakyRows012.namedCellKey).getLast? = some (-760 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_13 : List Cell := ([(-6, 9), (-6, 11), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_13_chain : (named_envelope_610_13.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_13_head : (named_envelope_610_13.map Internal.SnakyRows012.namedCellKey).head? = some (-759 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_13_last : (named_envelope_610_13.map Internal.SnakyRows012.namedCellKey).getLast? = some (-633 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_11 : List Cell := Internal.SnakyRows012.named_envelope_610_12 ++ Internal.SnakyRows012.named_envelope_610_13
theorem Internal.SnakyRows012.named_envelope_610_11_chain : (named_envelope_610_11.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_12 Internal.SnakyRows012.named_envelope_610_13 (-760 : ℤ) (-759 : ℤ)
    Internal.SnakyRows012.named_envelope_610_12_chain Internal.SnakyRows012.named_envelope_610_13_chain Internal.SnakyRows012.named_envelope_610_12_last Internal.SnakyRows012.named_envelope_610_13_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_11_head : (named_envelope_610_11.map Internal.SnakyRows012.namedCellKey).head? = some (-770 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_12 Internal.SnakyRows012.named_envelope_610_13 (-770 : ℤ) Internal.SnakyRows012.named_envelope_610_12_head
theorem Internal.SnakyRows012.named_envelope_610_11_last : (named_envelope_610_11.map Internal.SnakyRows012.namedCellKey).getLast? = some (-633 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_12 Internal.SnakyRows012.named_envelope_610_13 (-633 : ℤ) Internal.SnakyRows012.named_envelope_610_13_last
def Internal.SnakyRows012.named_envelope_610_15 : List Cell := ([(-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_15_chain : (named_envelope_610_15.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_15_head : (named_envelope_610_15.map Internal.SnakyRows012.namedCellKey).head? = some (-632 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_15_last : (named_envelope_610_15.map Internal.SnakyRows012.namedCellKey).getLast? = some (-507 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_16 : List Cell := ([(-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, 1), (-3, 2)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_16_chain : (named_envelope_610_16.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_16_head : (named_envelope_610_16.map Internal.SnakyRows012.namedCellKey).head? = some (-506 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_16_last : (named_envelope_610_16.map Internal.SnakyRows012.namedCellKey).getLast? = some (-382 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_14 : List Cell := Internal.SnakyRows012.named_envelope_610_15 ++ Internal.SnakyRows012.named_envelope_610_16
theorem Internal.SnakyRows012.named_envelope_610_14_chain : (named_envelope_610_14.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_15 Internal.SnakyRows012.named_envelope_610_16 (-507 : ℤ) (-506 : ℤ)
    Internal.SnakyRows012.named_envelope_610_15_chain Internal.SnakyRows012.named_envelope_610_16_chain Internal.SnakyRows012.named_envelope_610_15_last Internal.SnakyRows012.named_envelope_610_16_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_14_head : (named_envelope_610_14.map Internal.SnakyRows012.namedCellKey).head? = some (-632 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_15 Internal.SnakyRows012.named_envelope_610_16 (-632 : ℤ) Internal.SnakyRows012.named_envelope_610_15_head
theorem Internal.SnakyRows012.named_envelope_610_14_last : (named_envelope_610_14.map Internal.SnakyRows012.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_15 Internal.SnakyRows012.named_envelope_610_16 (-382 : ℤ) Internal.SnakyRows012.named_envelope_610_16_last
def Internal.SnakyRows012.named_envelope_610_10 : List Cell := Internal.SnakyRows012.named_envelope_610_11 ++ Internal.SnakyRows012.named_envelope_610_14
theorem Internal.SnakyRows012.named_envelope_610_10_chain : (named_envelope_610_10.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_11 Internal.SnakyRows012.named_envelope_610_14 (-633 : ℤ) (-632 : ℤ)
    Internal.SnakyRows012.named_envelope_610_11_chain Internal.SnakyRows012.named_envelope_610_14_chain Internal.SnakyRows012.named_envelope_610_11_last Internal.SnakyRows012.named_envelope_610_14_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_10_head : (named_envelope_610_10.map Internal.SnakyRows012.namedCellKey).head? = some (-770 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_11 Internal.SnakyRows012.named_envelope_610_14 (-770 : ℤ) Internal.SnakyRows012.named_envelope_610_11_head
theorem Internal.SnakyRows012.named_envelope_610_10_last : (named_envelope_610_10.map Internal.SnakyRows012.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_11 Internal.SnakyRows012.named_envelope_610_14 (-382 : ℤ) Internal.SnakyRows012.named_envelope_610_14_last
def Internal.SnakyRows012.named_envelope_610_2 : List Cell := Internal.SnakyRows012.named_envelope_610_3 ++ Internal.SnakyRows012.named_envelope_610_10
theorem Internal.SnakyRows012.named_envelope_610_2_chain : (named_envelope_610_2.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_3 Internal.SnakyRows012.named_envelope_610_10 (-890 : ℤ) (-770 : ℤ)
    Internal.SnakyRows012.named_envelope_610_3_chain Internal.SnakyRows012.named_envelope_610_10_chain Internal.SnakyRows012.named_envelope_610_3_last Internal.SnakyRows012.named_envelope_610_10_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_2_head : (named_envelope_610_2.map Internal.SnakyRows012.namedCellKey).head? = some (-1536 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_3 Internal.SnakyRows012.named_envelope_610_10 (-1536 : ℤ) Internal.SnakyRows012.named_envelope_610_3_head
theorem Internal.SnakyRows012.named_envelope_610_2_last : (named_envelope_610_2.map Internal.SnakyRows012.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_3 Internal.SnakyRows012.named_envelope_610_10 (-382 : ℤ) Internal.SnakyRows012.named_envelope_610_10_last
def Internal.SnakyRows012.named_envelope_610_20 : List Cell := ([(-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_20_chain : (named_envelope_610_20.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_20_head : (named_envelope_610_20.map Internal.SnakyRows012.namedCellKey).head? = some (-381 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_20_last : (named_envelope_610_20.map Internal.SnakyRows012.namedCellKey).getLast? = some (-372 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_21 : List Cell := ([(-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_21_chain : (named_envelope_610_21.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_21_head : (named_envelope_610_21.map Internal.SnakyRows012.namedCellKey).head? = some (-371 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_21_last : (named_envelope_610_21.map Internal.SnakyRows012.namedCellKey).getLast? = some (-247 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_19 : List Cell := Internal.SnakyRows012.named_envelope_610_20 ++ Internal.SnakyRows012.named_envelope_610_21
theorem Internal.SnakyRows012.named_envelope_610_19_chain : (named_envelope_610_19.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_20 Internal.SnakyRows012.named_envelope_610_21 (-372 : ℤ) (-371 : ℤ)
    Internal.SnakyRows012.named_envelope_610_20_chain Internal.SnakyRows012.named_envelope_610_21_chain Internal.SnakyRows012.named_envelope_610_20_last Internal.SnakyRows012.named_envelope_610_21_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_19_head : (named_envelope_610_19.map Internal.SnakyRows012.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_20 Internal.SnakyRows012.named_envelope_610_21 (-381 : ℤ) Internal.SnakyRows012.named_envelope_610_20_head
theorem Internal.SnakyRows012.named_envelope_610_19_last : (named_envelope_610_19.map Internal.SnakyRows012.namedCellKey).getLast? = some (-247 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_20 Internal.SnakyRows012.named_envelope_610_21 (-247 : ℤ) Internal.SnakyRows012.named_envelope_610_21_last
def Internal.SnakyRows012.named_envelope_610_23 : List Cell := ([(-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -5), (-1, -4), (-1, -3), (-1, -2)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_23_chain : (named_envelope_610_23.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_23_head : (named_envelope_610_23.map Internal.SnakyRows012.namedCellKey).head? = some (-246 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_23_last : (named_envelope_610_23.map Internal.SnakyRows012.namedCellKey).getLast? = some (-130 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_24 : List Cell := ([(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_24_chain : (named_envelope_610_24.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_24_head : (named_envelope_610_24.map Internal.SnakyRows012.namedCellKey).head? = some (-129 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_24_last : (named_envelope_610_24.map Internal.SnakyRows012.namedCellKey).getLast? = some (-118 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_22 : List Cell := Internal.SnakyRows012.named_envelope_610_23 ++ Internal.SnakyRows012.named_envelope_610_24
theorem Internal.SnakyRows012.named_envelope_610_22_chain : (named_envelope_610_22.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_23 Internal.SnakyRows012.named_envelope_610_24 (-130 : ℤ) (-129 : ℤ)
    Internal.SnakyRows012.named_envelope_610_23_chain Internal.SnakyRows012.named_envelope_610_24_chain Internal.SnakyRows012.named_envelope_610_23_last Internal.SnakyRows012.named_envelope_610_24_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_22_head : (named_envelope_610_22.map Internal.SnakyRows012.namedCellKey).head? = some (-246 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_23 Internal.SnakyRows012.named_envelope_610_24 (-246 : ℤ) Internal.SnakyRows012.named_envelope_610_23_head
theorem Internal.SnakyRows012.named_envelope_610_22_last : (named_envelope_610_22.map Internal.SnakyRows012.namedCellKey).getLast? = some (-118 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_23 Internal.SnakyRows012.named_envelope_610_24 (-118 : ℤ) Internal.SnakyRows012.named_envelope_610_24_last
def Internal.SnakyRows012.named_envelope_610_18 : List Cell := Internal.SnakyRows012.named_envelope_610_19 ++ Internal.SnakyRows012.named_envelope_610_22
theorem Internal.SnakyRows012.named_envelope_610_18_chain : (named_envelope_610_18.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_19 Internal.SnakyRows012.named_envelope_610_22 (-247 : ℤ) (-246 : ℤ)
    Internal.SnakyRows012.named_envelope_610_19_chain Internal.SnakyRows012.named_envelope_610_22_chain Internal.SnakyRows012.named_envelope_610_19_last Internal.SnakyRows012.named_envelope_610_22_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_18_head : (named_envelope_610_18.map Internal.SnakyRows012.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_19 Internal.SnakyRows012.named_envelope_610_22 (-381 : ℤ) Internal.SnakyRows012.named_envelope_610_19_head
theorem Internal.SnakyRows012.named_envelope_610_18_last : (named_envelope_610_18.map Internal.SnakyRows012.namedCellKey).getLast? = some (-118 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_19 Internal.SnakyRows012.named_envelope_610_22 (-118 : ℤ) Internal.SnakyRows012.named_envelope_610_22_last
def Internal.SnakyRows012.named_envelope_610_27 : List Cell := ([(-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_27_chain : (named_envelope_610_27.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_27_head : (named_envelope_610_27.map Internal.SnakyRows012.namedCellKey).head? = some (-117 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_27_last : (named_envelope_610_27.map Internal.SnakyRows012.namedCellKey).getLast? = some (-1 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_28 : List Cell := ([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_28_chain : (named_envelope_610_28.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_28_head : (named_envelope_610_28.map Internal.SnakyRows012.namedCellKey).head? = some (0 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_28_last : (named_envelope_610_28.map Internal.SnakyRows012.namedCellKey).getLast? = some (10 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_26 : List Cell := Internal.SnakyRows012.named_envelope_610_27 ++ Internal.SnakyRows012.named_envelope_610_28
theorem Internal.SnakyRows012.named_envelope_610_26_chain : (named_envelope_610_26.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_27 Internal.SnakyRows012.named_envelope_610_28 (-1 : ℤ) (0 : ℤ)
    Internal.SnakyRows012.named_envelope_610_27_chain Internal.SnakyRows012.named_envelope_610_28_chain Internal.SnakyRows012.named_envelope_610_27_last Internal.SnakyRows012.named_envelope_610_28_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_26_head : (named_envelope_610_26.map Internal.SnakyRows012.namedCellKey).head? = some (-117 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_27 Internal.SnakyRows012.named_envelope_610_28 (-117 : ℤ) Internal.SnakyRows012.named_envelope_610_27_head
theorem Internal.SnakyRows012.named_envelope_610_26_last : (named_envelope_610_26.map Internal.SnakyRows012.namedCellKey).getLast? = some (10 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_27 Internal.SnakyRows012.named_envelope_610_28 (10 : ℤ) Internal.SnakyRows012.named_envelope_610_28_last
def Internal.SnakyRows012.named_envelope_610_30 : List Cell := ([(0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_30_chain : (named_envelope_610_30.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_30_head : (named_envelope_610_30.map Internal.SnakyRows012.namedCellKey).head? = some (11 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_30_last : (named_envelope_610_30.map Internal.SnakyRows012.namedCellKey).getLast? = some (127 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_31 : List Cell := ([(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_31_chain : (named_envelope_610_31.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_31_head : (named_envelope_610_31.map Internal.SnakyRows012.namedCellKey).head? = some (128 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_31_last : (named_envelope_610_31.map Internal.SnakyRows012.namedCellKey).getLast? = some (138 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_29 : List Cell := Internal.SnakyRows012.named_envelope_610_30 ++ Internal.SnakyRows012.named_envelope_610_31
theorem Internal.SnakyRows012.named_envelope_610_29_chain : (named_envelope_610_29.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_30 Internal.SnakyRows012.named_envelope_610_31 (127 : ℤ) (128 : ℤ)
    Internal.SnakyRows012.named_envelope_610_30_chain Internal.SnakyRows012.named_envelope_610_31_chain Internal.SnakyRows012.named_envelope_610_30_last Internal.SnakyRows012.named_envelope_610_31_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_29_head : (named_envelope_610_29.map Internal.SnakyRows012.namedCellKey).head? = some (11 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_30 Internal.SnakyRows012.named_envelope_610_31 (11 : ℤ) Internal.SnakyRows012.named_envelope_610_30_head
theorem Internal.SnakyRows012.named_envelope_610_29_last : (named_envelope_610_29.map Internal.SnakyRows012.namedCellKey).getLast? = some (138 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_30 Internal.SnakyRows012.named_envelope_610_31 (138 : ℤ) Internal.SnakyRows012.named_envelope_610_31_last
def Internal.SnakyRows012.named_envelope_610_25 : List Cell := Internal.SnakyRows012.named_envelope_610_26 ++ Internal.SnakyRows012.named_envelope_610_29
theorem Internal.SnakyRows012.named_envelope_610_25_chain : (named_envelope_610_25.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_26 Internal.SnakyRows012.named_envelope_610_29 (10 : ℤ) (11 : ℤ)
    Internal.SnakyRows012.named_envelope_610_26_chain Internal.SnakyRows012.named_envelope_610_29_chain Internal.SnakyRows012.named_envelope_610_26_last Internal.SnakyRows012.named_envelope_610_29_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_25_head : (named_envelope_610_25.map Internal.SnakyRows012.namedCellKey).head? = some (-117 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_26 Internal.SnakyRows012.named_envelope_610_29 (-117 : ℤ) Internal.SnakyRows012.named_envelope_610_26_head
theorem Internal.SnakyRows012.named_envelope_610_25_last : (named_envelope_610_25.map Internal.SnakyRows012.namedCellKey).getLast? = some (138 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_26 Internal.SnakyRows012.named_envelope_610_29 (138 : ℤ) Internal.SnakyRows012.named_envelope_610_29_last
def Internal.SnakyRows012.named_envelope_610_17 : List Cell := Internal.SnakyRows012.named_envelope_610_18 ++ Internal.SnakyRows012.named_envelope_610_25
theorem Internal.SnakyRows012.named_envelope_610_17_chain : (named_envelope_610_17.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_18 Internal.SnakyRows012.named_envelope_610_25 (-118 : ℤ) (-117 : ℤ)
    Internal.SnakyRows012.named_envelope_610_18_chain Internal.SnakyRows012.named_envelope_610_25_chain Internal.SnakyRows012.named_envelope_610_18_last Internal.SnakyRows012.named_envelope_610_25_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_17_head : (named_envelope_610_17.map Internal.SnakyRows012.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_18 Internal.SnakyRows012.named_envelope_610_25 (-381 : ℤ) Internal.SnakyRows012.named_envelope_610_18_head
theorem Internal.SnakyRows012.named_envelope_610_17_last : (named_envelope_610_17.map Internal.SnakyRows012.namedCellKey).getLast? = some (138 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_18 Internal.SnakyRows012.named_envelope_610_25 (138 : ℤ) Internal.SnakyRows012.named_envelope_610_25_last
def Internal.SnakyRows012.named_envelope_610_1 : List Cell := Internal.SnakyRows012.named_envelope_610_2 ++ Internal.SnakyRows012.named_envelope_610_17
theorem Internal.SnakyRows012.named_envelope_610_1_chain : (named_envelope_610_1.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_2 Internal.SnakyRows012.named_envelope_610_17 (-382 : ℤ) (-381 : ℤ)
    Internal.SnakyRows012.named_envelope_610_2_chain Internal.SnakyRows012.named_envelope_610_17_chain Internal.SnakyRows012.named_envelope_610_2_last Internal.SnakyRows012.named_envelope_610_17_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_1_head : (named_envelope_610_1.map Internal.SnakyRows012.namedCellKey).head? = some (-1536 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_2 Internal.SnakyRows012.named_envelope_610_17 (-1536 : ℤ) Internal.SnakyRows012.named_envelope_610_2_head
theorem Internal.SnakyRows012.named_envelope_610_1_last : (named_envelope_610_1.map Internal.SnakyRows012.namedCellKey).getLast? = some (138 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_2 Internal.SnakyRows012.named_envelope_610_17 (138 : ℤ) Internal.SnakyRows012.named_envelope_610_17_last
def Internal.SnakyRows012.named_envelope_610_36 : List Cell := ([(1, 11), (1, 12), (1, 13), (1, 14), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_36_chain : (named_envelope_610_36.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_36_head : (named_envelope_610_36.map Internal.SnakyRows012.namedCellKey).head? = some (139 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_36_last : (named_envelope_610_36.map Internal.SnakyRows012.namedCellKey).getLast? = some (256 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_37 : List Cell := ([(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_37_chain : (named_envelope_610_37.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_37_head : (named_envelope_610_37.map Internal.SnakyRows012.namedCellKey).head? = some (257 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_37_last : (named_envelope_610_37.map Internal.SnakyRows012.namedCellKey).getLast? = some (267 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_35 : List Cell := Internal.SnakyRows012.named_envelope_610_36 ++ Internal.SnakyRows012.named_envelope_610_37
theorem Internal.SnakyRows012.named_envelope_610_35_chain : (named_envelope_610_35.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_36 Internal.SnakyRows012.named_envelope_610_37 (256 : ℤ) (257 : ℤ)
    Internal.SnakyRows012.named_envelope_610_36_chain Internal.SnakyRows012.named_envelope_610_37_chain Internal.SnakyRows012.named_envelope_610_36_last Internal.SnakyRows012.named_envelope_610_37_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_35_head : (named_envelope_610_35.map Internal.SnakyRows012.namedCellKey).head? = some (139 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_36 Internal.SnakyRows012.named_envelope_610_37 (139 : ℤ) Internal.SnakyRows012.named_envelope_610_36_head
theorem Internal.SnakyRows012.named_envelope_610_35_last : (named_envelope_610_35.map Internal.SnakyRows012.namedCellKey).getLast? = some (267 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_36 Internal.SnakyRows012.named_envelope_610_37 (267 : ℤ) Internal.SnakyRows012.named_envelope_610_37_last
def Internal.SnakyRows012.named_envelope_610_39 : List Cell := ([(2, 12), (2, 13), (2, 14), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_39_chain : (named_envelope_610_39.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_39_head : (named_envelope_610_39.map Internal.SnakyRows012.namedCellKey).head? = some (268 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_39_last : (named_envelope_610_39.map Internal.SnakyRows012.namedCellKey).getLast? = some (388 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_40 : List Cell := ([(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, -3)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_40_chain : (named_envelope_610_40.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_40_head : (named_envelope_610_40.map Internal.SnakyRows012.namedCellKey).head? = some (389 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_40_last : (named_envelope_610_40.map Internal.SnakyRows012.namedCellKey).getLast? = some (509 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_38 : List Cell := Internal.SnakyRows012.named_envelope_610_39 ++ Internal.SnakyRows012.named_envelope_610_40
theorem Internal.SnakyRows012.named_envelope_610_38_chain : (named_envelope_610_38.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_39 Internal.SnakyRows012.named_envelope_610_40 (388 : ℤ) (389 : ℤ)
    Internal.SnakyRows012.named_envelope_610_39_chain Internal.SnakyRows012.named_envelope_610_40_chain Internal.SnakyRows012.named_envelope_610_39_last Internal.SnakyRows012.named_envelope_610_40_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_38_head : (named_envelope_610_38.map Internal.SnakyRows012.namedCellKey).head? = some (268 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_39 Internal.SnakyRows012.named_envelope_610_40 (268 : ℤ) Internal.SnakyRows012.named_envelope_610_39_head
theorem Internal.SnakyRows012.named_envelope_610_38_last : (named_envelope_610_38.map Internal.SnakyRows012.namedCellKey).getLast? = some (509 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_39 Internal.SnakyRows012.named_envelope_610_40 (509 : ℤ) Internal.SnakyRows012.named_envelope_610_40_last
def Internal.SnakyRows012.named_envelope_610_34 : List Cell := Internal.SnakyRows012.named_envelope_610_35 ++ Internal.SnakyRows012.named_envelope_610_38
theorem Internal.SnakyRows012.named_envelope_610_34_chain : (named_envelope_610_34.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_35 Internal.SnakyRows012.named_envelope_610_38 (267 : ℤ) (268 : ℤ)
    Internal.SnakyRows012.named_envelope_610_35_chain Internal.SnakyRows012.named_envelope_610_38_chain Internal.SnakyRows012.named_envelope_610_35_last Internal.SnakyRows012.named_envelope_610_38_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_34_head : (named_envelope_610_34.map Internal.SnakyRows012.namedCellKey).head? = some (139 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_35 Internal.SnakyRows012.named_envelope_610_38 (139 : ℤ) Internal.SnakyRows012.named_envelope_610_35_head
theorem Internal.SnakyRows012.named_envelope_610_34_last : (named_envelope_610_34.map Internal.SnakyRows012.namedCellKey).getLast? = some (509 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_35 Internal.SnakyRows012.named_envelope_610_38 (509 : ℤ) Internal.SnakyRows012.named_envelope_610_38_last
def Internal.SnakyRows012.named_envelope_610_43 : List Cell := ([(4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_43_chain : (named_envelope_610_43.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_43_head : (named_envelope_610_43.map Internal.SnakyRows012.namedCellKey).head? = some (510 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_43_last : (named_envelope_610_43.map Internal.SnakyRows012.namedCellKey).getLast? = some (519 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_44 : List Cell := ([(4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_44_chain : (named_envelope_610_44.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_44_head : (named_envelope_610_44.map Internal.SnakyRows012.namedCellKey).head? = some (520 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_44_last : (named_envelope_610_44.map Internal.SnakyRows012.namedCellKey).getLast? = some (640 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_42 : List Cell := Internal.SnakyRows012.named_envelope_610_43 ++ Internal.SnakyRows012.named_envelope_610_44
theorem Internal.SnakyRows012.named_envelope_610_42_chain : (named_envelope_610_42.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_43 Internal.SnakyRows012.named_envelope_610_44 (519 : ℤ) (520 : ℤ)
    Internal.SnakyRows012.named_envelope_610_43_chain Internal.SnakyRows012.named_envelope_610_44_chain Internal.SnakyRows012.named_envelope_610_43_last Internal.SnakyRows012.named_envelope_610_44_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_42_head : (named_envelope_610_42.map Internal.SnakyRows012.namedCellKey).head? = some (510 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_43 Internal.SnakyRows012.named_envelope_610_44 (510 : ℤ) Internal.SnakyRows012.named_envelope_610_43_head
theorem Internal.SnakyRows012.named_envelope_610_42_last : (named_envelope_610_42.map Internal.SnakyRows012.namedCellKey).getLast? = some (640 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_43 Internal.SnakyRows012.named_envelope_610_44 (640 : ℤ) Internal.SnakyRows012.named_envelope_610_44_last
def Internal.SnakyRows012.named_envelope_610_46 : List Cell := ([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_46_chain : (named_envelope_610_46.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_46_head : (named_envelope_610_46.map Internal.SnakyRows012.namedCellKey).head? = some (641 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_46_last : (named_envelope_610_46.map Internal.SnakyRows012.namedCellKey).getLast? = some (651 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_47 : List Cell := ([(5, 12), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_47_chain : (named_envelope_610_47.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_47_head : (named_envelope_610_47.map Internal.SnakyRows012.namedCellKey).head? = some (652 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_47_last : (named_envelope_610_47.map Internal.SnakyRows012.namedCellKey).getLast? = some (773 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_45 : List Cell := Internal.SnakyRows012.named_envelope_610_46 ++ Internal.SnakyRows012.named_envelope_610_47
theorem Internal.SnakyRows012.named_envelope_610_45_chain : (named_envelope_610_45.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_46 Internal.SnakyRows012.named_envelope_610_47 (651 : ℤ) (652 : ℤ)
    Internal.SnakyRows012.named_envelope_610_46_chain Internal.SnakyRows012.named_envelope_610_47_chain Internal.SnakyRows012.named_envelope_610_46_last Internal.SnakyRows012.named_envelope_610_47_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_45_head : (named_envelope_610_45.map Internal.SnakyRows012.namedCellKey).head? = some (641 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_46 Internal.SnakyRows012.named_envelope_610_47 (641 : ℤ) Internal.SnakyRows012.named_envelope_610_46_head
theorem Internal.SnakyRows012.named_envelope_610_45_last : (named_envelope_610_45.map Internal.SnakyRows012.namedCellKey).getLast? = some (773 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_46 Internal.SnakyRows012.named_envelope_610_47 (773 : ℤ) Internal.SnakyRows012.named_envelope_610_47_last
def Internal.SnakyRows012.named_envelope_610_41 : List Cell := Internal.SnakyRows012.named_envelope_610_42 ++ Internal.SnakyRows012.named_envelope_610_45
theorem Internal.SnakyRows012.named_envelope_610_41_chain : (named_envelope_610_41.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_42 Internal.SnakyRows012.named_envelope_610_45 (640 : ℤ) (641 : ℤ)
    Internal.SnakyRows012.named_envelope_610_42_chain Internal.SnakyRows012.named_envelope_610_45_chain Internal.SnakyRows012.named_envelope_610_42_last Internal.SnakyRows012.named_envelope_610_45_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_41_head : (named_envelope_610_41.map Internal.SnakyRows012.namedCellKey).head? = some (510 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_42 Internal.SnakyRows012.named_envelope_610_45 (510 : ℤ) Internal.SnakyRows012.named_envelope_610_42_head
theorem Internal.SnakyRows012.named_envelope_610_41_last : (named_envelope_610_41.map Internal.SnakyRows012.namedCellKey).getLast? = some (773 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_42 Internal.SnakyRows012.named_envelope_610_45 (773 : ℤ) Internal.SnakyRows012.named_envelope_610_45_last
def Internal.SnakyRows012.named_envelope_610_33 : List Cell := Internal.SnakyRows012.named_envelope_610_34 ++ Internal.SnakyRows012.named_envelope_610_41
theorem Internal.SnakyRows012.named_envelope_610_33_chain : (named_envelope_610_33.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_34 Internal.SnakyRows012.named_envelope_610_41 (509 : ℤ) (510 : ℤ)
    Internal.SnakyRows012.named_envelope_610_34_chain Internal.SnakyRows012.named_envelope_610_41_chain Internal.SnakyRows012.named_envelope_610_34_last Internal.SnakyRows012.named_envelope_610_41_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_33_head : (named_envelope_610_33.map Internal.SnakyRows012.namedCellKey).head? = some (139 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_34 Internal.SnakyRows012.named_envelope_610_41 (139 : ℤ) Internal.SnakyRows012.named_envelope_610_34_head
theorem Internal.SnakyRows012.named_envelope_610_33_last : (named_envelope_610_33.map Internal.SnakyRows012.namedCellKey).getLast? = some (773 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_34 Internal.SnakyRows012.named_envelope_610_41 (773 : ℤ) Internal.SnakyRows012.named_envelope_610_41_last
def Internal.SnakyRows012.named_envelope_610_51 : List Cell := ([(6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_51_chain : (named_envelope_610_51.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_51_head : (named_envelope_610_51.map Internal.SnakyRows012.namedCellKey).head? = some (774 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_51_last : (named_envelope_610_51.map Internal.SnakyRows012.namedCellKey).getLast? = some (894 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_52 : List Cell := ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_52_chain : (named_envelope_610_52.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_52_head : (named_envelope_610_52.map Internal.SnakyRows012.namedCellKey).head? = some (895 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_52_last : (named_envelope_610_52.map Internal.SnakyRows012.namedCellKey).getLast? = some (905 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_50 : List Cell := Internal.SnakyRows012.named_envelope_610_51 ++ Internal.SnakyRows012.named_envelope_610_52
theorem Internal.SnakyRows012.named_envelope_610_50_chain : (named_envelope_610_50.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_51 Internal.SnakyRows012.named_envelope_610_52 (894 : ℤ) (895 : ℤ)
    Internal.SnakyRows012.named_envelope_610_51_chain Internal.SnakyRows012.named_envelope_610_52_chain Internal.SnakyRows012.named_envelope_610_51_last Internal.SnakyRows012.named_envelope_610_52_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_50_head : (named_envelope_610_50.map Internal.SnakyRows012.namedCellKey).head? = some (774 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_51 Internal.SnakyRows012.named_envelope_610_52 (774 : ℤ) Internal.SnakyRows012.named_envelope_610_51_head
theorem Internal.SnakyRows012.named_envelope_610_50_last : (named_envelope_610_50.map Internal.SnakyRows012.namedCellKey).getLast? = some (905 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_51 Internal.SnakyRows012.named_envelope_610_52 (905 : ℤ) Internal.SnakyRows012.named_envelope_610_52_last
def Internal.SnakyRows012.named_envelope_610_54 : List Cell := ([(7, 10), (7, 11), (7, 12), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_54_chain : (named_envelope_610_54.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_54_head : (named_envelope_610_54.map Internal.SnakyRows012.namedCellKey).head? = some (906 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_54_last : (named_envelope_610_54.map Internal.SnakyRows012.namedCellKey).getLast? = some (1028 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_55 : List Cell := ([(8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_55_chain : (named_envelope_610_55.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_55_head : (named_envelope_610_55.map Internal.SnakyRows012.namedCellKey).head? = some (1029 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_55_last : (named_envelope_610_55.map Internal.SnakyRows012.namedCellKey).getLast? = some (1152 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_53 : List Cell := Internal.SnakyRows012.named_envelope_610_54 ++ Internal.SnakyRows012.named_envelope_610_55
theorem Internal.SnakyRows012.named_envelope_610_53_chain : (named_envelope_610_53.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_54 Internal.SnakyRows012.named_envelope_610_55 (1028 : ℤ) (1029 : ℤ)
    Internal.SnakyRows012.named_envelope_610_54_chain Internal.SnakyRows012.named_envelope_610_55_chain Internal.SnakyRows012.named_envelope_610_54_last Internal.SnakyRows012.named_envelope_610_55_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_53_head : (named_envelope_610_53.map Internal.SnakyRows012.namedCellKey).head? = some (906 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_54 Internal.SnakyRows012.named_envelope_610_55 (906 : ℤ) Internal.SnakyRows012.named_envelope_610_54_head
theorem Internal.SnakyRows012.named_envelope_610_53_last : (named_envelope_610_53.map Internal.SnakyRows012.namedCellKey).getLast? = some (1152 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_54 Internal.SnakyRows012.named_envelope_610_55 (1152 : ℤ) Internal.SnakyRows012.named_envelope_610_55_last
def Internal.SnakyRows012.named_envelope_610_49 : List Cell := Internal.SnakyRows012.named_envelope_610_50 ++ Internal.SnakyRows012.named_envelope_610_53
theorem Internal.SnakyRows012.named_envelope_610_49_chain : (named_envelope_610_49.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_50 Internal.SnakyRows012.named_envelope_610_53 (905 : ℤ) (906 : ℤ)
    Internal.SnakyRows012.named_envelope_610_50_chain Internal.SnakyRows012.named_envelope_610_53_chain Internal.SnakyRows012.named_envelope_610_50_last Internal.SnakyRows012.named_envelope_610_53_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_49_head : (named_envelope_610_49.map Internal.SnakyRows012.namedCellKey).head? = some (774 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_50 Internal.SnakyRows012.named_envelope_610_53 (774 : ℤ) Internal.SnakyRows012.named_envelope_610_50_head
theorem Internal.SnakyRows012.named_envelope_610_49_last : (named_envelope_610_49.map Internal.SnakyRows012.namedCellKey).getLast? = some (1152 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_50 Internal.SnakyRows012.named_envelope_610_53 (1152 : ℤ) Internal.SnakyRows012.named_envelope_610_53_last
def Internal.SnakyRows012.named_envelope_610_58 : List Cell := ([(9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, -2)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_58_chain : (named_envelope_610_58.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_58_head : (named_envelope_610_58.map Internal.SnakyRows012.namedCellKey).head? = some (1153 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_58_last : (named_envelope_610_58.map Internal.SnakyRows012.namedCellKey).getLast? = some (1278 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_59 : List Cell := ([(10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_59_chain : (named_envelope_610_59.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_59_head : (named_envelope_610_59.map Internal.SnakyRows012.namedCellKey).head? = some (1279 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_59_last : (named_envelope_610_59.map Internal.SnakyRows012.namedCellKey).getLast? = some (1289 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_57 : List Cell := Internal.SnakyRows012.named_envelope_610_58 ++ Internal.SnakyRows012.named_envelope_610_59
theorem Internal.SnakyRows012.named_envelope_610_57_chain : (named_envelope_610_57.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_58 Internal.SnakyRows012.named_envelope_610_59 (1278 : ℤ) (1279 : ℤ)
    Internal.SnakyRows012.named_envelope_610_58_chain Internal.SnakyRows012.named_envelope_610_59_chain Internal.SnakyRows012.named_envelope_610_58_last Internal.SnakyRows012.named_envelope_610_59_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_57_head : (named_envelope_610_57.map Internal.SnakyRows012.namedCellKey).head? = some (1153 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_58 Internal.SnakyRows012.named_envelope_610_59 (1153 : ℤ) Internal.SnakyRows012.named_envelope_610_58_head
theorem Internal.SnakyRows012.named_envelope_610_57_last : (named_envelope_610_57.map Internal.SnakyRows012.namedCellKey).getLast? = some (1289 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_58 Internal.SnakyRows012.named_envelope_610_59 (1289 : ℤ) Internal.SnakyRows012.named_envelope_610_59_last
def Internal.SnakyRows012.named_envelope_610_61 : List Cell := ([(11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (12, -2), (12, 0)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_61_chain : (named_envelope_610_61.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_61_head : (named_envelope_610_61.map Internal.SnakyRows012.namedCellKey).head? = some (1406 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_61_last : (named_envelope_610_61.map Internal.SnakyRows012.namedCellKey).getLast? = some (1536 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_62 : List Cell := ([(12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)] : List Cell)
theorem Internal.SnakyRows012.named_envelope_610_62_chain : (named_envelope_610_62.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012.named_envelope_610_62_head : (named_envelope_610_62.map Internal.SnakyRows012.namedCellKey).head? = some (1537 : ℤ) := by decide
theorem Internal.SnakyRows012.named_envelope_610_62_last : (named_envelope_610_62.map Internal.SnakyRows012.namedCellKey).getLast? = some (1794 : ℤ) := by decide
def Internal.SnakyRows012.named_envelope_610_60 : List Cell := Internal.SnakyRows012.named_envelope_610_61 ++ Internal.SnakyRows012.named_envelope_610_62
theorem Internal.SnakyRows012.named_envelope_610_60_chain : (named_envelope_610_60.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_61 Internal.SnakyRows012.named_envelope_610_62 (1536 : ℤ) (1537 : ℤ)
    Internal.SnakyRows012.named_envelope_610_61_chain Internal.SnakyRows012.named_envelope_610_62_chain Internal.SnakyRows012.named_envelope_610_61_last Internal.SnakyRows012.named_envelope_610_62_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_60_head : (named_envelope_610_60.map Internal.SnakyRows012.namedCellKey).head? = some (1406 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_61 Internal.SnakyRows012.named_envelope_610_62 (1406 : ℤ) Internal.SnakyRows012.named_envelope_610_61_head
theorem Internal.SnakyRows012.named_envelope_610_60_last : (named_envelope_610_60.map Internal.SnakyRows012.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_61 Internal.SnakyRows012.named_envelope_610_62 (1794 : ℤ) Internal.SnakyRows012.named_envelope_610_62_last
def Internal.SnakyRows012.named_envelope_610_56 : List Cell := Internal.SnakyRows012.named_envelope_610_57 ++ Internal.SnakyRows012.named_envelope_610_60
theorem Internal.SnakyRows012.named_envelope_610_56_chain : (named_envelope_610_56.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_57 Internal.SnakyRows012.named_envelope_610_60 (1289 : ℤ) (1406 : ℤ)
    Internal.SnakyRows012.named_envelope_610_57_chain Internal.SnakyRows012.named_envelope_610_60_chain Internal.SnakyRows012.named_envelope_610_57_last Internal.SnakyRows012.named_envelope_610_60_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_56_head : (named_envelope_610_56.map Internal.SnakyRows012.namedCellKey).head? = some (1153 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_57 Internal.SnakyRows012.named_envelope_610_60 (1153 : ℤ) Internal.SnakyRows012.named_envelope_610_57_head
theorem Internal.SnakyRows012.named_envelope_610_56_last : (named_envelope_610_56.map Internal.SnakyRows012.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_57 Internal.SnakyRows012.named_envelope_610_60 (1794 : ℤ) Internal.SnakyRows012.named_envelope_610_60_last
def Internal.SnakyRows012.named_envelope_610_48 : List Cell := Internal.SnakyRows012.named_envelope_610_49 ++ Internal.SnakyRows012.named_envelope_610_56
theorem Internal.SnakyRows012.named_envelope_610_48_chain : (named_envelope_610_48.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_49 Internal.SnakyRows012.named_envelope_610_56 (1152 : ℤ) (1153 : ℤ)
    Internal.SnakyRows012.named_envelope_610_49_chain Internal.SnakyRows012.named_envelope_610_56_chain Internal.SnakyRows012.named_envelope_610_49_last Internal.SnakyRows012.named_envelope_610_56_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_48_head : (named_envelope_610_48.map Internal.SnakyRows012.namedCellKey).head? = some (774 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_49 Internal.SnakyRows012.named_envelope_610_56 (774 : ℤ) Internal.SnakyRows012.named_envelope_610_49_head
theorem Internal.SnakyRows012.named_envelope_610_48_last : (named_envelope_610_48.map Internal.SnakyRows012.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_49 Internal.SnakyRows012.named_envelope_610_56 (1794 : ℤ) Internal.SnakyRows012.named_envelope_610_56_last
def Internal.SnakyRows012.named_envelope_610_32 : List Cell := Internal.SnakyRows012.named_envelope_610_33 ++ Internal.SnakyRows012.named_envelope_610_48
theorem Internal.SnakyRows012.named_envelope_610_32_chain : (named_envelope_610_32.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_33 Internal.SnakyRows012.named_envelope_610_48 (773 : ℤ) (774 : ℤ)
    Internal.SnakyRows012.named_envelope_610_33_chain Internal.SnakyRows012.named_envelope_610_48_chain Internal.SnakyRows012.named_envelope_610_33_last Internal.SnakyRows012.named_envelope_610_48_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_32_head : (named_envelope_610_32.map Internal.SnakyRows012.namedCellKey).head? = some (139 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_33 Internal.SnakyRows012.named_envelope_610_48 (139 : ℤ) Internal.SnakyRows012.named_envelope_610_33_head
theorem Internal.SnakyRows012.named_envelope_610_32_last : (named_envelope_610_32.map Internal.SnakyRows012.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_33 Internal.SnakyRows012.named_envelope_610_48 (1794 : ℤ) Internal.SnakyRows012.named_envelope_610_48_last
def Internal.SnakyRows012.named_envelope_610_0 : List Cell := Internal.SnakyRows012.named_envelope_610_1 ++ Internal.SnakyRows012.named_envelope_610_32
theorem Internal.SnakyRows012.named_envelope_610_0_chain : (named_envelope_610_0.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012.named_chain_append Internal.SnakyRows012.named_envelope_610_1 Internal.SnakyRows012.named_envelope_610_32 (138 : ℤ) (139 : ℤ)
    Internal.SnakyRows012.named_envelope_610_1_chain Internal.SnakyRows012.named_envelope_610_32_chain Internal.SnakyRows012.named_envelope_610_1_last Internal.SnakyRows012.named_envelope_610_32_head (by decide)
theorem Internal.SnakyRows012.named_envelope_610_0_head : (named_envelope_610_0.map Internal.SnakyRows012.namedCellKey).head? = some (-1536 : ℤ) :=
  Internal.SnakyRows012.named_head_append Internal.SnakyRows012.named_envelope_610_1 Internal.SnakyRows012.named_envelope_610_32 (-1536 : ℤ) Internal.SnakyRows012.named_envelope_610_1_head
theorem Internal.SnakyRows012.named_envelope_610_0_last : (named_envelope_610_0.map Internal.SnakyRows012.namedCellKey).getLast? = some (1794 : ℤ) :=
  Internal.SnakyRows012.named_last_append Internal.SnakyRows012.named_envelope_610_1 Internal.SnakyRows012.named_envelope_610_32 (1794 : ℤ) Internal.SnakyRows012.named_envelope_610_32_last
theorem Internal.SnakyRows012.named_envelope_610_nodup : (Internal.SnakyRows012.named_envelope_610_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows012.named_nodup_of_chain Internal.SnakyRows012.named_envelope_610_0 Internal.SnakyRows012.named_envelope_610_0_chain
def envelope_610 : Finset Cell := ⟨(Internal.SnakyRows012.named_envelope_610_0 : Multiset Cell), Internal.SnakyRows012.named_envelope_610_nodup⟩
def childrenC_610 : Fin 8 → Finset Cell := ![(placedSet 2 (1, 0) required_221), (placedSet 5 (1, 0) required_286), (placedSet 2 (1, 0) required_107), (placedSet 1 (1, 0) required_472), (placedSet 1 (1, 0) required_566), (placedSet 5 (1, 0) required_532), (placedSet 1 (1, 0) required_542), (placedSet 0 (-2, 2) required_609)]
def childrenD_610 : Fin 8 → Finset Cell := ![(placedSet 2 (1, 0) envelope_221), (placedSet 5 (1, 0) envelope_286), (placedSet 2 (1, 0) envelope_107), (placedSet 1 (1, 0) envelope_472), (placedSet 1 (1, 0) envelope_566), (placedSet 5 (1, 0) envelope_532), (placedSet 1 (1, 0) envelope_542), (placedSet 0 (-2, 2) envelope_609)]
theorem common_sub_610 : commonEnvelope childrenD_610 ⊆ insert (0, 0) required_610 := by decide
theorem child_required_sub_610 : ∀ j, childrenC_610 j ⊆ insert (0, 0) required_610 := by decide
theorem Internal.SnakyRows012.containment_610_0_points_0 :
    ∀ p ∈ ([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell), placement 2 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_0_points_1 :
    ∀ p ∈ ([(3, 0), (3, 1), (4, 1)] : List Cell), placement 2 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_0 :
    placedSet 2 (1, 0) envelope_221 ⊆ envelope_610 := by
  apply Internal.SnakyRows012.placedSet_subset_of_points
  change ∀ p ∈ ((([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) ++ ([(3, 0), (3, 1), (4, 1)] : List Cell))), placement 2 (1, 0) p ∈ envelope_610
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_0_points_0, Internal.SnakyRows012.containment_610_0_points_1⟩
theorem Internal.SnakyRows012.containment_610_1_points_0 :
    ∀ p ∈ ([(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)] : List Cell), placement 5 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_1_points_1 :
    ∀ p ∈ ([(2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell), placement 5 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_1 :
    placedSet 5 (1, 0) envelope_286 ⊆ envelope_610 := by
  apply Internal.SnakyRows012.placedSet_subset_of_points
  change ∀ p ∈ ((([(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)] : List Cell) ++ ([(2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell))), placement 5 (1, 0) p ∈ envelope_610
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_1_points_0, Internal.SnakyRows012.containment_610_1_points_1⟩
theorem Internal.SnakyRows012.containment_610_2_points_0 :
    ∀ p ∈ ([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell), placement 2 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_2 :
    placedSet 2 (1, 0) envelope_107 ⊆ envelope_610 := by
  apply Internal.SnakyRows012.placedSet_subset_of_points
  change ∀ p ∈ (([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell)), placement 2 (1, 0) p ∈ envelope_610
  exact Internal.SnakyRows012.containment_610_2_points_0
theorem Internal.SnakyRows012.containment_610_3_points_0 :
    ∀ p ∈ ([(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_3_points_1 :
    ∀ p ∈ ([(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_3_points_2 :
    ∀ p ∈ ([(1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_3_points_3 :
    ∀ p ∈ ([(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_3_points_4 :
    ∀ p ∈ ([(4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_3 :
    placedSet 1 (1, 0) envelope_472 ⊆ envelope_610 := by
  apply Internal.SnakyRows012.placedSet_subset_of_points
  change ∀ p ∈ ((([(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2)] : List Cell) ++ (([(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0)] : List Cell) ++ (([(1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5)] : List Cell) ++ (([(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)] : List Cell) ++ ([(4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell)))))), placement 1 (1, 0) p ∈ envelope_610
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_3_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_3_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_3_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_3_points_3, Internal.SnakyRows012.containment_610_3_points_4⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4_points_0 :
    ∀ p ∈ ([(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4_points_1 :
    ∀ p ∈ ([(-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4_points_2 :
    ∀ p ∈ ([(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4_points_3 :
    ∀ p ∈ ([(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4_points_4 :
    ∀ p ∈ ([(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4_points_5 :
    ∀ p ∈ ([(4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4_points_6 :
    ∀ p ∈ ([(6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_4 :
    placedSet 1 (1, 0) envelope_566 ⊆ envelope_610 := by
  apply Internal.SnakyRows012.placedSet_subset_of_points
  change ∀ p ∈ ((([(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2)] : List Cell) ++ (([(-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2)] : List Cell) ++ (([(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4)] : List Cell) ++ (([(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1)] : List Cell) ++ (([(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell) ++ (([(4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0)] : List Cell) ++ ([(6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell)))))))), placement 1 (1, 0) p ∈ envelope_610
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_4_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_4_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_4_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_4_points_3, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_4_points_4, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_4_points_5, Internal.SnakyRows012.containment_610_4_points_6⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_5_points_0 :
    ∀ p ∈ ([(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3)] : List Cell), placement 5 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_5_points_1 :
    ∀ p ∈ ([(-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell), placement 5 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_5_points_2 :
    ∀ p ∈ ([(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1)] : List Cell), placement 5 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_5_points_3 :
    ∀ p ∈ ([(4, 0), (4, 1), (5, -2), (5, 0), (5, 1)] : List Cell), placement 5 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_5 :
    placedSet 5 (1, 0) envelope_532 ⊆ envelope_610 := by
  apply Internal.SnakyRows012.placedSet_subset_of_points
  change ∀ p ∈ ((([(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3)] : List Cell) ++ (([(-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) ++ (([(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1)] : List Cell) ++ ([(4, 0), (4, 1), (5, -2), (5, 0), (5, 1)] : List Cell))))), placement 5 (1, 0) p ∈ envelope_610
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_5_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_5_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_5_points_2, Internal.SnakyRows012.containment_610_5_points_3⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_6_points_0 :
    ∀ p ∈ ([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_6_points_1 :
    ∀ p ∈ ([(0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_6_points_2 :
    ∀ p ∈ ([(2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_6_points_3 :
    ∀ p ∈ ([(4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_6_points_4 :
    ∀ p ∈ ([(7, 4)] : List Cell), placement 1 (1, 0) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩
theorem Internal.SnakyRows012.containment_610_6 :
    placedSet 1 (1, 0) envelope_542 ⊆ envelope_610 := by
  apply Internal.SnakyRows012.placedSet_subset_of_points
  change ∀ p ∈ ((([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)] : List Cell) ++ (([(0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell) ++ (([(2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell) ++ (([(4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3)] : List Cell) ++ ([(7, 4)] : List Cell)))))), placement 1 (1, 0) p ∈ envelope_610
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_6_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_6_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_6_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows012.containment_610_6_points_3, Internal.SnakyRows012.containment_610_6_points_4⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_0 :
    ∀ p ∈ ([(-10, -2), (-10, -1), (-10, 0), (-10, 1), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 4), (-7, -4), (-7, -3)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_1 :
    ∀ p ∈ ([(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_2 :
    ∀ p ∈ ([(-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_3 :
    ∀ p ∈ ([(-4, 2), (-4, 3), (-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_4 :
    ∀ p ∈ ([(-3, 7), (-3, 8), (-3, 9), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_5 :
    ∀ p ∈ ([(-2, 10), (-2, 11), (-2, 12), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_6 :
    ∀ p ∈ ([(0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_7 :
    ∀ p ∈ ([(0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_8 :
    ∀ p ∈ ([(1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_9 :
    ∀ p ∈ ([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_10 :
    ∀ p ∈ ([(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_11 :
    ∀ p ∈ ([(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_12 :
    ∀ p ∈ ([(5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -5)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_13 :
    ∀ p ∈ ([(6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_14 :
    ∀ p ∈ ([(6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_15 :
    ∀ p ∈ ([(8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_16 :
    ∀ p ∈ ([(8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_17 :
    ∀ p ∈ ([(9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_18 :
    ∀ p ∈ ([(11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_19 :
    ∀ p ∈ ([(12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7_points_20 :
    ∀ p ∈ ([(13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)] : List Cell), placement 0 (-2, 2) p ∈ envelope_610 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012.containment_610_7 :
    placedSet 0 (-2, 2) envelope_609 ⊆ envelope_610 := by decide +kernel
theorem child_envelope_sub_610 : ∀ j, childrenD_610 j ⊆ envelope_610 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows012.containment_610_0
  · exact Internal.SnakyRows012.containment_610_1
  · exact Internal.SnakyRows012.containment_610_2
  · exact Internal.SnakyRows012.containment_610_3
  · exact Internal.SnakyRows012.containment_610_4
  · exact Internal.SnakyRows012.containment_610_5
  · exact Internal.SnakyRows012.containment_610_6
  · exact Internal.SnakyRows012.containment_610_7
theorem pivot_mem_610 : (0, 0) ∈ envelope_610 := by decide
theorem children_work_610 : ∀ j, Template HasSnaky 31 (childrenC_610 j) (childrenD_610 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_221 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_286 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_107 2 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_472 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_566 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_532 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_542 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_609 0 (-2, 2)).mono (by decide)
theorem row_works_610 : Template HasSnaky 32 required_610 envelope_610 := by
  refine compose HasSnaky 31 childrenC_610 childrenD_610 children_work_610 (0, 0)
    required_610 envelope_610 pivot_mem_610 child_required_sub_610 child_envelope_sub_610 ?_
  intro b hb; exact common_sub_610 (mem_commonEnvelope childrenD_610 b hb)
end SnakyConditional

end OAI
