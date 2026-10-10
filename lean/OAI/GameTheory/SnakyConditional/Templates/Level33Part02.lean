import OAI.GameTheory.SnakyConditional.Templates.Level19Part03
import OAI.GameTheory.SnakyConditional.Templates.Level26Part01
import OAI.GameTheory.SnakyConditional.Templates.Level26Part05
import OAI.GameTheory.SnakyConditional.Templates.Level32Part01

namespace OAI

namespace SnakyConditional
def required_609 : Finset Cell := ⟨(([(0, -2), (0, -1), (1, -2), (2, -2)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows012D.named_envelope_609_5 : List Cell := ([(-10, -2), (-10, -1), (-10, 0), (-10, 1), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-8, -2), (-8, -1)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_5_chain : (named_envelope_609_5.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_5_head : (named_envelope_609_5.map Internal.SnakyRows012D.namedCellKey).head? = some (-1282 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_5_last : (named_envelope_609_5.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-1025 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_6 : List Cell := ([(-8, 0), (-8, 1), (-8, 2), (-8, 4), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_6_chain : (named_envelope_609_6.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_6_head : (named_envelope_609_6.map Internal.SnakyRows012D.namedCellKey).head? = some (-1024 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_6_last : (named_envelope_609_6.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-894 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_4 : List Cell := Internal.SnakyRows012D.named_envelope_609_5 ++ Internal.SnakyRows012D.named_envelope_609_6
theorem Internal.SnakyRows012D.named_envelope_609_4_chain : (named_envelope_609_4.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_5 Internal.SnakyRows012D.named_envelope_609_6 (-1025 : ℤ) (-1024 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_5_chain Internal.SnakyRows012D.named_envelope_609_6_chain Internal.SnakyRows012D.named_envelope_609_5_last Internal.SnakyRows012D.named_envelope_609_6_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_4_head : (named_envelope_609_4.map Internal.SnakyRows012D.namedCellKey).head? = some (-1282 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_5 Internal.SnakyRows012D.named_envelope_609_6 (-1282 : ℤ) Internal.SnakyRows012D.named_envelope_609_5_head
theorem Internal.SnakyRows012D.named_envelope_609_4_last : (named_envelope_609_4.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-894 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_5 Internal.SnakyRows012D.named_envelope_609_6 (-894 : ℤ) Internal.SnakyRows012D.named_envelope_609_6_last
def Internal.SnakyRows012D.named_envelope_609_8 : List Cell := ([(-7, 3), (-7, 4), (-7, 5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_8_chain : (named_envelope_609_8.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_8_head : (named_envelope_609_8.map Internal.SnakyRows012D.namedCellKey).head? = some (-893 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_8_last : (named_envelope_609_8.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-766 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_9 : List Cell := ([(-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_9_chain : (named_envelope_609_9.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_9_head : (named_envelope_609_9.map Internal.SnakyRows012D.namedCellKey).head? = some (-765 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_9_last : (named_envelope_609_9.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-636 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_7 : List Cell := Internal.SnakyRows012D.named_envelope_609_8 ++ Internal.SnakyRows012D.named_envelope_609_9
theorem Internal.SnakyRows012D.named_envelope_609_7_chain : (named_envelope_609_7.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_8 Internal.SnakyRows012D.named_envelope_609_9 (-766 : ℤ) (-765 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_8_chain Internal.SnakyRows012D.named_envelope_609_9_chain Internal.SnakyRows012D.named_envelope_609_8_last Internal.SnakyRows012D.named_envelope_609_9_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_7_head : (named_envelope_609_7.map Internal.SnakyRows012D.namedCellKey).head? = some (-893 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_8 Internal.SnakyRows012D.named_envelope_609_9 (-893 : ℤ) Internal.SnakyRows012D.named_envelope_609_8_head
theorem Internal.SnakyRows012D.named_envelope_609_7_last : (named_envelope_609_7.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-636 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_8 Internal.SnakyRows012D.named_envelope_609_9 (-636 : ℤ) Internal.SnakyRows012D.named_envelope_609_9_last
def Internal.SnakyRows012D.named_envelope_609_3 : List Cell := Internal.SnakyRows012D.named_envelope_609_4 ++ Internal.SnakyRows012D.named_envelope_609_7
theorem Internal.SnakyRows012D.named_envelope_609_3_chain : (named_envelope_609_3.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_4 Internal.SnakyRows012D.named_envelope_609_7 (-894 : ℤ) (-893 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_4_chain Internal.SnakyRows012D.named_envelope_609_7_chain Internal.SnakyRows012D.named_envelope_609_4_last Internal.SnakyRows012D.named_envelope_609_7_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_3_head : (named_envelope_609_3.map Internal.SnakyRows012D.namedCellKey).head? = some (-1282 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_4 Internal.SnakyRows012D.named_envelope_609_7 (-1282 : ℤ) Internal.SnakyRows012D.named_envelope_609_4_head
theorem Internal.SnakyRows012D.named_envelope_609_3_last : (named_envelope_609_3.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-636 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_4 Internal.SnakyRows012D.named_envelope_609_7 (-636 : ℤ) Internal.SnakyRows012D.named_envelope_609_7_last
def Internal.SnakyRows012D.named_envelope_609_12 : List Cell := ([(-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 6)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_12_chain : (named_envelope_609_12.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_12_head : (named_envelope_609_12.map Internal.SnakyRows012D.namedCellKey).head? = some (-516 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_12_last : (named_envelope_609_12.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-506 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_13 : List Cell := ([(-4, 7), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_13_chain : (named_envelope_609_13.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_13_head : (named_envelope_609_13.map Internal.SnakyRows012D.namedCellKey).head? = some (-505 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_13_last : (named_envelope_609_13.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-379 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_11 : List Cell := Internal.SnakyRows012D.named_envelope_609_12 ++ Internal.SnakyRows012D.named_envelope_609_13
theorem Internal.SnakyRows012D.named_envelope_609_11_chain : (named_envelope_609_11.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_12 Internal.SnakyRows012D.named_envelope_609_13 (-506 : ℤ) (-505 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_12_chain Internal.SnakyRows012D.named_envelope_609_13_chain Internal.SnakyRows012D.named_envelope_609_12_last Internal.SnakyRows012D.named_envelope_609_13_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_11_head : (named_envelope_609_11.map Internal.SnakyRows012D.namedCellKey).head? = some (-516 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_12 Internal.SnakyRows012D.named_envelope_609_13 (-516 : ℤ) Internal.SnakyRows012D.named_envelope_609_12_head
theorem Internal.SnakyRows012D.named_envelope_609_11_last : (named_envelope_609_11.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-379 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_12 Internal.SnakyRows012D.named_envelope_609_13 (-379 : ℤ) Internal.SnakyRows012D.named_envelope_609_13_last
def Internal.SnakyRows012D.named_envelope_609_15 : List Cell := ([(-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_15_chain : (named_envelope_609_15.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_15_head : (named_envelope_609_15.map Internal.SnakyRows012D.namedCellKey).head? = some (-378 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_15_last : (named_envelope_609_15.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-254 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_16 : List Cell := ([(-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -1)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_16_chain : (named_envelope_609_16.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_16_head : (named_envelope_609_16.map Internal.SnakyRows012D.namedCellKey).head? = some (-253 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_16_last : (named_envelope_609_16.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-129 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_14 : List Cell := Internal.SnakyRows012D.named_envelope_609_15 ++ Internal.SnakyRows012D.named_envelope_609_16
theorem Internal.SnakyRows012D.named_envelope_609_14_chain : (named_envelope_609_14.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_15 Internal.SnakyRows012D.named_envelope_609_16 (-254 : ℤ) (-253 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_15_chain Internal.SnakyRows012D.named_envelope_609_16_chain Internal.SnakyRows012D.named_envelope_609_15_last Internal.SnakyRows012D.named_envelope_609_16_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_14_head : (named_envelope_609_14.map Internal.SnakyRows012D.namedCellKey).head? = some (-378 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_15 Internal.SnakyRows012D.named_envelope_609_16 (-378 : ℤ) Internal.SnakyRows012D.named_envelope_609_15_head
theorem Internal.SnakyRows012D.named_envelope_609_14_last : (named_envelope_609_14.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_15 Internal.SnakyRows012D.named_envelope_609_16 (-129 : ℤ) Internal.SnakyRows012D.named_envelope_609_16_last
def Internal.SnakyRows012D.named_envelope_609_10 : List Cell := Internal.SnakyRows012D.named_envelope_609_11 ++ Internal.SnakyRows012D.named_envelope_609_14
theorem Internal.SnakyRows012D.named_envelope_609_10_chain : (named_envelope_609_10.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_11 Internal.SnakyRows012D.named_envelope_609_14 (-379 : ℤ) (-378 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_11_chain Internal.SnakyRows012D.named_envelope_609_14_chain Internal.SnakyRows012D.named_envelope_609_11_last Internal.SnakyRows012D.named_envelope_609_14_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_10_head : (named_envelope_609_10.map Internal.SnakyRows012D.namedCellKey).head? = some (-516 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_11 Internal.SnakyRows012D.named_envelope_609_14 (-516 : ℤ) Internal.SnakyRows012D.named_envelope_609_11_head
theorem Internal.SnakyRows012D.named_envelope_609_10_last : (named_envelope_609_10.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_11 Internal.SnakyRows012D.named_envelope_609_14 (-129 : ℤ) Internal.SnakyRows012D.named_envelope_609_14_last
def Internal.SnakyRows012D.named_envelope_609_2 : List Cell := Internal.SnakyRows012D.named_envelope_609_3 ++ Internal.SnakyRows012D.named_envelope_609_10
theorem Internal.SnakyRows012D.named_envelope_609_2_chain : (named_envelope_609_2.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_3 Internal.SnakyRows012D.named_envelope_609_10 (-636 : ℤ) (-516 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_3_chain Internal.SnakyRows012D.named_envelope_609_10_chain Internal.SnakyRows012D.named_envelope_609_3_last Internal.SnakyRows012D.named_envelope_609_10_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_2_head : (named_envelope_609_2.map Internal.SnakyRows012D.namedCellKey).head? = some (-1282 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_3 Internal.SnakyRows012D.named_envelope_609_10 (-1282 : ℤ) Internal.SnakyRows012D.named_envelope_609_3_head
theorem Internal.SnakyRows012D.named_envelope_609_2_last : (named_envelope_609_2.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-129 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_3 Internal.SnakyRows012D.named_envelope_609_10 (-129 : ℤ) Internal.SnakyRows012D.named_envelope_609_10_last
def Internal.SnakyRows012D.named_envelope_609_20 : List Cell := ([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_20_chain : (named_envelope_609_20.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_20_head : (named_envelope_609_20.map Internal.SnakyRows012D.namedCellKey).head? = some (-128 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_20_last : (named_envelope_609_20.map Internal.SnakyRows012D.namedCellKey).getLast? = some (-119 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_21 : List Cell := ([(-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_21_chain : (named_envelope_609_21.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_21_head : (named_envelope_609_21.map Internal.SnakyRows012D.namedCellKey).head? = some (-118 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_21_last : (named_envelope_609_21.map Internal.SnakyRows012D.namedCellKey).getLast? = some (6 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_19 : List Cell := Internal.SnakyRows012D.named_envelope_609_20 ++ Internal.SnakyRows012D.named_envelope_609_21
theorem Internal.SnakyRows012D.named_envelope_609_19_chain : (named_envelope_609_19.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_20 Internal.SnakyRows012D.named_envelope_609_21 (-119 : ℤ) (-118 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_20_chain Internal.SnakyRows012D.named_envelope_609_21_chain Internal.SnakyRows012D.named_envelope_609_20_last Internal.SnakyRows012D.named_envelope_609_21_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_19_head : (named_envelope_609_19.map Internal.SnakyRows012D.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_20 Internal.SnakyRows012D.named_envelope_609_21 (-128 : ℤ) Internal.SnakyRows012D.named_envelope_609_20_head
theorem Internal.SnakyRows012D.named_envelope_609_19_last : (named_envelope_609_19.map Internal.SnakyRows012D.namedCellKey).getLast? = some (6 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_20 Internal.SnakyRows012D.named_envelope_609_21 (6 : ℤ) Internal.SnakyRows012D.named_envelope_609_21_last
def Internal.SnakyRows012D.named_envelope_609_23 : List Cell := ([(0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_23_chain : (named_envelope_609_23.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_23_head : (named_envelope_609_23.map Internal.SnakyRows012D.namedCellKey).head? = some (7 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_23_last : (named_envelope_609_23.map Internal.SnakyRows012D.namedCellKey).getLast? = some (122 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_24 : List Cell := ([(1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_24_chain : (named_envelope_609_24.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_24_head : (named_envelope_609_24.map Internal.SnakyRows012D.namedCellKey).head? = some (123 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_24_last : (named_envelope_609_24.map Internal.SnakyRows012D.namedCellKey).getLast? = some (134 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_22 : List Cell := Internal.SnakyRows012D.named_envelope_609_23 ++ Internal.SnakyRows012D.named_envelope_609_24
theorem Internal.SnakyRows012D.named_envelope_609_22_chain : (named_envelope_609_22.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_23 Internal.SnakyRows012D.named_envelope_609_24 (122 : ℤ) (123 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_23_chain Internal.SnakyRows012D.named_envelope_609_24_chain Internal.SnakyRows012D.named_envelope_609_23_last Internal.SnakyRows012D.named_envelope_609_24_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_22_head : (named_envelope_609_22.map Internal.SnakyRows012D.namedCellKey).head? = some (7 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_23 Internal.SnakyRows012D.named_envelope_609_24 (7 : ℤ) Internal.SnakyRows012D.named_envelope_609_23_head
theorem Internal.SnakyRows012D.named_envelope_609_22_last : (named_envelope_609_22.map Internal.SnakyRows012D.namedCellKey).getLast? = some (134 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_23 Internal.SnakyRows012D.named_envelope_609_24 (134 : ℤ) Internal.SnakyRows012D.named_envelope_609_24_last
def Internal.SnakyRows012D.named_envelope_609_18 : List Cell := Internal.SnakyRows012D.named_envelope_609_19 ++ Internal.SnakyRows012D.named_envelope_609_22
theorem Internal.SnakyRows012D.named_envelope_609_18_chain : (named_envelope_609_18.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_19 Internal.SnakyRows012D.named_envelope_609_22 (6 : ℤ) (7 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_19_chain Internal.SnakyRows012D.named_envelope_609_22_chain Internal.SnakyRows012D.named_envelope_609_19_last Internal.SnakyRows012D.named_envelope_609_22_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_18_head : (named_envelope_609_18.map Internal.SnakyRows012D.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_19 Internal.SnakyRows012D.named_envelope_609_22 (-128 : ℤ) Internal.SnakyRows012D.named_envelope_609_19_head
theorem Internal.SnakyRows012D.named_envelope_609_18_last : (named_envelope_609_18.map Internal.SnakyRows012D.namedCellKey).getLast? = some (134 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_19 Internal.SnakyRows012D.named_envelope_609_22 (134 : ℤ) Internal.SnakyRows012D.named_envelope_609_22_last
def Internal.SnakyRows012D.named_envelope_609_27 : List Cell := ([(1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_27_chain : (named_envelope_609_27.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_27_head : (named_envelope_609_27.map Internal.SnakyRows012D.namedCellKey).head? = some (135 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_27_last : (named_envelope_609_27.map Internal.SnakyRows012D.namedCellKey).getLast? = some (252 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_28 : List Cell := ([(2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_28_chain : (named_envelope_609_28.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_28_head : (named_envelope_609_28.map Internal.SnakyRows012D.namedCellKey).head? = some (253 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_28_last : (named_envelope_609_28.map Internal.SnakyRows012D.namedCellKey).getLast? = some (263 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_26 : List Cell := Internal.SnakyRows012D.named_envelope_609_27 ++ Internal.SnakyRows012D.named_envelope_609_28
theorem Internal.SnakyRows012D.named_envelope_609_26_chain : (named_envelope_609_26.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_27 Internal.SnakyRows012D.named_envelope_609_28 (252 : ℤ) (253 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_27_chain Internal.SnakyRows012D.named_envelope_609_28_chain Internal.SnakyRows012D.named_envelope_609_27_last Internal.SnakyRows012D.named_envelope_609_28_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_26_head : (named_envelope_609_26.map Internal.SnakyRows012D.namedCellKey).head? = some (135 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_27 Internal.SnakyRows012D.named_envelope_609_28 (135 : ℤ) Internal.SnakyRows012D.named_envelope_609_27_head
theorem Internal.SnakyRows012D.named_envelope_609_26_last : (named_envelope_609_26.map Internal.SnakyRows012D.namedCellKey).getLast? = some (263 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_27 Internal.SnakyRows012D.named_envelope_609_28 (263 : ℤ) Internal.SnakyRows012D.named_envelope_609_28_last
def Internal.SnakyRows012D.named_envelope_609_30 : List Cell := ([(2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -6), (3, -5), (3, -4)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_30_chain : (named_envelope_609_30.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_30_head : (named_envelope_609_30.map Internal.SnakyRows012D.namedCellKey).head? = some (264 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_30_last : (named_envelope_609_30.map Internal.SnakyRows012D.namedCellKey).getLast? = some (380 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_31 : List Cell := ([(3, -3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_31_chain : (named_envelope_609_31.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_31_head : (named_envelope_609_31.map Internal.SnakyRows012D.namedCellKey).head? = some (381 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_31_last : (named_envelope_609_31.map Internal.SnakyRows012D.namedCellKey).getLast? = some (392 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_29 : List Cell := Internal.SnakyRows012D.named_envelope_609_30 ++ Internal.SnakyRows012D.named_envelope_609_31
theorem Internal.SnakyRows012D.named_envelope_609_29_chain : (named_envelope_609_29.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_30 Internal.SnakyRows012D.named_envelope_609_31 (380 : ℤ) (381 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_30_chain Internal.SnakyRows012D.named_envelope_609_31_chain Internal.SnakyRows012D.named_envelope_609_30_last Internal.SnakyRows012D.named_envelope_609_31_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_29_head : (named_envelope_609_29.map Internal.SnakyRows012D.namedCellKey).head? = some (264 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_30 Internal.SnakyRows012D.named_envelope_609_31 (264 : ℤ) Internal.SnakyRows012D.named_envelope_609_30_head
theorem Internal.SnakyRows012D.named_envelope_609_29_last : (named_envelope_609_29.map Internal.SnakyRows012D.namedCellKey).getLast? = some (392 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_30 Internal.SnakyRows012D.named_envelope_609_31 (392 : ℤ) Internal.SnakyRows012D.named_envelope_609_31_last
def Internal.SnakyRows012D.named_envelope_609_25 : List Cell := Internal.SnakyRows012D.named_envelope_609_26 ++ Internal.SnakyRows012D.named_envelope_609_29
theorem Internal.SnakyRows012D.named_envelope_609_25_chain : (named_envelope_609_25.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_26 Internal.SnakyRows012D.named_envelope_609_29 (263 : ℤ) (264 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_26_chain Internal.SnakyRows012D.named_envelope_609_29_chain Internal.SnakyRows012D.named_envelope_609_26_last Internal.SnakyRows012D.named_envelope_609_29_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_25_head : (named_envelope_609_25.map Internal.SnakyRows012D.namedCellKey).head? = some (135 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_26 Internal.SnakyRows012D.named_envelope_609_29 (135 : ℤ) Internal.SnakyRows012D.named_envelope_609_26_head
theorem Internal.SnakyRows012D.named_envelope_609_25_last : (named_envelope_609_25.map Internal.SnakyRows012D.namedCellKey).getLast? = some (392 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_26 Internal.SnakyRows012D.named_envelope_609_29 (392 : ℤ) Internal.SnakyRows012D.named_envelope_609_29_last
def Internal.SnakyRows012D.named_envelope_609_17 : List Cell := Internal.SnakyRows012D.named_envelope_609_18 ++ Internal.SnakyRows012D.named_envelope_609_25
theorem Internal.SnakyRows012D.named_envelope_609_17_chain : (named_envelope_609_17.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_18 Internal.SnakyRows012D.named_envelope_609_25 (134 : ℤ) (135 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_18_chain Internal.SnakyRows012D.named_envelope_609_25_chain Internal.SnakyRows012D.named_envelope_609_18_last Internal.SnakyRows012D.named_envelope_609_25_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_17_head : (named_envelope_609_17.map Internal.SnakyRows012D.namedCellKey).head? = some (-128 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_18 Internal.SnakyRows012D.named_envelope_609_25 (-128 : ℤ) Internal.SnakyRows012D.named_envelope_609_18_head
theorem Internal.SnakyRows012D.named_envelope_609_17_last : (named_envelope_609_17.map Internal.SnakyRows012D.namedCellKey).getLast? = some (392 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_18 Internal.SnakyRows012D.named_envelope_609_25 (392 : ℤ) Internal.SnakyRows012D.named_envelope_609_25_last
def Internal.SnakyRows012D.named_envelope_609_1 : List Cell := Internal.SnakyRows012D.named_envelope_609_2 ++ Internal.SnakyRows012D.named_envelope_609_17
theorem Internal.SnakyRows012D.named_envelope_609_1_chain : (named_envelope_609_1.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_2 Internal.SnakyRows012D.named_envelope_609_17 (-129 : ℤ) (-128 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_2_chain Internal.SnakyRows012D.named_envelope_609_17_chain Internal.SnakyRows012D.named_envelope_609_2_last Internal.SnakyRows012D.named_envelope_609_17_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_1_head : (named_envelope_609_1.map Internal.SnakyRows012D.namedCellKey).head? = some (-1282 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_2 Internal.SnakyRows012D.named_envelope_609_17 (-1282 : ℤ) Internal.SnakyRows012D.named_envelope_609_2_head
theorem Internal.SnakyRows012D.named_envelope_609_1_last : (named_envelope_609_1.map Internal.SnakyRows012D.namedCellKey).getLast? = some (392 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_2 Internal.SnakyRows012D.named_envelope_609_17 (392 : ℤ) Internal.SnakyRows012D.named_envelope_609_17_last
def Internal.SnakyRows012D.named_envelope_609_36 : List Cell := ([(3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_36_chain : (named_envelope_609_36.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_36_head : (named_envelope_609_36.map Internal.SnakyRows012D.namedCellKey).head? = some (393 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_36_last : (named_envelope_609_36.map Internal.SnakyRows012D.namedCellKey).getLast? = some (512 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_37 : List Cell := ([(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_37_chain : (named_envelope_609_37.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_37_head : (named_envelope_609_37.map Internal.SnakyRows012D.namedCellKey).head? = some (513 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_37_last : (named_envelope_609_37.map Internal.SnakyRows012D.namedCellKey).getLast? = some (523 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_35 : List Cell := Internal.SnakyRows012D.named_envelope_609_36 ++ Internal.SnakyRows012D.named_envelope_609_37
theorem Internal.SnakyRows012D.named_envelope_609_35_chain : (named_envelope_609_35.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_36 Internal.SnakyRows012D.named_envelope_609_37 (512 : ℤ) (513 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_36_chain Internal.SnakyRows012D.named_envelope_609_37_chain Internal.SnakyRows012D.named_envelope_609_36_last Internal.SnakyRows012D.named_envelope_609_37_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_35_head : (named_envelope_609_35.map Internal.SnakyRows012D.namedCellKey).head? = some (393 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_36 Internal.SnakyRows012D.named_envelope_609_37 (393 : ℤ) Internal.SnakyRows012D.named_envelope_609_36_head
theorem Internal.SnakyRows012D.named_envelope_609_35_last : (named_envelope_609_35.map Internal.SnakyRows012D.namedCellKey).getLast? = some (523 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_36 Internal.SnakyRows012D.named_envelope_609_37 (523 : ℤ) Internal.SnakyRows012D.named_envelope_609_37_last
def Internal.SnakyRows012D.named_envelope_609_39 : List Cell := ([(4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_39_chain : (named_envelope_609_39.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_39_head : (named_envelope_609_39.map Internal.SnakyRows012D.namedCellKey).head? = some (524 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_39_last : (named_envelope_609_39.map Internal.SnakyRows012D.namedCellKey).getLast? = some (644 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_40 : List Cell := ([(5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -5), (6, -4), (6, -3)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_40_chain : (named_envelope_609_40.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_40_head : (named_envelope_609_40.map Internal.SnakyRows012D.namedCellKey).head? = some (645 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_40_last : (named_envelope_609_40.map Internal.SnakyRows012D.namedCellKey).getLast? = some (765 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_38 : List Cell := Internal.SnakyRows012D.named_envelope_609_39 ++ Internal.SnakyRows012D.named_envelope_609_40
theorem Internal.SnakyRows012D.named_envelope_609_38_chain : (named_envelope_609_38.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_39 Internal.SnakyRows012D.named_envelope_609_40 (644 : ℤ) (645 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_39_chain Internal.SnakyRows012D.named_envelope_609_40_chain Internal.SnakyRows012D.named_envelope_609_39_last Internal.SnakyRows012D.named_envelope_609_40_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_38_head : (named_envelope_609_38.map Internal.SnakyRows012D.namedCellKey).head? = some (524 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_39 Internal.SnakyRows012D.named_envelope_609_40 (524 : ℤ) Internal.SnakyRows012D.named_envelope_609_39_head
theorem Internal.SnakyRows012D.named_envelope_609_38_last : (named_envelope_609_38.map Internal.SnakyRows012D.namedCellKey).getLast? = some (765 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_39 Internal.SnakyRows012D.named_envelope_609_40 (765 : ℤ) Internal.SnakyRows012D.named_envelope_609_40_last
def Internal.SnakyRows012D.named_envelope_609_34 : List Cell := Internal.SnakyRows012D.named_envelope_609_35 ++ Internal.SnakyRows012D.named_envelope_609_38
theorem Internal.SnakyRows012D.named_envelope_609_34_chain : (named_envelope_609_34.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_35 Internal.SnakyRows012D.named_envelope_609_38 (523 : ℤ) (524 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_35_chain Internal.SnakyRows012D.named_envelope_609_38_chain Internal.SnakyRows012D.named_envelope_609_35_last Internal.SnakyRows012D.named_envelope_609_38_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_34_head : (named_envelope_609_34.map Internal.SnakyRows012D.namedCellKey).head? = some (393 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_35 Internal.SnakyRows012D.named_envelope_609_38 (393 : ℤ) Internal.SnakyRows012D.named_envelope_609_35_head
theorem Internal.SnakyRows012D.named_envelope_609_34_last : (named_envelope_609_34.map Internal.SnakyRows012D.namedCellKey).getLast? = some (765 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_35 Internal.SnakyRows012D.named_envelope_609_38 (765 : ℤ) Internal.SnakyRows012D.named_envelope_609_38_last
def Internal.SnakyRows012D.named_envelope_609_43 : List Cell := ([(6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_43_chain : (named_envelope_609_43.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_43_head : (named_envelope_609_43.map Internal.SnakyRows012D.namedCellKey).head? = some (766 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_43_last : (named_envelope_609_43.map Internal.SnakyRows012D.namedCellKey).getLast? = some (775 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_44 : List Cell := ([(6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_44_chain : (named_envelope_609_44.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_44_head : (named_envelope_609_44.map Internal.SnakyRows012D.namedCellKey).head? = some (776 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_44_last : (named_envelope_609_44.map Internal.SnakyRows012D.namedCellKey).getLast? = some (897 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_42 : List Cell := Internal.SnakyRows012D.named_envelope_609_43 ++ Internal.SnakyRows012D.named_envelope_609_44
theorem Internal.SnakyRows012D.named_envelope_609_42_chain : (named_envelope_609_42.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_43 Internal.SnakyRows012D.named_envelope_609_44 (775 : ℤ) (776 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_43_chain Internal.SnakyRows012D.named_envelope_609_44_chain Internal.SnakyRows012D.named_envelope_609_43_last Internal.SnakyRows012D.named_envelope_609_44_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_42_head : (named_envelope_609_42.map Internal.SnakyRows012D.namedCellKey).head? = some (766 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_43 Internal.SnakyRows012D.named_envelope_609_44 (766 : ℤ) Internal.SnakyRows012D.named_envelope_609_43_head
theorem Internal.SnakyRows012D.named_envelope_609_42_last : (named_envelope_609_42.map Internal.SnakyRows012D.namedCellKey).getLast? = some (897 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_43 Internal.SnakyRows012D.named_envelope_609_44 (897 : ℤ) Internal.SnakyRows012D.named_envelope_609_44_last
def Internal.SnakyRows012D.named_envelope_609_46 : List Cell := ([(7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_46_chain : (named_envelope_609_46.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_46_head : (named_envelope_609_46.map Internal.SnakyRows012D.namedCellKey).head? = some (898 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_46_last : (named_envelope_609_46.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1018 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_47 : List Cell := ([(8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_47_chain : (named_envelope_609_47.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_47_head : (named_envelope_609_47.map Internal.SnakyRows012D.namedCellKey).head? = some (1019 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_47_last : (named_envelope_609_47.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1029 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_45 : List Cell := Internal.SnakyRows012D.named_envelope_609_46 ++ Internal.SnakyRows012D.named_envelope_609_47
theorem Internal.SnakyRows012D.named_envelope_609_45_chain : (named_envelope_609_45.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_46 Internal.SnakyRows012D.named_envelope_609_47 (1018 : ℤ) (1019 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_46_chain Internal.SnakyRows012D.named_envelope_609_47_chain Internal.SnakyRows012D.named_envelope_609_46_last Internal.SnakyRows012D.named_envelope_609_47_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_45_head : (named_envelope_609_45.map Internal.SnakyRows012D.namedCellKey).head? = some (898 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_46 Internal.SnakyRows012D.named_envelope_609_47 (898 : ℤ) Internal.SnakyRows012D.named_envelope_609_46_head
theorem Internal.SnakyRows012D.named_envelope_609_45_last : (named_envelope_609_45.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1029 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_46 Internal.SnakyRows012D.named_envelope_609_47 (1029 : ℤ) Internal.SnakyRows012D.named_envelope_609_47_last
def Internal.SnakyRows012D.named_envelope_609_41 : List Cell := Internal.SnakyRows012D.named_envelope_609_42 ++ Internal.SnakyRows012D.named_envelope_609_45
theorem Internal.SnakyRows012D.named_envelope_609_41_chain : (named_envelope_609_41.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_42 Internal.SnakyRows012D.named_envelope_609_45 (897 : ℤ) (898 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_42_chain Internal.SnakyRows012D.named_envelope_609_45_chain Internal.SnakyRows012D.named_envelope_609_42_last Internal.SnakyRows012D.named_envelope_609_45_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_41_head : (named_envelope_609_41.map Internal.SnakyRows012D.namedCellKey).head? = some (766 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_42 Internal.SnakyRows012D.named_envelope_609_45 (766 : ℤ) Internal.SnakyRows012D.named_envelope_609_42_head
theorem Internal.SnakyRows012D.named_envelope_609_41_last : (named_envelope_609_41.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1029 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_42 Internal.SnakyRows012D.named_envelope_609_45 (1029 : ℤ) Internal.SnakyRows012D.named_envelope_609_45_last
def Internal.SnakyRows012D.named_envelope_609_33 : List Cell := Internal.SnakyRows012D.named_envelope_609_34 ++ Internal.SnakyRows012D.named_envelope_609_41
theorem Internal.SnakyRows012D.named_envelope_609_33_chain : (named_envelope_609_33.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_34 Internal.SnakyRows012D.named_envelope_609_41 (765 : ℤ) (766 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_34_chain Internal.SnakyRows012D.named_envelope_609_41_chain Internal.SnakyRows012D.named_envelope_609_34_last Internal.SnakyRows012D.named_envelope_609_41_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_33_head : (named_envelope_609_33.map Internal.SnakyRows012D.namedCellKey).head? = some (393 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_34 Internal.SnakyRows012D.named_envelope_609_41 (393 : ℤ) Internal.SnakyRows012D.named_envelope_609_34_head
theorem Internal.SnakyRows012D.named_envelope_609_33_last : (named_envelope_609_33.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1029 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_34 Internal.SnakyRows012D.named_envelope_609_41 (1029 : ℤ) Internal.SnakyRows012D.named_envelope_609_41_last
def Internal.SnakyRows012D.named_envelope_609_51 : List Cell := ([(8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_51_chain : (named_envelope_609_51.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_51_head : (named_envelope_609_51.map Internal.SnakyRows012D.namedCellKey).head? = some (1030 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_51_last : (named_envelope_609_51.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1150 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_52 : List Cell := ([(9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_52_chain : (named_envelope_609_52.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_52_head : (named_envelope_609_52.map Internal.SnakyRows012D.namedCellKey).head? = some (1151 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_52_last : (named_envelope_609_52.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1161 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_50 : List Cell := Internal.SnakyRows012D.named_envelope_609_51 ++ Internal.SnakyRows012D.named_envelope_609_52
theorem Internal.SnakyRows012D.named_envelope_609_50_chain : (named_envelope_609_50.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_51 Internal.SnakyRows012D.named_envelope_609_52 (1150 : ℤ) (1151 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_51_chain Internal.SnakyRows012D.named_envelope_609_52_chain Internal.SnakyRows012D.named_envelope_609_51_last Internal.SnakyRows012D.named_envelope_609_52_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_50_head : (named_envelope_609_50.map Internal.SnakyRows012D.namedCellKey).head? = some (1030 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_51 Internal.SnakyRows012D.named_envelope_609_52 (1030 : ℤ) Internal.SnakyRows012D.named_envelope_609_51_head
theorem Internal.SnakyRows012D.named_envelope_609_50_last : (named_envelope_609_50.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1161 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_51 Internal.SnakyRows012D.named_envelope_609_52 (1161 : ℤ) Internal.SnakyRows012D.named_envelope_609_52_last
def Internal.SnakyRows012D.named_envelope_609_54 : List Cell := ([(9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_54_chain : (named_envelope_609_54.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_54_head : (named_envelope_609_54.map Internal.SnakyRows012D.namedCellKey).head? = some (1162 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_54_last : (named_envelope_609_54.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1283 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_55 : List Cell := ([(10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_55_chain : (named_envelope_609_55.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_55_head : (named_envelope_609_55.map Internal.SnakyRows012D.namedCellKey).head? = some (1284 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_55_last : (named_envelope_609_55.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1407 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_53 : List Cell := Internal.SnakyRows012D.named_envelope_609_54 ++ Internal.SnakyRows012D.named_envelope_609_55
theorem Internal.SnakyRows012D.named_envelope_609_53_chain : (named_envelope_609_53.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_54 Internal.SnakyRows012D.named_envelope_609_55 (1283 : ℤ) (1284 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_54_chain Internal.SnakyRows012D.named_envelope_609_55_chain Internal.SnakyRows012D.named_envelope_609_54_last Internal.SnakyRows012D.named_envelope_609_55_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_53_head : (named_envelope_609_53.map Internal.SnakyRows012D.namedCellKey).head? = some (1162 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_54 Internal.SnakyRows012D.named_envelope_609_55 (1162 : ℤ) Internal.SnakyRows012D.named_envelope_609_54_head
theorem Internal.SnakyRows012D.named_envelope_609_53_last : (named_envelope_609_53.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1407 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_54 Internal.SnakyRows012D.named_envelope_609_55 (1407 : ℤ) Internal.SnakyRows012D.named_envelope_609_55_last
def Internal.SnakyRows012D.named_envelope_609_49 : List Cell := Internal.SnakyRows012D.named_envelope_609_50 ++ Internal.SnakyRows012D.named_envelope_609_53
theorem Internal.SnakyRows012D.named_envelope_609_49_chain : (named_envelope_609_49.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_50 Internal.SnakyRows012D.named_envelope_609_53 (1161 : ℤ) (1162 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_50_chain Internal.SnakyRows012D.named_envelope_609_53_chain Internal.SnakyRows012D.named_envelope_609_50_last Internal.SnakyRows012D.named_envelope_609_53_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_49_head : (named_envelope_609_49.map Internal.SnakyRows012D.namedCellKey).head? = some (1030 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_50 Internal.SnakyRows012D.named_envelope_609_53 (1030 : ℤ) Internal.SnakyRows012D.named_envelope_609_50_head
theorem Internal.SnakyRows012D.named_envelope_609_49_last : (named_envelope_609_49.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1407 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_50 Internal.SnakyRows012D.named_envelope_609_53 (1407 : ℤ) Internal.SnakyRows012D.named_envelope_609_53_last
def Internal.SnakyRows012D.named_envelope_609_58 : List Cell := ([(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_58_chain : (named_envelope_609_58.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_58_head : (named_envelope_609_58.map Internal.SnakyRows012D.namedCellKey).head? = some (1408 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_58_last : (named_envelope_609_58.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1533 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_59 : List Cell := ([(12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_59_chain : (named_envelope_609_59.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_59_head : (named_envelope_609_59.map Internal.SnakyRows012D.namedCellKey).head? = some (1534 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_59_last : (named_envelope_609_59.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1660 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_57 : List Cell := Internal.SnakyRows012D.named_envelope_609_58 ++ Internal.SnakyRows012D.named_envelope_609_59
theorem Internal.SnakyRows012D.named_envelope_609_57_chain : (named_envelope_609_57.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_58 Internal.SnakyRows012D.named_envelope_609_59 (1533 : ℤ) (1534 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_58_chain Internal.SnakyRows012D.named_envelope_609_59_chain Internal.SnakyRows012D.named_envelope_609_58_last Internal.SnakyRows012D.named_envelope_609_59_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_57_head : (named_envelope_609_57.map Internal.SnakyRows012D.namedCellKey).head? = some (1408 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_58 Internal.SnakyRows012D.named_envelope_609_59 (1408 : ℤ) Internal.SnakyRows012D.named_envelope_609_58_head
theorem Internal.SnakyRows012D.named_envelope_609_57_last : (named_envelope_609_57.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1660 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_58 Internal.SnakyRows012D.named_envelope_609_59 (1660 : ℤ) Internal.SnakyRows012D.named_envelope_609_59_last
def Internal.SnakyRows012D.named_envelope_609_61 : List Cell := ([(13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_61_chain : (named_envelope_609_61.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_61_head : (named_envelope_609_61.map Internal.SnakyRows012D.namedCellKey).head? = some (1661 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_61_last : (named_envelope_609_61.map Internal.SnakyRows012D.namedCellKey).getLast? = some (1790 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_62 : List Cell := ([(14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)] : List Cell)
theorem Internal.SnakyRows012D.named_envelope_609_62_chain : (named_envelope_609_62.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_62_head : (named_envelope_609_62.map Internal.SnakyRows012D.namedCellKey).head? = some (1791 : ℤ) := by decide
theorem Internal.SnakyRows012D.named_envelope_609_62_last : (named_envelope_609_62.map Internal.SnakyRows012D.namedCellKey).getLast? = some (2048 : ℤ) := by decide
def Internal.SnakyRows012D.named_envelope_609_60 : List Cell := Internal.SnakyRows012D.named_envelope_609_61 ++ Internal.SnakyRows012D.named_envelope_609_62
theorem Internal.SnakyRows012D.named_envelope_609_60_chain : (named_envelope_609_60.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_61 Internal.SnakyRows012D.named_envelope_609_62 (1790 : ℤ) (1791 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_61_chain Internal.SnakyRows012D.named_envelope_609_62_chain Internal.SnakyRows012D.named_envelope_609_61_last Internal.SnakyRows012D.named_envelope_609_62_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_60_head : (named_envelope_609_60.map Internal.SnakyRows012D.namedCellKey).head? = some (1661 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_61 Internal.SnakyRows012D.named_envelope_609_62 (1661 : ℤ) Internal.SnakyRows012D.named_envelope_609_61_head
theorem Internal.SnakyRows012D.named_envelope_609_60_last : (named_envelope_609_60.map Internal.SnakyRows012D.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_61 Internal.SnakyRows012D.named_envelope_609_62 (2048 : ℤ) Internal.SnakyRows012D.named_envelope_609_62_last
def Internal.SnakyRows012D.named_envelope_609_56 : List Cell := Internal.SnakyRows012D.named_envelope_609_57 ++ Internal.SnakyRows012D.named_envelope_609_60
theorem Internal.SnakyRows012D.named_envelope_609_56_chain : (named_envelope_609_56.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_57 Internal.SnakyRows012D.named_envelope_609_60 (1660 : ℤ) (1661 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_57_chain Internal.SnakyRows012D.named_envelope_609_60_chain Internal.SnakyRows012D.named_envelope_609_57_last Internal.SnakyRows012D.named_envelope_609_60_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_56_head : (named_envelope_609_56.map Internal.SnakyRows012D.namedCellKey).head? = some (1408 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_57 Internal.SnakyRows012D.named_envelope_609_60 (1408 : ℤ) Internal.SnakyRows012D.named_envelope_609_57_head
theorem Internal.SnakyRows012D.named_envelope_609_56_last : (named_envelope_609_56.map Internal.SnakyRows012D.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_57 Internal.SnakyRows012D.named_envelope_609_60 (2048 : ℤ) Internal.SnakyRows012D.named_envelope_609_60_last
def Internal.SnakyRows012D.named_envelope_609_48 : List Cell := Internal.SnakyRows012D.named_envelope_609_49 ++ Internal.SnakyRows012D.named_envelope_609_56
theorem Internal.SnakyRows012D.named_envelope_609_48_chain : (named_envelope_609_48.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_49 Internal.SnakyRows012D.named_envelope_609_56 (1407 : ℤ) (1408 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_49_chain Internal.SnakyRows012D.named_envelope_609_56_chain Internal.SnakyRows012D.named_envelope_609_49_last Internal.SnakyRows012D.named_envelope_609_56_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_48_head : (named_envelope_609_48.map Internal.SnakyRows012D.namedCellKey).head? = some (1030 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_49 Internal.SnakyRows012D.named_envelope_609_56 (1030 : ℤ) Internal.SnakyRows012D.named_envelope_609_49_head
theorem Internal.SnakyRows012D.named_envelope_609_48_last : (named_envelope_609_48.map Internal.SnakyRows012D.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_49 Internal.SnakyRows012D.named_envelope_609_56 (2048 : ℤ) Internal.SnakyRows012D.named_envelope_609_56_last
def Internal.SnakyRows012D.named_envelope_609_32 : List Cell := Internal.SnakyRows012D.named_envelope_609_33 ++ Internal.SnakyRows012D.named_envelope_609_48
theorem Internal.SnakyRows012D.named_envelope_609_32_chain : (named_envelope_609_32.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_33 Internal.SnakyRows012D.named_envelope_609_48 (1029 : ℤ) (1030 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_33_chain Internal.SnakyRows012D.named_envelope_609_48_chain Internal.SnakyRows012D.named_envelope_609_33_last Internal.SnakyRows012D.named_envelope_609_48_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_32_head : (named_envelope_609_32.map Internal.SnakyRows012D.namedCellKey).head? = some (393 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_33 Internal.SnakyRows012D.named_envelope_609_48 (393 : ℤ) Internal.SnakyRows012D.named_envelope_609_33_head
theorem Internal.SnakyRows012D.named_envelope_609_32_last : (named_envelope_609_32.map Internal.SnakyRows012D.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_33 Internal.SnakyRows012D.named_envelope_609_48 (2048 : ℤ) Internal.SnakyRows012D.named_envelope_609_48_last
def Internal.SnakyRows012D.named_envelope_609_0 : List Cell := Internal.SnakyRows012D.named_envelope_609_1 ++ Internal.SnakyRows012D.named_envelope_609_32
theorem Internal.SnakyRows012D.named_envelope_609_0_chain : (named_envelope_609_0.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows012D.named_chain_append Internal.SnakyRows012D.named_envelope_609_1 Internal.SnakyRows012D.named_envelope_609_32 (392 : ℤ) (393 : ℤ)
    Internal.SnakyRows012D.named_envelope_609_1_chain Internal.SnakyRows012D.named_envelope_609_32_chain Internal.SnakyRows012D.named_envelope_609_1_last Internal.SnakyRows012D.named_envelope_609_32_head (by decide)
theorem Internal.SnakyRows012D.named_envelope_609_0_head : (named_envelope_609_0.map Internal.SnakyRows012D.namedCellKey).head? = some (-1282 : ℤ) :=
  Internal.SnakyRows012D.named_head_append Internal.SnakyRows012D.named_envelope_609_1 Internal.SnakyRows012D.named_envelope_609_32 (-1282 : ℤ) Internal.SnakyRows012D.named_envelope_609_1_head
theorem Internal.SnakyRows012D.named_envelope_609_0_last : (named_envelope_609_0.map Internal.SnakyRows012D.namedCellKey).getLast? = some (2048 : ℤ) :=
  Internal.SnakyRows012D.named_last_append Internal.SnakyRows012D.named_envelope_609_1 Internal.SnakyRows012D.named_envelope_609_32 (2048 : ℤ) Internal.SnakyRows012D.named_envelope_609_32_last
theorem Internal.SnakyRows012D.named_envelope_609_nodup : (Internal.SnakyRows012D.named_envelope_609_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows012D.named_nodup_of_chain Internal.SnakyRows012D.named_envelope_609_0 Internal.SnakyRows012D.named_envelope_609_0_chain
def envelope_609 : Finset Cell := ⟨(Internal.SnakyRows012D.named_envelope_609_0 : Multiset Cell), Internal.SnakyRows012D.named_envelope_609_nodup⟩
def childrenC_609 : Fin 8 → Finset Cell := ![(placedSet 4 (0, 1) required_286), (placedSet 3 (0, 1) required_107), (placedSet 4 (0, 1) required_532), (placedSet 0 (0, 1) required_542), (placedSet 3 (0, 1) required_221), (placedSet 4 (0, 1) required_562), (placedSet 4 (0, 1) required_575), (placedSet 1 (2, 0) required_604)]
def childrenD_609 : Fin 8 → Finset Cell := ![(placedSet 4 (0, 1) envelope_286), (placedSet 3 (0, 1) envelope_107), (placedSet 4 (0, 1) envelope_532), (placedSet 0 (0, 1) envelope_542), (placedSet 3 (0, 1) envelope_221), (placedSet 4 (0, 1) envelope_562), (placedSet 4 (0, 1) envelope_575), (placedSet 1 (2, 0) envelope_604)]
theorem common_sub_609 : commonEnvelope childrenD_609 ⊆ insert (0, 0) required_609 := by decide
theorem child_required_sub_609 : ∀ j, childrenC_609 j ⊆ insert (0, 0) required_609 := by decide
theorem Internal.SnakyRows012D.containment_609_0_points_0 :
    ∀ p ∈ ([(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_0_points_1 :
    ∀ p ∈ ([(2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_0 :
    placedSet 4 (0, 1) envelope_286 ⊆ envelope_609 := by
  apply Internal.SnakyRows012D.placedSet_subset_of_points
  change ∀ p ∈ ((([(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)] : List Cell) ++ ([(2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)] : List Cell))), placement 4 (0, 1) p ∈ envelope_609
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_0_points_0, Internal.SnakyRows012D.containment_609_0_points_1⟩
theorem Internal.SnakyRows012D.containment_609_1_points_0 :
    ∀ p ∈ ([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell), placement 3 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_1 :
    placedSet 3 (0, 1) envelope_107 ⊆ envelope_609 := by
  apply Internal.SnakyRows012D.placedSet_subset_of_points
  change ∀ p ∈ (([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)] : List Cell)), placement 3 (0, 1) p ∈ envelope_609
  exact Internal.SnakyRows012D.containment_609_1_points_0
theorem Internal.SnakyRows012D.containment_609_2_points_0 :
    ∀ p ∈ ([(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_2_points_1 :
    ∀ p ∈ ([(-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_2_points_2 :
    ∀ p ∈ ([(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_2_points_3 :
    ∀ p ∈ ([(4, 0), (4, 1), (5, -2), (5, 0), (5, 1)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_2 :
    placedSet 4 (0, 1) envelope_532 ⊆ envelope_609 := by
  apply Internal.SnakyRows012D.placedSet_subset_of_points
  change ∀ p ∈ ((([(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3)] : List Cell) ++ (([(-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) ++ (([(2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1)] : List Cell) ++ ([(4, 0), (4, 1), (5, -2), (5, 0), (5, 1)] : List Cell))))), placement 4 (0, 1) p ∈ envelope_609
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_2_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_2_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_2_points_2, Internal.SnakyRows012D.containment_609_2_points_3⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_3_points_0 :
    ∀ p ∈ ([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)] : List Cell), placement 0 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_3_points_1 :
    ∀ p ∈ ([(0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell), placement 0 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_3_points_2 :
    ∀ p ∈ ([(2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell), placement 0 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_3_points_3 :
    ∀ p ∈ ([(4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3)] : List Cell), placement 0 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_3_points_4 :
    ∀ p ∈ ([(7, 4)] : List Cell), placement 0 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩
theorem Internal.SnakyRows012D.containment_609_3 :
    placedSet 0 (0, 1) envelope_542 ⊆ envelope_609 := by
  apply Internal.SnakyRows012D.placedSet_subset_of_points
  change ∀ p ∈ ((([(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)] : List Cell) ++ (([(0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell) ++ (([(2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell) ++ (([(4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3)] : List Cell) ++ ([(7, 4)] : List Cell)))))), placement 0 (0, 1) p ∈ envelope_609
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_3_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_3_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_3_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_3_points_3, Internal.SnakyRows012D.containment_609_3_points_4⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_4_points_0 :
    ∀ p ∈ ([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell), placement 3 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_4_points_1 :
    ∀ p ∈ ([(3, 0), (3, 1), (4, 1)] : List Cell), placement 3 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_4 :
    placedSet 3 (0, 1) envelope_221 ⊆ envelope_609 := by
  apply Internal.SnakyRows012D.placedSet_subset_of_points
  change ∀ p ∈ ((([(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)] : List Cell) ++ ([(3, 0), (3, 1), (4, 1)] : List Cell))), placement 3 (0, 1) p ∈ envelope_609
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_4_points_0, Internal.SnakyRows012D.containment_609_4_points_1⟩
theorem Internal.SnakyRows012D.containment_609_5_points_0 :
    ∀ p ∈ ([(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_5_points_1 :
    ∀ p ∈ ([(0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -4)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_5_points_2 :
    ∀ p ∈ ([(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_5_points_3 :
    ∀ p ∈ ([(5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_5_points_4 :
    ∀ p ∈ ([(6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_5_points_5 :
    ∀ p ∈ ([(8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_5 :
    placedSet 4 (0, 1) envelope_562 ⊆ envelope_609 := by
  apply Internal.SnakyRows012D.placedSet_subset_of_points
  change ∀ p ∈ ((([(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)] : List Cell) ++ (([(0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -4)] : List Cell) ++ (([(3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) ++ (([(5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1)] : List Cell) ++ (([(6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0)] : List Cell) ++ ([(8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)] : List Cell))))))), placement 4 (0, 1) p ∈ envelope_609
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_5_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_5_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_5_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_5_points_3, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_5_points_4, Internal.SnakyRows012D.containment_609_5_points_5⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_0 :
    ∀ p ∈ ([(-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -2)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_1 :
    ∀ p ∈ ([(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_2 :
    ∀ p ∈ ([(-3, 6), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_3 :
    ∀ p ∈ ([(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_4 :
    ∀ p ∈ ([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_5 :
    ∀ p ∈ ([(3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_6 :
    ∀ p ∈ ([(5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_7 :
    ∀ p ∈ ([(7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6_points_8 :
    ∀ p ∈ ([(9, 0), (10, -3), (10, -2), (10, -1), (10, 0)] : List Cell), placement 4 (0, 1) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_6 :
    placedSet 4 (0, 1) envelope_575 ⊆ envelope_609 := by
  apply Internal.SnakyRows012D.placedSet_subset_of_points
  change ∀ p ∈ ((([(-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -2)] : List Cell) ++ (([(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5)] : List Cell) ++ (([(-3, 6), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell) ++ (([(0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) ++ (([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2)] : List Cell) ++ (([(3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1)] : List Cell) ++ (([(5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3)] : List Cell) ++ (([(7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1)] : List Cell) ++ ([(9, 0), (10, -3), (10, -2), (10, -1), (10, 0)] : List Cell)))))))))), placement 4 (0, 1) p ∈ envelope_609
  exact List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_0, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_1, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_2, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_3, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_4, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_5, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_6, List.forall_mem_append.mpr ⟨Internal.SnakyRows012D.containment_609_6_points_7, Internal.SnakyRows012D.containment_609_6_points_8⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_0 :
    ∀ p ∈ ([(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_1 :
    ∀ p ∈ ([(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -1), (-3, 0)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_2 :
    ∀ p ∈ ([(-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_3 :
    ∀ p ∈ ([(-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_4 :
    ∀ p ∈ ([(-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_5 :
    ∀ p ∈ ([(0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_6 :
    ∀ p ∈ ([(0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_7 :
    ∀ p ∈ ([(1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_8 :
    ∀ p ∈ ([(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_9 :
    ∀ p ∈ ([(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_10 :
    ∀ p ∈ ([(4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_11 :
    ∀ p ∈ ([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_12 :
    ∀ p ∈ ([(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_13 :
    ∀ p ∈ ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_14 :
    ∀ p ∈ ([(8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_15 :
    ∀ p ∈ ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_16 :
    ∀ p ∈ ([(10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7_points_17 :
    ∀ p ∈ ([(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)] : List Cell), placement 1 (2, 0) p ∈ envelope_609 := by
  exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyRows012D.containment_609_7 :
    placedSet 1 (2, 0) envelope_604 ⊆ envelope_609 := by decide +kernel
theorem child_envelope_sub_609 : ∀ j, childrenD_609 j ⊆ envelope_609 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows012D.containment_609_0
  · exact Internal.SnakyRows012D.containment_609_1
  · exact Internal.SnakyRows012D.containment_609_2
  · exact Internal.SnakyRows012D.containment_609_3
  · exact Internal.SnakyRows012D.containment_609_4
  · exact Internal.SnakyRows012D.containment_609_5
  · exact Internal.SnakyRows012D.containment_609_6
  · exact Internal.SnakyRows012D.containment_609_7
theorem pivot_mem_609 : (0, 0) ∈ envelope_609 := by decide
theorem children_work_609 : ∀ j, Template HasSnaky 30 (childrenC_609 j) (childrenD_609 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_286 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_107 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_532 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_542 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_221 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_562 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_575 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_604 1 (2, 0)).mono (by decide)
theorem row_works_609 : Template HasSnaky 31 required_609 envelope_609 := by
  refine compose HasSnaky 30 childrenC_609 childrenD_609 children_work_609 (0, 0)
    required_609 envelope_609 pivot_mem_609 child_required_sub_609 child_envelope_sub_609 ?_
  intro b hb; exact common_sub_609 (mem_commonEnvelope childrenD_609 b hb)
end SnakyConditional

end OAI
