import OAI.GameTheory.SnakyConditional.Regions.Region595
import OAI.GameTheory.SnakyConditional.Templates.Level16Part06
import OAI.GameTheory.SnakyConditional.Templates.Level18Part06
import OAI.GameTheory.SnakyConditional.Templates.Level24Part02

namespace OAI

namespace SnakyConditional
def required_591 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows010.named_envelope_591_4 : List Cell := ([(-10, -1), (-10, 0), (-10, 1), (-10, 2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-8, -4), (-8, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_4_chain : (named_envelope_591_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_4_head : (named_envelope_591_4.map Internal.SnakyRows010.namedCellKey).head? = some (-1281 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_4_last : (named_envelope_591_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-1026 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_5 : List Cell := ([(-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_5_chain : (named_envelope_591_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_5_head : (named_envelope_591_5.map Internal.SnakyRows010.namedCellKey).head? = some (-1025 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_5_last : (named_envelope_591_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-895 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_3 : List Cell := Internal.SnakyRows010.named_envelope_591_4 ++ Internal.SnakyRows010.named_envelope_591_5
theorem Internal.SnakyRows010.named_envelope_591_3_chain : (named_envelope_591_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_4 Internal.SnakyRows010.named_envelope_591_5 (-1026 : ℤ) (-1025 : ℤ)
    Internal.SnakyRows010.named_envelope_591_4_chain Internal.SnakyRows010.named_envelope_591_5_chain Internal.SnakyRows010.named_envelope_591_4_last Internal.SnakyRows010.named_envelope_591_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_3_head : (named_envelope_591_3.map Internal.SnakyRows010.namedCellKey).head? = some (-1281 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_4 Internal.SnakyRows010.named_envelope_591_5 (-1281 : ℤ) Internal.SnakyRows010.named_envelope_591_4_head
theorem Internal.SnakyRows010.named_envelope_591_3_last : (named_envelope_591_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-895 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_4 Internal.SnakyRows010.named_envelope_591_5 (-895 : ℤ) Internal.SnakyRows010.named_envelope_591_5_last
def Internal.SnakyRows010.named_envelope_591_7 : List Cell := ([(-7, 2), (-7, 3), (-7, 4), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_7_chain : (named_envelope_591_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_7_head : (named_envelope_591_7.map Internal.SnakyRows010.namedCellKey).head? = some (-894 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_7_last : (named_envelope_591_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-765 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_8 : List Cell := ([(-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_8_chain : (named_envelope_591_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_8_head : (named_envelope_591_8.map Internal.SnakyRows010.namedCellKey).head? = some (-764 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_8_last : (named_envelope_591_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-517 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_6 : List Cell := Internal.SnakyRows010.named_envelope_591_7 ++ Internal.SnakyRows010.named_envelope_591_8
theorem Internal.SnakyRows010.named_envelope_591_6_chain : (named_envelope_591_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_7 Internal.SnakyRows010.named_envelope_591_8 (-765 : ℤ) (-764 : ℤ)
    Internal.SnakyRows010.named_envelope_591_7_chain Internal.SnakyRows010.named_envelope_591_8_chain Internal.SnakyRows010.named_envelope_591_7_last Internal.SnakyRows010.named_envelope_591_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_6_head : (named_envelope_591_6.map Internal.SnakyRows010.namedCellKey).head? = some (-894 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_7 Internal.SnakyRows010.named_envelope_591_8 (-894 : ℤ) Internal.SnakyRows010.named_envelope_591_7_head
theorem Internal.SnakyRows010.named_envelope_591_6_last : (named_envelope_591_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-517 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_7 Internal.SnakyRows010.named_envelope_591_8 (-517 : ℤ) Internal.SnakyRows010.named_envelope_591_8_last
def Internal.SnakyRows010.named_envelope_591_2 : List Cell := Internal.SnakyRows010.named_envelope_591_3 ++ Internal.SnakyRows010.named_envelope_591_6
theorem Internal.SnakyRows010.named_envelope_591_2_chain : (named_envelope_591_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_3 Internal.SnakyRows010.named_envelope_591_6 (-895 : ℤ) (-894 : ℤ)
    Internal.SnakyRows010.named_envelope_591_3_chain Internal.SnakyRows010.named_envelope_591_6_chain Internal.SnakyRows010.named_envelope_591_3_last Internal.SnakyRows010.named_envelope_591_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_2_head : (named_envelope_591_2.map Internal.SnakyRows010.namedCellKey).head? = some (-1281 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_3 Internal.SnakyRows010.named_envelope_591_6 (-1281 : ℤ) Internal.SnakyRows010.named_envelope_591_3_head
theorem Internal.SnakyRows010.named_envelope_591_2_last : (named_envelope_591_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-517 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_3 Internal.SnakyRows010.named_envelope_591_6 (-517 : ℤ) Internal.SnakyRows010.named_envelope_591_6_last
def Internal.SnakyRows010.named_envelope_591_11 : List Cell := ([(-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_11_chain : (named_envelope_591_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_11_head : (named_envelope_591_11.map Internal.SnakyRows010.namedCellKey).head? = some (-516 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_11_last : (named_envelope_591_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (-387 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_12 : List Cell := ([(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -4), (-2, -3), (-2, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_12_chain : (named_envelope_591_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_12_head : (named_envelope_591_12.map Internal.SnakyRows010.namedCellKey).head? = some (-386 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_12_last : (named_envelope_591_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (-258 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_10 : List Cell := Internal.SnakyRows010.named_envelope_591_11 ++ Internal.SnakyRows010.named_envelope_591_12
theorem Internal.SnakyRows010.named_envelope_591_10_chain : (named_envelope_591_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_11 Internal.SnakyRows010.named_envelope_591_12 (-387 : ℤ) (-386 : ℤ)
    Internal.SnakyRows010.named_envelope_591_11_chain Internal.SnakyRows010.named_envelope_591_12_chain Internal.SnakyRows010.named_envelope_591_11_last Internal.SnakyRows010.named_envelope_591_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_10_head : (named_envelope_591_10.map Internal.SnakyRows010.namedCellKey).head? = some (-516 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_11 Internal.SnakyRows010.named_envelope_591_12 (-516 : ℤ) Internal.SnakyRows010.named_envelope_591_11_head
theorem Internal.SnakyRows010.named_envelope_591_10_last : (named_envelope_591_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (-258 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_11 Internal.SnakyRows010.named_envelope_591_12 (-258 : ℤ) Internal.SnakyRows010.named_envelope_591_12_last
def Internal.SnakyRows010.named_envelope_591_14 : List Cell := ([(-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -5), (-1, -4), (-1, -3), (-1, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_14_chain : (named_envelope_591_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_14_head : (named_envelope_591_14.map Internal.SnakyRows010.namedCellKey).head? = some (-257 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_14_last : (named_envelope_591_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (-129 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_15 : List Cell := ([(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_15_chain : (named_envelope_591_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_15_head : (named_envelope_591_15.map Internal.SnakyRows010.namedCellKey).head? = some (-128 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_15_last : (named_envelope_591_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (-1 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_13 : List Cell := Internal.SnakyRows010.named_envelope_591_14 ++ Internal.SnakyRows010.named_envelope_591_15
theorem Internal.SnakyRows010.named_envelope_591_13_chain : (named_envelope_591_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_14 Internal.SnakyRows010.named_envelope_591_15 (-129 : ℤ) (-128 : ℤ)
    Internal.SnakyRows010.named_envelope_591_14_chain Internal.SnakyRows010.named_envelope_591_15_chain Internal.SnakyRows010.named_envelope_591_14_last Internal.SnakyRows010.named_envelope_591_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_13_head : (named_envelope_591_13.map Internal.SnakyRows010.namedCellKey).head? = some (-257 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_14 Internal.SnakyRows010.named_envelope_591_15 (-257 : ℤ) Internal.SnakyRows010.named_envelope_591_14_head
theorem Internal.SnakyRows010.named_envelope_591_13_last : (named_envelope_591_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (-1 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_14 Internal.SnakyRows010.named_envelope_591_15 (-1 : ℤ) Internal.SnakyRows010.named_envelope_591_15_last
def Internal.SnakyRows010.named_envelope_591_9 : List Cell := Internal.SnakyRows010.named_envelope_591_10 ++ Internal.SnakyRows010.named_envelope_591_13
theorem Internal.SnakyRows010.named_envelope_591_9_chain : (named_envelope_591_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_10 Internal.SnakyRows010.named_envelope_591_13 (-258 : ℤ) (-257 : ℤ)
    Internal.SnakyRows010.named_envelope_591_10_chain Internal.SnakyRows010.named_envelope_591_13_chain Internal.SnakyRows010.named_envelope_591_10_last Internal.SnakyRows010.named_envelope_591_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_9_head : (named_envelope_591_9.map Internal.SnakyRows010.namedCellKey).head? = some (-516 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_10 Internal.SnakyRows010.named_envelope_591_13 (-516 : ℤ) Internal.SnakyRows010.named_envelope_591_10_head
theorem Internal.SnakyRows010.named_envelope_591_9_last : (named_envelope_591_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (-1 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_10 Internal.SnakyRows010.named_envelope_591_13 (-1 : ℤ) Internal.SnakyRows010.named_envelope_591_13_last
def Internal.SnakyRows010.named_envelope_591_1 : List Cell := Internal.SnakyRows010.named_envelope_591_2 ++ Internal.SnakyRows010.named_envelope_591_9
theorem Internal.SnakyRows010.named_envelope_591_1_chain : (named_envelope_591_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_2 Internal.SnakyRows010.named_envelope_591_9 (-517 : ℤ) (-516 : ℤ)
    Internal.SnakyRows010.named_envelope_591_2_chain Internal.SnakyRows010.named_envelope_591_9_chain Internal.SnakyRows010.named_envelope_591_2_last Internal.SnakyRows010.named_envelope_591_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_1_head : (named_envelope_591_1.map Internal.SnakyRows010.namedCellKey).head? = some (-1281 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_2 Internal.SnakyRows010.named_envelope_591_9 (-1281 : ℤ) Internal.SnakyRows010.named_envelope_591_2_head
theorem Internal.SnakyRows010.named_envelope_591_1_last : (named_envelope_591_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (-1 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_2 Internal.SnakyRows010.named_envelope_591_9 (-1 : ℤ) Internal.SnakyRows010.named_envelope_591_9_last
def Internal.SnakyRows010.named_envelope_591_19 : List Cell := ([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_19_chain : (named_envelope_591_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_19_head : (named_envelope_591_19.map Internal.SnakyRows010.namedCellKey).head? = some (0 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_19_last : (named_envelope_591_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (129 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_20 : List Cell := ([(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_20_chain : (named_envelope_591_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_20_head : (named_envelope_591_20.map Internal.SnakyRows010.namedCellKey).head? = some (130 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_20_last : (named_envelope_591_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (257 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_18 : List Cell := Internal.SnakyRows010.named_envelope_591_19 ++ Internal.SnakyRows010.named_envelope_591_20
theorem Internal.SnakyRows010.named_envelope_591_18_chain : (named_envelope_591_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_19 Internal.SnakyRows010.named_envelope_591_20 (129 : ℤ) (130 : ℤ)
    Internal.SnakyRows010.named_envelope_591_19_chain Internal.SnakyRows010.named_envelope_591_20_chain Internal.SnakyRows010.named_envelope_591_19_last Internal.SnakyRows010.named_envelope_591_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_18_head : (named_envelope_591_18.map Internal.SnakyRows010.namedCellKey).head? = some (0 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_19 Internal.SnakyRows010.named_envelope_591_20 (0 : ℤ) Internal.SnakyRows010.named_envelope_591_19_head
theorem Internal.SnakyRows010.named_envelope_591_18_last : (named_envelope_591_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (257 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_19 Internal.SnakyRows010.named_envelope_591_20 (257 : ℤ) Internal.SnakyRows010.named_envelope_591_20_last
def Internal.SnakyRows010.named_envelope_591_22 : List Cell := ([(2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_22_chain : (named_envelope_591_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_22_head : (named_envelope_591_22.map Internal.SnakyRows010.namedCellKey).head? = some (258 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_22_last : (named_envelope_591_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (386 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_23 : List Cell := ([(3, 3), (3, 4), (3, 5), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_23_chain : (named_envelope_591_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_23_head : (named_envelope_591_23.map Internal.SnakyRows010.namedCellKey).head? = some (387 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_23_last : (named_envelope_591_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (514 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_21 : List Cell := Internal.SnakyRows010.named_envelope_591_22 ++ Internal.SnakyRows010.named_envelope_591_23
theorem Internal.SnakyRows010.named_envelope_591_21_chain : (named_envelope_591_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_22 Internal.SnakyRows010.named_envelope_591_23 (386 : ℤ) (387 : ℤ)
    Internal.SnakyRows010.named_envelope_591_22_chain Internal.SnakyRows010.named_envelope_591_23_chain Internal.SnakyRows010.named_envelope_591_22_last Internal.SnakyRows010.named_envelope_591_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_21_head : (named_envelope_591_21.map Internal.SnakyRows010.namedCellKey).head? = some (258 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_22 Internal.SnakyRows010.named_envelope_591_23 (258 : ℤ) Internal.SnakyRows010.named_envelope_591_22_head
theorem Internal.SnakyRows010.named_envelope_591_21_last : (named_envelope_591_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (514 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_22 Internal.SnakyRows010.named_envelope_591_23 (514 : ℤ) Internal.SnakyRows010.named_envelope_591_23_last
def Internal.SnakyRows010.named_envelope_591_17 : List Cell := Internal.SnakyRows010.named_envelope_591_18 ++ Internal.SnakyRows010.named_envelope_591_21
theorem Internal.SnakyRows010.named_envelope_591_17_chain : (named_envelope_591_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_18 Internal.SnakyRows010.named_envelope_591_21 (257 : ℤ) (258 : ℤ)
    Internal.SnakyRows010.named_envelope_591_18_chain Internal.SnakyRows010.named_envelope_591_21_chain Internal.SnakyRows010.named_envelope_591_18_last Internal.SnakyRows010.named_envelope_591_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_17_head : (named_envelope_591_17.map Internal.SnakyRows010.namedCellKey).head? = some (0 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_18 Internal.SnakyRows010.named_envelope_591_21 (0 : ℤ) Internal.SnakyRows010.named_envelope_591_18_head
theorem Internal.SnakyRows010.named_envelope_591_17_last : (named_envelope_591_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (514 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_18 Internal.SnakyRows010.named_envelope_591_21 (514 : ℤ) Internal.SnakyRows010.named_envelope_591_21_last
def Internal.SnakyRows010.named_envelope_591_26 : List Cell := ([(4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_26_chain : (named_envelope_591_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_26_head : (named_envelope_591_26.map Internal.SnakyRows010.namedCellKey).head? = some (515 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_26_last : (named_envelope_591_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (644 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_27 : List Cell := ([(6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_27_chain : (named_envelope_591_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_27_head : (named_envelope_591_27.map Internal.SnakyRows010.namedCellKey).head? = some (764 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_27_last : (named_envelope_591_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (892 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_25 : List Cell := Internal.SnakyRows010.named_envelope_591_26 ++ Internal.SnakyRows010.named_envelope_591_27
theorem Internal.SnakyRows010.named_envelope_591_25_chain : (named_envelope_591_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_26 Internal.SnakyRows010.named_envelope_591_27 (644 : ℤ) (764 : ℤ)
    Internal.SnakyRows010.named_envelope_591_26_chain Internal.SnakyRows010.named_envelope_591_27_chain Internal.SnakyRows010.named_envelope_591_26_last Internal.SnakyRows010.named_envelope_591_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_25_head : (named_envelope_591_25.map Internal.SnakyRows010.namedCellKey).head? = some (515 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_26 Internal.SnakyRows010.named_envelope_591_27 (515 : ℤ) Internal.SnakyRows010.named_envelope_591_26_head
theorem Internal.SnakyRows010.named_envelope_591_25_last : (named_envelope_591_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (892 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_26 Internal.SnakyRows010.named_envelope_591_27 (892 : ℤ) Internal.SnakyRows010.named_envelope_591_27_last
def Internal.SnakyRows010.named_envelope_591_29 : List Cell := ([(7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -4), (8, -2), (8, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_29_chain : (named_envelope_591_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_29_head : (named_envelope_591_29.map Internal.SnakyRows010.namedCellKey).head? = some (893 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_29_last : (named_envelope_591_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (1023 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_30 : List Cell := ([(8, 0), (8, 1), (8, 2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_591_30_chain : (named_envelope_591_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_591_30_head : (named_envelope_591_30.map Internal.SnakyRows010.namedCellKey).head? = some (1024 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_591_30_last : (named_envelope_591_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1282 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_591_28 : List Cell := Internal.SnakyRows010.named_envelope_591_29 ++ Internal.SnakyRows010.named_envelope_591_30
theorem Internal.SnakyRows010.named_envelope_591_28_chain : (named_envelope_591_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_29 Internal.SnakyRows010.named_envelope_591_30 (1023 : ℤ) (1024 : ℤ)
    Internal.SnakyRows010.named_envelope_591_29_chain Internal.SnakyRows010.named_envelope_591_30_chain Internal.SnakyRows010.named_envelope_591_29_last Internal.SnakyRows010.named_envelope_591_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_28_head : (named_envelope_591_28.map Internal.SnakyRows010.namedCellKey).head? = some (893 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_29 Internal.SnakyRows010.named_envelope_591_30 (893 : ℤ) Internal.SnakyRows010.named_envelope_591_29_head
theorem Internal.SnakyRows010.named_envelope_591_28_last : (named_envelope_591_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1282 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_29 Internal.SnakyRows010.named_envelope_591_30 (1282 : ℤ) Internal.SnakyRows010.named_envelope_591_30_last
def Internal.SnakyRows010.named_envelope_591_24 : List Cell := Internal.SnakyRows010.named_envelope_591_25 ++ Internal.SnakyRows010.named_envelope_591_28
theorem Internal.SnakyRows010.named_envelope_591_24_chain : (named_envelope_591_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_25 Internal.SnakyRows010.named_envelope_591_28 (892 : ℤ) (893 : ℤ)
    Internal.SnakyRows010.named_envelope_591_25_chain Internal.SnakyRows010.named_envelope_591_28_chain Internal.SnakyRows010.named_envelope_591_25_last Internal.SnakyRows010.named_envelope_591_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_24_head : (named_envelope_591_24.map Internal.SnakyRows010.namedCellKey).head? = some (515 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_25 Internal.SnakyRows010.named_envelope_591_28 (515 : ℤ) Internal.SnakyRows010.named_envelope_591_25_head
theorem Internal.SnakyRows010.named_envelope_591_24_last : (named_envelope_591_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1282 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_25 Internal.SnakyRows010.named_envelope_591_28 (1282 : ℤ) Internal.SnakyRows010.named_envelope_591_28_last
def Internal.SnakyRows010.named_envelope_591_16 : List Cell := Internal.SnakyRows010.named_envelope_591_17 ++ Internal.SnakyRows010.named_envelope_591_24
theorem Internal.SnakyRows010.named_envelope_591_16_chain : (named_envelope_591_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_17 Internal.SnakyRows010.named_envelope_591_24 (514 : ℤ) (515 : ℤ)
    Internal.SnakyRows010.named_envelope_591_17_chain Internal.SnakyRows010.named_envelope_591_24_chain Internal.SnakyRows010.named_envelope_591_17_last Internal.SnakyRows010.named_envelope_591_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_16_head : (named_envelope_591_16.map Internal.SnakyRows010.namedCellKey).head? = some (0 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_17 Internal.SnakyRows010.named_envelope_591_24 (0 : ℤ) Internal.SnakyRows010.named_envelope_591_17_head
theorem Internal.SnakyRows010.named_envelope_591_16_last : (named_envelope_591_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1282 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_17 Internal.SnakyRows010.named_envelope_591_24 (1282 : ℤ) Internal.SnakyRows010.named_envelope_591_24_last
def Internal.SnakyRows010.named_envelope_591_0 : List Cell := Internal.SnakyRows010.named_envelope_591_1 ++ Internal.SnakyRows010.named_envelope_591_16
theorem Internal.SnakyRows010.named_envelope_591_0_chain : (named_envelope_591_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_591_1 Internal.SnakyRows010.named_envelope_591_16 (-1 : ℤ) (0 : ℤ)
    Internal.SnakyRows010.named_envelope_591_1_chain Internal.SnakyRows010.named_envelope_591_16_chain Internal.SnakyRows010.named_envelope_591_1_last Internal.SnakyRows010.named_envelope_591_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_591_0_head : (named_envelope_591_0.map Internal.SnakyRows010.namedCellKey).head? = some (-1281 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_591_1 Internal.SnakyRows010.named_envelope_591_16 (-1281 : ℤ) Internal.SnakyRows010.named_envelope_591_1_head
theorem Internal.SnakyRows010.named_envelope_591_0_last : (named_envelope_591_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1282 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_591_1 Internal.SnakyRows010.named_envelope_591_16 (1282 : ℤ) Internal.SnakyRows010.named_envelope_591_16_last
theorem Internal.SnakyRows010.named_envelope_591_nodup : (Internal.SnakyRows010.named_envelope_591_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_591_0 Internal.SnakyRows010.named_envelope_591_0_chain
def envelope_591 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_591_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_591_nodup⟩
def childrenC_591 : Fin 6 → Finset Cell := ![(placedSet 0 (0, 1) required_524), (placedSet 1 (0, -3) required_529), (placedSet 3 (0, -3) required_529), (placedSet 1 (0, -3) required_538), (placedSet 3 (0, -3) required_538), (placedSet 5 (0, -3) required_197)]
def childrenD_591 : Fin 6 → Finset Cell := ![(placedSet 0 (0, 1) envelope_524), (placedSet 1 (0, -3) envelope_529), (placedSet 3 (0, -3) envelope_529), (placedSet 1 (0, -3) envelope_538), (placedSet 3 (0, -3) envelope_538), (placedSet 5 (0, -3) envelope_197)]
theorem common_sub_591 : commonEnvelope childrenD_591 ⊆ insert (0, 0) required_591 := by decide
theorem child_required_sub_591 : ∀ j, childrenC_591 j ⊆ insert (0, 0) required_591 := by decide
theorem Internal.SnakyRows010.containment_591_0 :
    placedSet 0 (0, 1) envelope_524 ⊆ envelope_591 := by decide
theorem Internal.SnakyRows010.containment_591_1 :
    placedSet 1 (0, -3) envelope_529 ⊆ envelope_591 := by decide
theorem Internal.SnakyRows010.containment_591_2 :
    placedSet 3 (0, -3) envelope_529 ⊆ envelope_591 := by decide
theorem Internal.SnakyRows010.containment_591_3 :
    placedSet 1 (0, -3) envelope_538 ⊆ envelope_591 := by decide +kernel
theorem Internal.SnakyRows010.containment_591_4 :
    placedSet 3 (0, -3) envelope_538 ⊆ envelope_591 := by decide
theorem Internal.SnakyRows010.containment_591_5 :
    placedSet 5 (0, -3) envelope_197 ⊆ envelope_591 := by decide
theorem child_envelope_sub_591 : ∀ j, childrenD_591 j ⊆ envelope_591 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_591_0
  · exact Internal.SnakyRows010.containment_591_1
  · exact Internal.SnakyRows010.containment_591_2
  · exact Internal.SnakyRows010.containment_591_3
  · exact Internal.SnakyRows010.containment_591_4
  · exact Internal.SnakyRows010.containment_591_5
theorem pivot_mem_591 : (0, 0) ∈ envelope_591 := by decide
theorem children_work_591 : ∀ j, Template HasSnaky 22 (childrenC_591 j) (childrenD_591 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_524 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_529 1 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_529 3 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_538 1 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_538 3 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_197 5 (0, -3)).mono (by decide)
theorem row_works_591 : Template HasSnaky 23 required_591 envelope_591 := by
  refine compose HasSnaky 22 childrenC_591 childrenD_591 children_work_591 (0, 0)
    required_591 envelope_591 pivot_mem_591 child_required_sub_591 child_envelope_sub_591 ?_
  intro b hb; exact common_sub_591 (mem_commonEnvelope childrenD_591 b hb)
end SnakyConditional

end OAI
