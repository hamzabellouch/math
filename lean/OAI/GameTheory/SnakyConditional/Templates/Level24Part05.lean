import OAI.GameTheory.SnakyConditional.Regions.Region595
import OAI.GameTheory.SnakyConditional.Templates.Level18Part05
import OAI.GameTheory.SnakyConditional.Templates.Level23Part01
import OAI.GameTheory.SnakyConditional.Templates.Level23Part04

namespace OAI

namespace SnakyConditional
def required_587 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows010.named_envelope_587_4 : List Cell := ([(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_4_chain : (named_envelope_587_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_4_head : (named_envelope_587_4.map Internal.SnakyRows010.namedCellKey).head? = some (-898 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_4_last : (named_envelope_587_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-644 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_5 : List Cell := ([(-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -6), (-4, -5), (-4, -4), (-4, -3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_5_chain : (named_envelope_587_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_5_head : (named_envelope_587_5.map Internal.SnakyRows010.namedCellKey).head? = some (-643 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_5_last : (named_envelope_587_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-515 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_3 : List Cell := Internal.SnakyRows010.named_envelope_587_4 ++ Internal.SnakyRows010.named_envelope_587_5
theorem Internal.SnakyRows010.named_envelope_587_3_chain : (named_envelope_587_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_4 Internal.SnakyRows010.named_envelope_587_5 (-644 : ℤ) (-643 : ℤ)
    Internal.SnakyRows010.named_envelope_587_4_chain Internal.SnakyRows010.named_envelope_587_5_chain Internal.SnakyRows010.named_envelope_587_4_last Internal.SnakyRows010.named_envelope_587_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_3_head : (named_envelope_587_3.map Internal.SnakyRows010.namedCellKey).head? = some (-898 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_4 Internal.SnakyRows010.named_envelope_587_5 (-898 : ℤ) Internal.SnakyRows010.named_envelope_587_4_head
theorem Internal.SnakyRows010.named_envelope_587_3_last : (named_envelope_587_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-515 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_4 Internal.SnakyRows010.named_envelope_587_5 (-515 : ℤ) Internal.SnakyRows010.named_envelope_587_5_last
def Internal.SnakyRows010.named_envelope_587_7 : List Cell := ([(-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -6), (-3, -5), (-3, -4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_7_chain : (named_envelope_587_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_7_head : (named_envelope_587_7.map Internal.SnakyRows010.namedCellKey).head? = some (-514 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_7_last : (named_envelope_587_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-388 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_8 : List Cell := ([(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -6), (-2, -5), (-2, -4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_8_chain : (named_envelope_587_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_8_head : (named_envelope_587_8.map Internal.SnakyRows010.namedCellKey).head? = some (-387 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_8_last : (named_envelope_587_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-260 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_6 : List Cell := Internal.SnakyRows010.named_envelope_587_7 ++ Internal.SnakyRows010.named_envelope_587_8
theorem Internal.SnakyRows010.named_envelope_587_6_chain : (named_envelope_587_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_7 Internal.SnakyRows010.named_envelope_587_8 (-388 : ℤ) (-387 : ℤ)
    Internal.SnakyRows010.named_envelope_587_7_chain Internal.SnakyRows010.named_envelope_587_8_chain Internal.SnakyRows010.named_envelope_587_7_last Internal.SnakyRows010.named_envelope_587_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_6_head : (named_envelope_587_6.map Internal.SnakyRows010.namedCellKey).head? = some (-514 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_7 Internal.SnakyRows010.named_envelope_587_8 (-514 : ℤ) Internal.SnakyRows010.named_envelope_587_7_head
theorem Internal.SnakyRows010.named_envelope_587_6_last : (named_envelope_587_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-260 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_7 Internal.SnakyRows010.named_envelope_587_8 (-260 : ℤ) Internal.SnakyRows010.named_envelope_587_8_last
def Internal.SnakyRows010.named_envelope_587_2 : List Cell := Internal.SnakyRows010.named_envelope_587_3 ++ Internal.SnakyRows010.named_envelope_587_6
theorem Internal.SnakyRows010.named_envelope_587_2_chain : (named_envelope_587_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_3 Internal.SnakyRows010.named_envelope_587_6 (-515 : ℤ) (-514 : ℤ)
    Internal.SnakyRows010.named_envelope_587_3_chain Internal.SnakyRows010.named_envelope_587_6_chain Internal.SnakyRows010.named_envelope_587_3_last Internal.SnakyRows010.named_envelope_587_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_2_head : (named_envelope_587_2.map Internal.SnakyRows010.namedCellKey).head? = some (-898 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_3 Internal.SnakyRows010.named_envelope_587_6 (-898 : ℤ) Internal.SnakyRows010.named_envelope_587_3_head
theorem Internal.SnakyRows010.named_envelope_587_2_last : (named_envelope_587_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-260 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_3 Internal.SnakyRows010.named_envelope_587_6 (-260 : ℤ) Internal.SnakyRows010.named_envelope_587_6_last
def Internal.SnakyRows010.named_envelope_587_11 : List Cell := ([(-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_11_chain : (named_envelope_587_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_11_head : (named_envelope_587_11.map Internal.SnakyRows010.namedCellKey).head? = some (-259 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_11_last : (named_envelope_587_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (-133 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_12 : List Cell := ([(-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_12_chain : (named_envelope_587_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_12_head : (named_envelope_587_12.map Internal.SnakyRows010.namedCellKey).head? = some (-132 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_12_last : (named_envelope_587_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (-5 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_10 : List Cell := Internal.SnakyRows010.named_envelope_587_11 ++ Internal.SnakyRows010.named_envelope_587_12
theorem Internal.SnakyRows010.named_envelope_587_10_chain : (named_envelope_587_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_11 Internal.SnakyRows010.named_envelope_587_12 (-133 : ℤ) (-132 : ℤ)
    Internal.SnakyRows010.named_envelope_587_11_chain Internal.SnakyRows010.named_envelope_587_12_chain Internal.SnakyRows010.named_envelope_587_11_last Internal.SnakyRows010.named_envelope_587_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_10_head : (named_envelope_587_10.map Internal.SnakyRows010.namedCellKey).head? = some (-259 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_11 Internal.SnakyRows010.named_envelope_587_12 (-259 : ℤ) Internal.SnakyRows010.named_envelope_587_11_head
theorem Internal.SnakyRows010.named_envelope_587_10_last : (named_envelope_587_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (-5 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_11 Internal.SnakyRows010.named_envelope_587_12 (-5 : ℤ) Internal.SnakyRows010.named_envelope_587_12_last
def Internal.SnakyRows010.named_envelope_587_14 : List Cell := ([(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_14_chain : (named_envelope_587_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_14_head : (named_envelope_587_14.map Internal.SnakyRows010.namedCellKey).head? = some (-4 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_14_last : (named_envelope_587_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (125 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_15 : List Cell := ([(1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -7), (2, -6), (2, -5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_15_chain : (named_envelope_587_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_15_head : (named_envelope_587_15.map Internal.SnakyRows010.namedCellKey).head? = some (126 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_15_last : (named_envelope_587_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_13 : List Cell := Internal.SnakyRows010.named_envelope_587_14 ++ Internal.SnakyRows010.named_envelope_587_15
theorem Internal.SnakyRows010.named_envelope_587_13_chain : (named_envelope_587_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_14 Internal.SnakyRows010.named_envelope_587_15 (125 : ℤ) (126 : ℤ)
    Internal.SnakyRows010.named_envelope_587_14_chain Internal.SnakyRows010.named_envelope_587_15_chain Internal.SnakyRows010.named_envelope_587_14_last Internal.SnakyRows010.named_envelope_587_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_13_head : (named_envelope_587_13.map Internal.SnakyRows010.namedCellKey).head? = some (-4 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_14 Internal.SnakyRows010.named_envelope_587_15 (-4 : ℤ) Internal.SnakyRows010.named_envelope_587_14_head
theorem Internal.SnakyRows010.named_envelope_587_13_last : (named_envelope_587_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_14 Internal.SnakyRows010.named_envelope_587_15 (251 : ℤ) Internal.SnakyRows010.named_envelope_587_15_last
def Internal.SnakyRows010.named_envelope_587_9 : List Cell := Internal.SnakyRows010.named_envelope_587_10 ++ Internal.SnakyRows010.named_envelope_587_13
theorem Internal.SnakyRows010.named_envelope_587_9_chain : (named_envelope_587_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_10 Internal.SnakyRows010.named_envelope_587_13 (-5 : ℤ) (-4 : ℤ)
    Internal.SnakyRows010.named_envelope_587_10_chain Internal.SnakyRows010.named_envelope_587_13_chain Internal.SnakyRows010.named_envelope_587_10_last Internal.SnakyRows010.named_envelope_587_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_9_head : (named_envelope_587_9.map Internal.SnakyRows010.namedCellKey).head? = some (-259 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_10 Internal.SnakyRows010.named_envelope_587_13 (-259 : ℤ) Internal.SnakyRows010.named_envelope_587_10_head
theorem Internal.SnakyRows010.named_envelope_587_9_last : (named_envelope_587_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_10 Internal.SnakyRows010.named_envelope_587_13 (251 : ℤ) Internal.SnakyRows010.named_envelope_587_13_last
def Internal.SnakyRows010.named_envelope_587_1 : List Cell := Internal.SnakyRows010.named_envelope_587_2 ++ Internal.SnakyRows010.named_envelope_587_9
theorem Internal.SnakyRows010.named_envelope_587_1_chain : (named_envelope_587_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_2 Internal.SnakyRows010.named_envelope_587_9 (-260 : ℤ) (-259 : ℤ)
    Internal.SnakyRows010.named_envelope_587_2_chain Internal.SnakyRows010.named_envelope_587_9_chain Internal.SnakyRows010.named_envelope_587_2_last Internal.SnakyRows010.named_envelope_587_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_1_head : (named_envelope_587_1.map Internal.SnakyRows010.namedCellKey).head? = some (-898 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_2 Internal.SnakyRows010.named_envelope_587_9 (-898 : ℤ) Internal.SnakyRows010.named_envelope_587_2_head
theorem Internal.SnakyRows010.named_envelope_587_1_last : (named_envelope_587_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_2 Internal.SnakyRows010.named_envelope_587_9 (251 : ℤ) Internal.SnakyRows010.named_envelope_587_9_last
def Internal.SnakyRows010.named_envelope_587_19 : List Cell := ([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_19_chain : (named_envelope_587_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_19_head : (named_envelope_587_19.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_19_last : (named_envelope_587_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (260 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_20 : List Cell := ([(2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_20_chain : (named_envelope_587_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_20_head : (named_envelope_587_20.map Internal.SnakyRows010.namedCellKey).head? = some (261 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_20_last : (named_envelope_587_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (384 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_18 : List Cell := Internal.SnakyRows010.named_envelope_587_19 ++ Internal.SnakyRows010.named_envelope_587_20
theorem Internal.SnakyRows010.named_envelope_587_18_chain : (named_envelope_587_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_19 Internal.SnakyRows010.named_envelope_587_20 (260 : ℤ) (261 : ℤ)
    Internal.SnakyRows010.named_envelope_587_19_chain Internal.SnakyRows010.named_envelope_587_20_chain Internal.SnakyRows010.named_envelope_587_19_last Internal.SnakyRows010.named_envelope_587_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_18_head : (named_envelope_587_18.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_19 Internal.SnakyRows010.named_envelope_587_20 (252 : ℤ) Internal.SnakyRows010.named_envelope_587_19_head
theorem Internal.SnakyRows010.named_envelope_587_18_last : (named_envelope_587_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (384 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_19 Internal.SnakyRows010.named_envelope_587_20 (384 : ℤ) Internal.SnakyRows010.named_envelope_587_20_last
def Internal.SnakyRows010.named_envelope_587_22 : List Cell := ([(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -7), (4, -6), (4, -5), (4, -4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_22_chain : (named_envelope_587_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_22_head : (named_envelope_587_22.map Internal.SnakyRows010.namedCellKey).head? = some (385 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_22_last : (named_envelope_587_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (508 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_23 : List Cell := ([(4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_23_chain : (named_envelope_587_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_23_head : (named_envelope_587_23.map Internal.SnakyRows010.namedCellKey).head? = some (509 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_23_last : (named_envelope_587_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (518 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_21 : List Cell := Internal.SnakyRows010.named_envelope_587_22 ++ Internal.SnakyRows010.named_envelope_587_23
theorem Internal.SnakyRows010.named_envelope_587_21_chain : (named_envelope_587_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_22 Internal.SnakyRows010.named_envelope_587_23 (508 : ℤ) (509 : ℤ)
    Internal.SnakyRows010.named_envelope_587_22_chain Internal.SnakyRows010.named_envelope_587_23_chain Internal.SnakyRows010.named_envelope_587_22_last Internal.SnakyRows010.named_envelope_587_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_21_head : (named_envelope_587_21.map Internal.SnakyRows010.namedCellKey).head? = some (385 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_22 Internal.SnakyRows010.named_envelope_587_23 (385 : ℤ) Internal.SnakyRows010.named_envelope_587_22_head
theorem Internal.SnakyRows010.named_envelope_587_21_last : (named_envelope_587_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (518 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_22 Internal.SnakyRows010.named_envelope_587_23 (518 : ℤ) Internal.SnakyRows010.named_envelope_587_23_last
def Internal.SnakyRows010.named_envelope_587_17 : List Cell := Internal.SnakyRows010.named_envelope_587_18 ++ Internal.SnakyRows010.named_envelope_587_21
theorem Internal.SnakyRows010.named_envelope_587_17_chain : (named_envelope_587_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_18 Internal.SnakyRows010.named_envelope_587_21 (384 : ℤ) (385 : ℤ)
    Internal.SnakyRows010.named_envelope_587_18_chain Internal.SnakyRows010.named_envelope_587_21_chain Internal.SnakyRows010.named_envelope_587_18_last Internal.SnakyRows010.named_envelope_587_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_17_head : (named_envelope_587_17.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_18 Internal.SnakyRows010.named_envelope_587_21 (252 : ℤ) Internal.SnakyRows010.named_envelope_587_18_head
theorem Internal.SnakyRows010.named_envelope_587_17_last : (named_envelope_587_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (518 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_18 Internal.SnakyRows010.named_envelope_587_21 (518 : ℤ) Internal.SnakyRows010.named_envelope_587_21_last
def Internal.SnakyRows010.named_envelope_587_26 : List Cell := ([(5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_26_chain : (named_envelope_587_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_26_head : (named_envelope_587_26.map Internal.SnakyRows010.namedCellKey).head? = some (635 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_26_last : (named_envelope_587_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (643 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_27 : List Cell := ([(5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_27_chain : (named_envelope_587_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_27_head : (named_envelope_587_27.map Internal.SnakyRows010.namedCellKey).head? = some (644 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_27_last : (named_envelope_587_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (771 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_25 : List Cell := Internal.SnakyRows010.named_envelope_587_26 ++ Internal.SnakyRows010.named_envelope_587_27
theorem Internal.SnakyRows010.named_envelope_587_25_chain : (named_envelope_587_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_26 Internal.SnakyRows010.named_envelope_587_27 (643 : ℤ) (644 : ℤ)
    Internal.SnakyRows010.named_envelope_587_26_chain Internal.SnakyRows010.named_envelope_587_27_chain Internal.SnakyRows010.named_envelope_587_26_last Internal.SnakyRows010.named_envelope_587_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_25_head : (named_envelope_587_25.map Internal.SnakyRows010.namedCellKey).head? = some (635 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_26 Internal.SnakyRows010.named_envelope_587_27 (635 : ℤ) Internal.SnakyRows010.named_envelope_587_26_head
theorem Internal.SnakyRows010.named_envelope_587_25_last : (named_envelope_587_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (771 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_26 Internal.SnakyRows010.named_envelope_587_27 (771 : ℤ) Internal.SnakyRows010.named_envelope_587_27_last
def Internal.SnakyRows010.named_envelope_587_29 : List Cell := ([(6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_29_chain : (named_envelope_587_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_29_head : (named_envelope_587_29.map Internal.SnakyRows010.namedCellKey).head? = some (772 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_29_last : (named_envelope_587_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (898 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_30 : List Cell := ([(7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (9, -2), (9, -1), (9, 0), (9, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_587_30_chain : (named_envelope_587_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_587_30_head : (named_envelope_587_30.map Internal.SnakyRows010.namedCellKey).head? = some (899 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_587_30_last : (named_envelope_587_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1153 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_587_28 : List Cell := Internal.SnakyRows010.named_envelope_587_29 ++ Internal.SnakyRows010.named_envelope_587_30
theorem Internal.SnakyRows010.named_envelope_587_28_chain : (named_envelope_587_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_29 Internal.SnakyRows010.named_envelope_587_30 (898 : ℤ) (899 : ℤ)
    Internal.SnakyRows010.named_envelope_587_29_chain Internal.SnakyRows010.named_envelope_587_30_chain Internal.SnakyRows010.named_envelope_587_29_last Internal.SnakyRows010.named_envelope_587_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_28_head : (named_envelope_587_28.map Internal.SnakyRows010.namedCellKey).head? = some (772 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_29 Internal.SnakyRows010.named_envelope_587_30 (772 : ℤ) Internal.SnakyRows010.named_envelope_587_29_head
theorem Internal.SnakyRows010.named_envelope_587_28_last : (named_envelope_587_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_29 Internal.SnakyRows010.named_envelope_587_30 (1153 : ℤ) Internal.SnakyRows010.named_envelope_587_30_last
def Internal.SnakyRows010.named_envelope_587_24 : List Cell := Internal.SnakyRows010.named_envelope_587_25 ++ Internal.SnakyRows010.named_envelope_587_28
theorem Internal.SnakyRows010.named_envelope_587_24_chain : (named_envelope_587_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_25 Internal.SnakyRows010.named_envelope_587_28 (771 : ℤ) (772 : ℤ)
    Internal.SnakyRows010.named_envelope_587_25_chain Internal.SnakyRows010.named_envelope_587_28_chain Internal.SnakyRows010.named_envelope_587_25_last Internal.SnakyRows010.named_envelope_587_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_24_head : (named_envelope_587_24.map Internal.SnakyRows010.namedCellKey).head? = some (635 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_25 Internal.SnakyRows010.named_envelope_587_28 (635 : ℤ) Internal.SnakyRows010.named_envelope_587_25_head
theorem Internal.SnakyRows010.named_envelope_587_24_last : (named_envelope_587_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_25 Internal.SnakyRows010.named_envelope_587_28 (1153 : ℤ) Internal.SnakyRows010.named_envelope_587_28_last
def Internal.SnakyRows010.named_envelope_587_16 : List Cell := Internal.SnakyRows010.named_envelope_587_17 ++ Internal.SnakyRows010.named_envelope_587_24
theorem Internal.SnakyRows010.named_envelope_587_16_chain : (named_envelope_587_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_17 Internal.SnakyRows010.named_envelope_587_24 (518 : ℤ) (635 : ℤ)
    Internal.SnakyRows010.named_envelope_587_17_chain Internal.SnakyRows010.named_envelope_587_24_chain Internal.SnakyRows010.named_envelope_587_17_last Internal.SnakyRows010.named_envelope_587_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_16_head : (named_envelope_587_16.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_17 Internal.SnakyRows010.named_envelope_587_24 (252 : ℤ) Internal.SnakyRows010.named_envelope_587_17_head
theorem Internal.SnakyRows010.named_envelope_587_16_last : (named_envelope_587_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_17 Internal.SnakyRows010.named_envelope_587_24 (1153 : ℤ) Internal.SnakyRows010.named_envelope_587_24_last
def Internal.SnakyRows010.named_envelope_587_0 : List Cell := Internal.SnakyRows010.named_envelope_587_1 ++ Internal.SnakyRows010.named_envelope_587_16
theorem Internal.SnakyRows010.named_envelope_587_0_chain : (named_envelope_587_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_587_1 Internal.SnakyRows010.named_envelope_587_16 (251 : ℤ) (252 : ℤ)
    Internal.SnakyRows010.named_envelope_587_1_chain Internal.SnakyRows010.named_envelope_587_16_chain Internal.SnakyRows010.named_envelope_587_1_last Internal.SnakyRows010.named_envelope_587_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_587_0_head : (named_envelope_587_0.map Internal.SnakyRows010.namedCellKey).head? = some (-898 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_587_1 Internal.SnakyRows010.named_envelope_587_16 (-898 : ℤ) Internal.SnakyRows010.named_envelope_587_1_head
theorem Internal.SnakyRows010.named_envelope_587_0_last : (named_envelope_587_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1153 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_587_1 Internal.SnakyRows010.named_envelope_587_16 (1153 : ℤ) Internal.SnakyRows010.named_envelope_587_16_last
theorem Internal.SnakyRows010.named_envelope_587_nodup : (Internal.SnakyRows010.named_envelope_587_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_587_0 Internal.SnakyRows010.named_envelope_587_0_chain
def envelope_587 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_587_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_587_nodup⟩
def childrenC_587 : Fin 6 → Finset Cell := ![(placedSet 2 (0, -3) required_300), (placedSet 1 (0, 1) required_479), (placedSet 3 (1, 1) required_319), (placedSet 6 (0, -3) required_477), (placedSet 3 (0, 1) required_252), (placedSet 2 (0, 1) required_467)]
def childrenD_587 : Fin 6 → Finset Cell := ![(placedSet 2 (0, -3) envelope_300), (placedSet 1 (0, 1) envelope_479), (placedSet 3 (1, 1) envelope_319), (placedSet 6 (0, -3) envelope_477), (placedSet 3 (0, 1) envelope_252), (placedSet 2 (0, 1) envelope_467)]
theorem common_sub_587 : commonEnvelope childrenD_587 ⊆ insert (0, 0) required_587 := by decide
theorem child_required_sub_587 : ∀ j, childrenC_587 j ⊆ insert (0, 0) required_587 := by decide
theorem Internal.SnakyRows010.containment_587_0 :
    placedSet 2 (0, -3) envelope_300 ⊆ envelope_587 := by decide
theorem Internal.SnakyRows010.containment_587_1 :
    placedSet 1 (0, 1) envelope_479 ⊆ envelope_587 := by decide +kernel
theorem Internal.SnakyRows010.containment_587_2 :
    placedSet 3 (1, 1) envelope_319 ⊆ envelope_587 := by decide
theorem Internal.SnakyRows010.containment_587_3 :
    placedSet 6 (0, -3) envelope_477 ⊆ envelope_587 := by decide
theorem Internal.SnakyRows010.containment_587_4 :
    placedSet 3 (0, 1) envelope_252 ⊆ envelope_587 := by decide
theorem Internal.SnakyRows010.containment_587_5 :
    placedSet 2 (0, 1) envelope_467 ⊆ envelope_587 := by decide +kernel
theorem child_envelope_sub_587 : ∀ j, childrenD_587 j ⊆ envelope_587 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_587_0
  · exact Internal.SnakyRows010.containment_587_1
  · exact Internal.SnakyRows010.containment_587_2
  · exact Internal.SnakyRows010.containment_587_3
  · exact Internal.SnakyRows010.containment_587_4
  · exact Internal.SnakyRows010.containment_587_5
theorem pivot_mem_587 : (0, 0) ∈ envelope_587 := by decide
theorem children_work_587 : ∀ j, Template HasSnaky 21 (childrenC_587 j) (childrenD_587 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_300 2 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_479 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_319 3 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_477 6 (0, -3)).mono (by decide)
  · exact (placed_template_map row_works_252 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_467 2 (0, 1)).mono (by decide)
theorem row_works_587 : Template HasSnaky 22 required_587 envelope_587 := by
  refine compose HasSnaky 21 childrenC_587 childrenD_587 children_work_587 (0, 0)
    required_587 envelope_587 pivot_mem_587 child_required_sub_587 child_envelope_sub_587 ?_
  intro b hb; exact common_sub_587 (mem_commonEnvelope childrenD_587 b hb)
end SnakyConditional

end OAI
