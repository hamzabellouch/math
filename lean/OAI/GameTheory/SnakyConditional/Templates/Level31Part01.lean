import OAI.GameTheory.SnakyConditional.Templates.Level30Part02
import OAI.GameTheory.SnakyConditional.Templates.Level30Part03

namespace OAI

namespace SnakyConditional
def required_596 : Finset Cell := ⟨(([(0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011A.named_envelope_596_4 : List Cell := ([(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_4_chain : (named_envelope_596_4.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_4_head : (named_envelope_596_4.map Internal.SnakyRows011A.namedCellKey).head? = some (-761 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_4_last : (named_envelope_596_4.map Internal.SnakyRows011A.namedCellKey).getLast? = some (-504 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_5 : List Cell := ([(-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_5_chain : (named_envelope_596_5.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_5_head : (named_envelope_596_5.map Internal.SnakyRows011A.namedCellKey).head? = some (-503 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_5_last : (named_envelope_596_5.map Internal.SnakyRows011A.namedCellKey).getLast? = some (-373 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_3 : List Cell := Internal.SnakyRows011A.named_envelope_596_4 ++ Internal.SnakyRows011A.named_envelope_596_5
theorem Internal.SnakyRows011A.named_envelope_596_3_chain : (named_envelope_596_3.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_4 Internal.SnakyRows011A.named_envelope_596_5 (-504 : ℤ) (-503 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_4_chain Internal.SnakyRows011A.named_envelope_596_5_chain Internal.SnakyRows011A.named_envelope_596_4_last Internal.SnakyRows011A.named_envelope_596_5_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_3_head : (named_envelope_596_3.map Internal.SnakyRows011A.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_4 Internal.SnakyRows011A.named_envelope_596_5 (-761 : ℤ) Internal.SnakyRows011A.named_envelope_596_4_head
theorem Internal.SnakyRows011A.named_envelope_596_3_last : (named_envelope_596_3.map Internal.SnakyRows011A.namedCellKey).getLast? = some (-373 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_4 Internal.SnakyRows011A.named_envelope_596_5 (-373 : ℤ) Internal.SnakyRows011A.named_envelope_596_5_last
def Internal.SnakyRows011A.named_envelope_596_7 : List Cell := ([(-3, 12), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_7_chain : (named_envelope_596_7.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_7_head : (named_envelope_596_7.map Internal.SnakyRows011A.namedCellKey).head? = some (-372 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_7_last : (named_envelope_596_7.map Internal.SnakyRows011A.namedCellKey).getLast? = some (-241 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_8 : List Cell := ([(-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_8_chain : (named_envelope_596_8.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_8_head : (named_envelope_596_8.map Internal.SnakyRows011A.namedCellKey).head? = some (-132 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_8_last : (named_envelope_596_8.map Internal.SnakyRows011A.namedCellKey).getLast? = some (-116 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_6 : List Cell := Internal.SnakyRows011A.named_envelope_596_7 ++ Internal.SnakyRows011A.named_envelope_596_8
theorem Internal.SnakyRows011A.named_envelope_596_6_chain : (named_envelope_596_6.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_7 Internal.SnakyRows011A.named_envelope_596_8 (-241 : ℤ) (-132 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_7_chain Internal.SnakyRows011A.named_envelope_596_8_chain Internal.SnakyRows011A.named_envelope_596_7_last Internal.SnakyRows011A.named_envelope_596_8_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_6_head : (named_envelope_596_6.map Internal.SnakyRows011A.namedCellKey).head? = some (-372 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_7 Internal.SnakyRows011A.named_envelope_596_8 (-372 : ℤ) Internal.SnakyRows011A.named_envelope_596_7_head
theorem Internal.SnakyRows011A.named_envelope_596_6_last : (named_envelope_596_6.map Internal.SnakyRows011A.namedCellKey).getLast? = some (-116 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_7 Internal.SnakyRows011A.named_envelope_596_8 (-116 : ℤ) Internal.SnakyRows011A.named_envelope_596_8_last
def Internal.SnakyRows011A.named_envelope_596_2 : List Cell := Internal.SnakyRows011A.named_envelope_596_3 ++ Internal.SnakyRows011A.named_envelope_596_6
theorem Internal.SnakyRows011A.named_envelope_596_2_chain : (named_envelope_596_2.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_3 Internal.SnakyRows011A.named_envelope_596_6 (-373 : ℤ) (-372 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_3_chain Internal.SnakyRows011A.named_envelope_596_6_chain Internal.SnakyRows011A.named_envelope_596_3_last Internal.SnakyRows011A.named_envelope_596_6_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_2_head : (named_envelope_596_2.map Internal.SnakyRows011A.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_3 Internal.SnakyRows011A.named_envelope_596_6 (-761 : ℤ) Internal.SnakyRows011A.named_envelope_596_3_head
theorem Internal.SnakyRows011A.named_envelope_596_2_last : (named_envelope_596_2.map Internal.SnakyRows011A.namedCellKey).getLast? = some (-116 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_3 Internal.SnakyRows011A.named_envelope_596_6 (-116 : ℤ) Internal.SnakyRows011A.named_envelope_596_6_last
def Internal.SnakyRows011A.named_envelope_596_11 : List Cell := ([(-1, 13), (-1, 14), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_11_chain : (named_envelope_596_11.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_11_head : (named_envelope_596_11.map Internal.SnakyRows011A.namedCellKey).head? = some (-115 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_11_last : (named_envelope_596_11.map Internal.SnakyRows011A.namedCellKey).getLast? = some (7 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_12 : List Cell := ([(0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_12_chain : (named_envelope_596_12.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_12_head : (named_envelope_596_12.map Internal.SnakyRows011A.namedCellKey).head? = some (8 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_12_last : (named_envelope_596_12.map Internal.SnakyRows011A.namedCellKey).getLast? = some (128 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_10 : List Cell := Internal.SnakyRows011A.named_envelope_596_11 ++ Internal.SnakyRows011A.named_envelope_596_12
theorem Internal.SnakyRows011A.named_envelope_596_10_chain : (named_envelope_596_10.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_11 Internal.SnakyRows011A.named_envelope_596_12 (7 : ℤ) (8 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_11_chain Internal.SnakyRows011A.named_envelope_596_12_chain Internal.SnakyRows011A.named_envelope_596_11_last Internal.SnakyRows011A.named_envelope_596_12_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_10_head : (named_envelope_596_10.map Internal.SnakyRows011A.namedCellKey).head? = some (-115 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_11 Internal.SnakyRows011A.named_envelope_596_12 (-115 : ℤ) Internal.SnakyRows011A.named_envelope_596_11_head
theorem Internal.SnakyRows011A.named_envelope_596_10_last : (named_envelope_596_10.map Internal.SnakyRows011A.namedCellKey).getLast? = some (128 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_11 Internal.SnakyRows011A.named_envelope_596_12 (128 : ℤ) Internal.SnakyRows011A.named_envelope_596_12_last
def Internal.SnakyRows011A.named_envelope_596_14 : List Cell := ([(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -5)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_14_chain : (named_envelope_596_14.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_14_head : (named_envelope_596_14.map Internal.SnakyRows011A.namedCellKey).head? = some (129 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_14_last : (named_envelope_596_14.map Internal.SnakyRows011A.namedCellKey).getLast? = some (251 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_15 : List Cell := ([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_15_chain : (named_envelope_596_15.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_15_head : (named_envelope_596_15.map Internal.SnakyRows011A.namedCellKey).head? = some (252 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_15_last : (named_envelope_596_15.map Internal.SnakyRows011A.namedCellKey).getLast? = some (266 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_13 : List Cell := Internal.SnakyRows011A.named_envelope_596_14 ++ Internal.SnakyRows011A.named_envelope_596_15
theorem Internal.SnakyRows011A.named_envelope_596_13_chain : (named_envelope_596_13.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_14 Internal.SnakyRows011A.named_envelope_596_15 (251 : ℤ) (252 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_14_chain Internal.SnakyRows011A.named_envelope_596_15_chain Internal.SnakyRows011A.named_envelope_596_14_last Internal.SnakyRows011A.named_envelope_596_15_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_13_head : (named_envelope_596_13.map Internal.SnakyRows011A.namedCellKey).head? = some (129 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_14 Internal.SnakyRows011A.named_envelope_596_15 (129 : ℤ) Internal.SnakyRows011A.named_envelope_596_14_head
theorem Internal.SnakyRows011A.named_envelope_596_13_last : (named_envelope_596_13.map Internal.SnakyRows011A.namedCellKey).getLast? = some (266 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_14 Internal.SnakyRows011A.named_envelope_596_15 (266 : ℤ) Internal.SnakyRows011A.named_envelope_596_15_last
def Internal.SnakyRows011A.named_envelope_596_9 : List Cell := Internal.SnakyRows011A.named_envelope_596_10 ++ Internal.SnakyRows011A.named_envelope_596_13
theorem Internal.SnakyRows011A.named_envelope_596_9_chain : (named_envelope_596_9.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_10 Internal.SnakyRows011A.named_envelope_596_13 (128 : ℤ) (129 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_10_chain Internal.SnakyRows011A.named_envelope_596_13_chain Internal.SnakyRows011A.named_envelope_596_10_last Internal.SnakyRows011A.named_envelope_596_13_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_9_head : (named_envelope_596_9.map Internal.SnakyRows011A.namedCellKey).head? = some (-115 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_10 Internal.SnakyRows011A.named_envelope_596_13 (-115 : ℤ) Internal.SnakyRows011A.named_envelope_596_10_head
theorem Internal.SnakyRows011A.named_envelope_596_9_last : (named_envelope_596_9.map Internal.SnakyRows011A.namedCellKey).getLast? = some (266 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_10 Internal.SnakyRows011A.named_envelope_596_13 (266 : ℤ) Internal.SnakyRows011A.named_envelope_596_13_last
def Internal.SnakyRows011A.named_envelope_596_1 : List Cell := Internal.SnakyRows011A.named_envelope_596_2 ++ Internal.SnakyRows011A.named_envelope_596_9
theorem Internal.SnakyRows011A.named_envelope_596_1_chain : (named_envelope_596_1.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_2 Internal.SnakyRows011A.named_envelope_596_9 (-116 : ℤ) (-115 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_2_chain Internal.SnakyRows011A.named_envelope_596_9_chain Internal.SnakyRows011A.named_envelope_596_2_last Internal.SnakyRows011A.named_envelope_596_9_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_1_head : (named_envelope_596_1.map Internal.SnakyRows011A.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_2 Internal.SnakyRows011A.named_envelope_596_9 (-761 : ℤ) Internal.SnakyRows011A.named_envelope_596_2_head
theorem Internal.SnakyRows011A.named_envelope_596_1_last : (named_envelope_596_1.map Internal.SnakyRows011A.namedCellKey).getLast? = some (266 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_2 Internal.SnakyRows011A.named_envelope_596_9 (266 : ℤ) Internal.SnakyRows011A.named_envelope_596_9_last
def Internal.SnakyRows011A.named_envelope_596_19 : List Cell := ([(2, 11), (2, 12), (2, 13), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_19_chain : (named_envelope_596_19.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_19_head : (named_envelope_596_19.map Internal.SnakyRows011A.namedCellKey).head? = some (267 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_19_last : (named_envelope_596_19.map Internal.SnakyRows011A.namedCellKey).getLast? = some (389 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_20 : List Cell := ([(3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_20_chain : (named_envelope_596_20.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_20_head : (named_envelope_596_20.map Internal.SnakyRows011A.namedCellKey).head? = some (390 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_20_last : (named_envelope_596_20.map Internal.SnakyRows011A.namedCellKey).getLast? = some (512 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_18 : List Cell := Internal.SnakyRows011A.named_envelope_596_19 ++ Internal.SnakyRows011A.named_envelope_596_20
theorem Internal.SnakyRows011A.named_envelope_596_18_chain : (named_envelope_596_18.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_19 Internal.SnakyRows011A.named_envelope_596_20 (389 : ℤ) (390 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_19_chain Internal.SnakyRows011A.named_envelope_596_20_chain Internal.SnakyRows011A.named_envelope_596_19_last Internal.SnakyRows011A.named_envelope_596_20_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_18_head : (named_envelope_596_18.map Internal.SnakyRows011A.namedCellKey).head? = some (267 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_19 Internal.SnakyRows011A.named_envelope_596_20 (267 : ℤ) Internal.SnakyRows011A.named_envelope_596_19_head
theorem Internal.SnakyRows011A.named_envelope_596_18_last : (named_envelope_596_18.map Internal.SnakyRows011A.namedCellKey).getLast? = some (512 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_19 Internal.SnakyRows011A.named_envelope_596_20 (512 : ℤ) Internal.SnakyRows011A.named_envelope_596_20_last
def Internal.SnakyRows011A.named_envelope_596_22 : List Cell := ([(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_22_chain : (named_envelope_596_22.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_22_head : (named_envelope_596_22.map Internal.SnakyRows011A.namedCellKey).head? = some (513 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_22_last : (named_envelope_596_22.map Internal.SnakyRows011A.namedCellKey).getLast? = some (637 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_23 : List Cell := ([(5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, -3)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_23_chain : (named_envelope_596_23.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_23_head : (named_envelope_596_23.map Internal.SnakyRows011A.namedCellKey).head? = some (638 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_23_last : (named_envelope_596_23.map Internal.SnakyRows011A.namedCellKey).getLast? = some (765 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_21 : List Cell := Internal.SnakyRows011A.named_envelope_596_22 ++ Internal.SnakyRows011A.named_envelope_596_23
theorem Internal.SnakyRows011A.named_envelope_596_21_chain : (named_envelope_596_21.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_22 Internal.SnakyRows011A.named_envelope_596_23 (637 : ℤ) (638 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_22_chain Internal.SnakyRows011A.named_envelope_596_23_chain Internal.SnakyRows011A.named_envelope_596_22_last Internal.SnakyRows011A.named_envelope_596_23_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_21_head : (named_envelope_596_21.map Internal.SnakyRows011A.namedCellKey).head? = some (513 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_22 Internal.SnakyRows011A.named_envelope_596_23 (513 : ℤ) Internal.SnakyRows011A.named_envelope_596_22_head
theorem Internal.SnakyRows011A.named_envelope_596_21_last : (named_envelope_596_21.map Internal.SnakyRows011A.namedCellKey).getLast? = some (765 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_22 Internal.SnakyRows011A.named_envelope_596_23 (765 : ℤ) Internal.SnakyRows011A.named_envelope_596_23_last
def Internal.SnakyRows011A.named_envelope_596_17 : List Cell := Internal.SnakyRows011A.named_envelope_596_18 ++ Internal.SnakyRows011A.named_envelope_596_21
theorem Internal.SnakyRows011A.named_envelope_596_17_chain : (named_envelope_596_17.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_18 Internal.SnakyRows011A.named_envelope_596_21 (512 : ℤ) (513 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_18_chain Internal.SnakyRows011A.named_envelope_596_21_chain Internal.SnakyRows011A.named_envelope_596_18_last Internal.SnakyRows011A.named_envelope_596_21_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_17_head : (named_envelope_596_17.map Internal.SnakyRows011A.namedCellKey).head? = some (267 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_18 Internal.SnakyRows011A.named_envelope_596_21 (267 : ℤ) Internal.SnakyRows011A.named_envelope_596_18_head
theorem Internal.SnakyRows011A.named_envelope_596_17_last : (named_envelope_596_17.map Internal.SnakyRows011A.namedCellKey).getLast? = some (765 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_18 Internal.SnakyRows011A.named_envelope_596_21 (765 : ℤ) Internal.SnakyRows011A.named_envelope_596_21_last
def Internal.SnakyRows011A.named_envelope_596_26 : List Cell := ([(6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_26_chain : (named_envelope_596_26.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_26_head : (named_envelope_596_26.map Internal.SnakyRows011A.namedCellKey).head? = some (766 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_26_last : (named_envelope_596_26.map Internal.SnakyRows011A.namedCellKey).getLast? = some (893 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_27 : List Cell := ([(7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_27_chain : (named_envelope_596_27.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_27_head : (named_envelope_596_27.map Internal.SnakyRows011A.namedCellKey).head? = some (894 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_27_last : (named_envelope_596_27.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1023 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_25 : List Cell := Internal.SnakyRows011A.named_envelope_596_26 ++ Internal.SnakyRows011A.named_envelope_596_27
theorem Internal.SnakyRows011A.named_envelope_596_25_chain : (named_envelope_596_25.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_26 Internal.SnakyRows011A.named_envelope_596_27 (893 : ℤ) (894 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_26_chain Internal.SnakyRows011A.named_envelope_596_27_chain Internal.SnakyRows011A.named_envelope_596_26_last Internal.SnakyRows011A.named_envelope_596_27_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_25_head : (named_envelope_596_25.map Internal.SnakyRows011A.namedCellKey).head? = some (766 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_26 Internal.SnakyRows011A.named_envelope_596_27 (766 : ℤ) Internal.SnakyRows011A.named_envelope_596_26_head
theorem Internal.SnakyRows011A.named_envelope_596_25_last : (named_envelope_596_25.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1023 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_26 Internal.SnakyRows011A.named_envelope_596_27 (1023 : ℤ) Internal.SnakyRows011A.named_envelope_596_27_last
def Internal.SnakyRows011A.named_envelope_596_29 : List Cell := ([(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 2), (9, 3), (9, 4), (9, 5)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_29_chain : (named_envelope_596_29.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_29_head : (named_envelope_596_29.map Internal.SnakyRows011A.namedCellKey).head? = some (1024 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_29_last : (named_envelope_596_29.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1157 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_30 : List Cell := ([(9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)] : List Cell)
theorem Internal.SnakyRows011A.named_envelope_596_30_chain : (named_envelope_596_30.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_30_head : (named_envelope_596_30.map Internal.SnakyRows011A.namedCellKey).head? = some (1158 : ℤ) := by decide
theorem Internal.SnakyRows011A.named_envelope_596_30_last : (named_envelope_596_30.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1540 : ℤ) := by decide
def Internal.SnakyRows011A.named_envelope_596_28 : List Cell := Internal.SnakyRows011A.named_envelope_596_29 ++ Internal.SnakyRows011A.named_envelope_596_30
theorem Internal.SnakyRows011A.named_envelope_596_28_chain : (named_envelope_596_28.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_29 Internal.SnakyRows011A.named_envelope_596_30 (1157 : ℤ) (1158 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_29_chain Internal.SnakyRows011A.named_envelope_596_30_chain Internal.SnakyRows011A.named_envelope_596_29_last Internal.SnakyRows011A.named_envelope_596_30_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_28_head : (named_envelope_596_28.map Internal.SnakyRows011A.namedCellKey).head? = some (1024 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_29 Internal.SnakyRows011A.named_envelope_596_30 (1024 : ℤ) Internal.SnakyRows011A.named_envelope_596_29_head
theorem Internal.SnakyRows011A.named_envelope_596_28_last : (named_envelope_596_28.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_29 Internal.SnakyRows011A.named_envelope_596_30 (1540 : ℤ) Internal.SnakyRows011A.named_envelope_596_30_last
def Internal.SnakyRows011A.named_envelope_596_24 : List Cell := Internal.SnakyRows011A.named_envelope_596_25 ++ Internal.SnakyRows011A.named_envelope_596_28
theorem Internal.SnakyRows011A.named_envelope_596_24_chain : (named_envelope_596_24.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_25 Internal.SnakyRows011A.named_envelope_596_28 (1023 : ℤ) (1024 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_25_chain Internal.SnakyRows011A.named_envelope_596_28_chain Internal.SnakyRows011A.named_envelope_596_25_last Internal.SnakyRows011A.named_envelope_596_28_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_24_head : (named_envelope_596_24.map Internal.SnakyRows011A.namedCellKey).head? = some (766 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_25 Internal.SnakyRows011A.named_envelope_596_28 (766 : ℤ) Internal.SnakyRows011A.named_envelope_596_25_head
theorem Internal.SnakyRows011A.named_envelope_596_24_last : (named_envelope_596_24.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_25 Internal.SnakyRows011A.named_envelope_596_28 (1540 : ℤ) Internal.SnakyRows011A.named_envelope_596_28_last
def Internal.SnakyRows011A.named_envelope_596_16 : List Cell := Internal.SnakyRows011A.named_envelope_596_17 ++ Internal.SnakyRows011A.named_envelope_596_24
theorem Internal.SnakyRows011A.named_envelope_596_16_chain : (named_envelope_596_16.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_17 Internal.SnakyRows011A.named_envelope_596_24 (765 : ℤ) (766 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_17_chain Internal.SnakyRows011A.named_envelope_596_24_chain Internal.SnakyRows011A.named_envelope_596_17_last Internal.SnakyRows011A.named_envelope_596_24_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_16_head : (named_envelope_596_16.map Internal.SnakyRows011A.namedCellKey).head? = some (267 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_17 Internal.SnakyRows011A.named_envelope_596_24 (267 : ℤ) Internal.SnakyRows011A.named_envelope_596_17_head
theorem Internal.SnakyRows011A.named_envelope_596_16_last : (named_envelope_596_16.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_17 Internal.SnakyRows011A.named_envelope_596_24 (1540 : ℤ) Internal.SnakyRows011A.named_envelope_596_24_last
def Internal.SnakyRows011A.named_envelope_596_0 : List Cell := Internal.SnakyRows011A.named_envelope_596_1 ++ Internal.SnakyRows011A.named_envelope_596_16
theorem Internal.SnakyRows011A.named_envelope_596_0_chain : (named_envelope_596_0.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011A.named_chain_append Internal.SnakyRows011A.named_envelope_596_1 Internal.SnakyRows011A.named_envelope_596_16 (266 : ℤ) (267 : ℤ)
    Internal.SnakyRows011A.named_envelope_596_1_chain Internal.SnakyRows011A.named_envelope_596_16_chain Internal.SnakyRows011A.named_envelope_596_1_last Internal.SnakyRows011A.named_envelope_596_16_head (by decide)
theorem Internal.SnakyRows011A.named_envelope_596_0_head : (named_envelope_596_0.map Internal.SnakyRows011A.namedCellKey).head? = some (-761 : ℤ) :=
  Internal.SnakyRows011A.named_head_append Internal.SnakyRows011A.named_envelope_596_1 Internal.SnakyRows011A.named_envelope_596_16 (-761 : ℤ) Internal.SnakyRows011A.named_envelope_596_1_head
theorem Internal.SnakyRows011A.named_envelope_596_0_last : (named_envelope_596_0.map Internal.SnakyRows011A.namedCellKey).getLast? = some (1540 : ℤ) :=
  Internal.SnakyRows011A.named_last_append Internal.SnakyRows011A.named_envelope_596_1 Internal.SnakyRows011A.named_envelope_596_16 (1540 : ℤ) Internal.SnakyRows011A.named_envelope_596_16_last
theorem Internal.SnakyRows011A.named_envelope_596_nodup : (Internal.SnakyRows011A.named_envelope_596_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011A.named_nodup_of_chain Internal.SnakyRows011A.named_envelope_596_0 Internal.SnakyRows011A.named_envelope_596_0_chain
def envelope_596 : Finset Cell := ⟨(Internal.SnakyRows011A.named_envelope_596_0 : Multiset Cell), Internal.SnakyRows011A.named_envelope_596_nodup⟩
def childrenC_596 : Fin 6 → Finset Cell := ![(placedSet 5 (0, -2) required_385), (placedSet 0 (1, 2) required_592), (placedSet 1 (0, 2) required_330), (placedSet 5 (0, 2) required_529), (placedSet 1 (0, 2) required_385), (placedSet 5 (0, -2) required_330)]
def childrenD_596 : Fin 6 → Finset Cell := ![(placedSet 5 (0, -2) envelope_385), (placedSet 0 (1, 2) envelope_592), (placedSet 1 (0, 2) envelope_330), (placedSet 5 (0, 2) envelope_529), (placedSet 1 (0, 2) envelope_385), (placedSet 5 (0, -2) envelope_330)]
theorem common_sub_596 : commonEnvelope childrenD_596 ⊆ insert (0, 0) required_596 := by decide
theorem child_required_sub_596 : ∀ j, childrenC_596 j ⊆ insert (0, 0) required_596 := by decide
theorem Internal.SnakyRows011A.containment_596_0 :
    placedSet 5 (0, -2) envelope_385 ⊆ envelope_596 := by decide
theorem Internal.SnakyRows011A.containment_596_1 :
    placedSet 0 (1, 2) envelope_592 ⊆ envelope_596 := by decide +kernel
theorem Internal.SnakyRows011A.containment_596_2 :
    placedSet 1 (0, 2) envelope_330 ⊆ envelope_596 := by decide
theorem Internal.SnakyRows011A.containment_596_3 :
    placedSet 5 (0, 2) envelope_529 ⊆ envelope_596 := by decide
theorem Internal.SnakyRows011A.containment_596_4 :
    placedSet 1 (0, 2) envelope_385 ⊆ envelope_596 := by decide
theorem Internal.SnakyRows011A.containment_596_5 :
    placedSet 5 (0, -2) envelope_330 ⊆ envelope_596 := by decide
theorem child_envelope_sub_596 : ∀ j, childrenD_596 j ⊆ envelope_596 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011A.containment_596_0
  · exact Internal.SnakyRows011A.containment_596_1
  · exact Internal.SnakyRows011A.containment_596_2
  · exact Internal.SnakyRows011A.containment_596_3
  · exact Internal.SnakyRows011A.containment_596_4
  · exact Internal.SnakyRows011A.containment_596_5
theorem pivot_mem_596 : (0, 0) ∈ envelope_596 := by decide
theorem children_work_596 : ∀ j, Template HasSnaky 28 (childrenC_596 j) (childrenD_596 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_385 5 (0, -2)).mono (by decide)
  · exact (placed_template_map row_works_592 0 (1, 2)).mono (by decide)
  · exact (placed_template_map row_works_330 1 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_529 5 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_385 1 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_330 5 (0, -2)).mono (by decide)
theorem row_works_596 : Template HasSnaky 29 required_596 envelope_596 := by
  refine compose HasSnaky 28 childrenC_596 childrenD_596 children_work_596 (0, 0)
    required_596 envelope_596 pivot_mem_596 child_required_sub_596 child_envelope_sub_596 ?_
  intro b hb; exact common_sub_596 (mem_commonEnvelope childrenD_596 b hb)
def required_597 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows011B.named_envelope_597_4 : List Cell := ([(-4, -1), (-4, 1), (-4, 2), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_4_chain : (named_envelope_597_4.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_4_head : (named_envelope_597_4.map Internal.SnakyRows011B.namedCellKey).head? = some (-513 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_4_last : (named_envelope_597_4.map Internal.SnakyRows011B.namedCellKey).getLast? = some (-256 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_5 : List Cell := ([(-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_5_chain : (named_envelope_597_5.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_5_head : (named_envelope_597_5.map Internal.SnakyRows011B.namedCellKey).head? = some (-255 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_5_last : (named_envelope_597_5.map Internal.SnakyRows011B.namedCellKey).getLast? = some (-123 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_3 : List Cell := Internal.SnakyRows011B.named_envelope_597_4 ++ Internal.SnakyRows011B.named_envelope_597_5
theorem Internal.SnakyRows011B.named_envelope_597_3_chain : (named_envelope_597_3.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_4 Internal.SnakyRows011B.named_envelope_597_5 (-256 : ℤ) (-255 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_4_chain Internal.SnakyRows011B.named_envelope_597_5_chain Internal.SnakyRows011B.named_envelope_597_4_last Internal.SnakyRows011B.named_envelope_597_5_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_3_head : (named_envelope_597_3.map Internal.SnakyRows011B.namedCellKey).head? = some (-513 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_4 Internal.SnakyRows011B.named_envelope_597_5 (-513 : ℤ) Internal.SnakyRows011B.named_envelope_597_4_head
theorem Internal.SnakyRows011B.named_envelope_597_3_last : (named_envelope_597_3.map Internal.SnakyRows011B.namedCellKey).getLast? = some (-123 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_4 Internal.SnakyRows011B.named_envelope_597_5 (-123 : ℤ) Internal.SnakyRows011B.named_envelope_597_5_last
def Internal.SnakyRows011B.named_envelope_597_7 : List Cell := ([(-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_7_chain : (named_envelope_597_7.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_7_head : (named_envelope_597_7.map Internal.SnakyRows011B.namedCellKey).head? = some (-122 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_7_last : (named_envelope_597_7.map Internal.SnakyRows011B.namedCellKey).getLast? = some (128 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_8 : List Cell := ([(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_8_chain : (named_envelope_597_8.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_8_head : (named_envelope_597_8.map Internal.SnakyRows011B.namedCellKey).head? = some (129 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_8_last : (named_envelope_597_8.map Internal.SnakyRows011B.namedCellKey).getLast? = some (259 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_6 : List Cell := Internal.SnakyRows011B.named_envelope_597_7 ++ Internal.SnakyRows011B.named_envelope_597_8
theorem Internal.SnakyRows011B.named_envelope_597_6_chain : (named_envelope_597_6.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_7 Internal.SnakyRows011B.named_envelope_597_8 (128 : ℤ) (129 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_7_chain Internal.SnakyRows011B.named_envelope_597_8_chain Internal.SnakyRows011B.named_envelope_597_7_last Internal.SnakyRows011B.named_envelope_597_8_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_6_head : (named_envelope_597_6.map Internal.SnakyRows011B.namedCellKey).head? = some (-122 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_7 Internal.SnakyRows011B.named_envelope_597_8 (-122 : ℤ) Internal.SnakyRows011B.named_envelope_597_7_head
theorem Internal.SnakyRows011B.named_envelope_597_6_last : (named_envelope_597_6.map Internal.SnakyRows011B.namedCellKey).getLast? = some (259 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_7 Internal.SnakyRows011B.named_envelope_597_8 (259 : ℤ) Internal.SnakyRows011B.named_envelope_597_8_last
def Internal.SnakyRows011B.named_envelope_597_2 : List Cell := Internal.SnakyRows011B.named_envelope_597_3 ++ Internal.SnakyRows011B.named_envelope_597_6
theorem Internal.SnakyRows011B.named_envelope_597_2_chain : (named_envelope_597_2.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_3 Internal.SnakyRows011B.named_envelope_597_6 (-123 : ℤ) (-122 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_3_chain Internal.SnakyRows011B.named_envelope_597_6_chain Internal.SnakyRows011B.named_envelope_597_3_last Internal.SnakyRows011B.named_envelope_597_6_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_2_head : (named_envelope_597_2.map Internal.SnakyRows011B.namedCellKey).head? = some (-513 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_3 Internal.SnakyRows011B.named_envelope_597_6 (-513 : ℤ) Internal.SnakyRows011B.named_envelope_597_3_head
theorem Internal.SnakyRows011B.named_envelope_597_2_last : (named_envelope_597_2.map Internal.SnakyRows011B.namedCellKey).getLast? = some (259 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_3 Internal.SnakyRows011B.named_envelope_597_6 (259 : ℤ) Internal.SnakyRows011B.named_envelope_597_6_last
def Internal.SnakyRows011B.named_envelope_597_11 : List Cell := ([(2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_11_chain : (named_envelope_597_11.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_11_head : (named_envelope_597_11.map Internal.SnakyRows011B.namedCellKey).head? = some (260 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_11_last : (named_envelope_597_11.map Internal.SnakyRows011B.namedCellKey).getLast? = some (384 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_12 : List Cell := ([(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -4), (4, -3), (4, -2)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_12_chain : (named_envelope_597_12.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_12_head : (named_envelope_597_12.map Internal.SnakyRows011B.namedCellKey).head? = some (385 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_12_last : (named_envelope_597_12.map Internal.SnakyRows011B.namedCellKey).getLast? = some (510 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_10 : List Cell := Internal.SnakyRows011B.named_envelope_597_11 ++ Internal.SnakyRows011B.named_envelope_597_12
theorem Internal.SnakyRows011B.named_envelope_597_10_chain : (named_envelope_597_10.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_11 Internal.SnakyRows011B.named_envelope_597_12 (384 : ℤ) (385 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_11_chain Internal.SnakyRows011B.named_envelope_597_12_chain Internal.SnakyRows011B.named_envelope_597_11_last Internal.SnakyRows011B.named_envelope_597_12_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_10_head : (named_envelope_597_10.map Internal.SnakyRows011B.namedCellKey).head? = some (260 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_11 Internal.SnakyRows011B.named_envelope_597_12 (260 : ℤ) Internal.SnakyRows011B.named_envelope_597_11_head
theorem Internal.SnakyRows011B.named_envelope_597_10_last : (named_envelope_597_10.map Internal.SnakyRows011B.namedCellKey).getLast? = some (510 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_11 Internal.SnakyRows011B.named_envelope_597_12 (510 : ℤ) Internal.SnakyRows011B.named_envelope_597_12_last
def Internal.SnakyRows011B.named_envelope_597_14 : List Cell := ([(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_14_chain : (named_envelope_597_14.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_14_head : (named_envelope_597_14.map Internal.SnakyRows011B.namedCellKey).head? = some (511 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_14_last : (named_envelope_597_14.map Internal.SnakyRows011B.namedCellKey).getLast? = some (524 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_15 : List Cell := ([(5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_15_chain : (named_envelope_597_15.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_15_head : (named_envelope_597_15.map Internal.SnakyRows011B.namedCellKey).head? = some (635 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_15_last : (named_envelope_597_15.map Internal.SnakyRows011B.namedCellKey).getLast? = some (648 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_13 : List Cell := Internal.SnakyRows011B.named_envelope_597_14 ++ Internal.SnakyRows011B.named_envelope_597_15
theorem Internal.SnakyRows011B.named_envelope_597_13_chain : (named_envelope_597_13.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_14 Internal.SnakyRows011B.named_envelope_597_15 (524 : ℤ) (635 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_14_chain Internal.SnakyRows011B.named_envelope_597_15_chain Internal.SnakyRows011B.named_envelope_597_14_last Internal.SnakyRows011B.named_envelope_597_15_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_13_head : (named_envelope_597_13.map Internal.SnakyRows011B.namedCellKey).head? = some (511 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_14 Internal.SnakyRows011B.named_envelope_597_15 (511 : ℤ) Internal.SnakyRows011B.named_envelope_597_14_head
theorem Internal.SnakyRows011B.named_envelope_597_13_last : (named_envelope_597_13.map Internal.SnakyRows011B.namedCellKey).getLast? = some (648 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_14 Internal.SnakyRows011B.named_envelope_597_15 (648 : ℤ) Internal.SnakyRows011B.named_envelope_597_15_last
def Internal.SnakyRows011B.named_envelope_597_9 : List Cell := Internal.SnakyRows011B.named_envelope_597_10 ++ Internal.SnakyRows011B.named_envelope_597_13
theorem Internal.SnakyRows011B.named_envelope_597_9_chain : (named_envelope_597_9.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_10 Internal.SnakyRows011B.named_envelope_597_13 (510 : ℤ) (511 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_10_chain Internal.SnakyRows011B.named_envelope_597_13_chain Internal.SnakyRows011B.named_envelope_597_10_last Internal.SnakyRows011B.named_envelope_597_13_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_9_head : (named_envelope_597_9.map Internal.SnakyRows011B.namedCellKey).head? = some (260 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_10 Internal.SnakyRows011B.named_envelope_597_13 (260 : ℤ) Internal.SnakyRows011B.named_envelope_597_10_head
theorem Internal.SnakyRows011B.named_envelope_597_9_last : (named_envelope_597_9.map Internal.SnakyRows011B.namedCellKey).getLast? = some (648 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_10 Internal.SnakyRows011B.named_envelope_597_13 (648 : ℤ) Internal.SnakyRows011B.named_envelope_597_13_last
def Internal.SnakyRows011B.named_envelope_597_1 : List Cell := Internal.SnakyRows011B.named_envelope_597_2 ++ Internal.SnakyRows011B.named_envelope_597_9
theorem Internal.SnakyRows011B.named_envelope_597_1_chain : (named_envelope_597_1.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_2 Internal.SnakyRows011B.named_envelope_597_9 (259 : ℤ) (260 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_2_chain Internal.SnakyRows011B.named_envelope_597_9_chain Internal.SnakyRows011B.named_envelope_597_2_last Internal.SnakyRows011B.named_envelope_597_9_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_1_head : (named_envelope_597_1.map Internal.SnakyRows011B.namedCellKey).head? = some (-513 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_2 Internal.SnakyRows011B.named_envelope_597_9 (-513 : ℤ) Internal.SnakyRows011B.named_envelope_597_2_head
theorem Internal.SnakyRows011B.named_envelope_597_1_last : (named_envelope_597_1.map Internal.SnakyRows011B.namedCellKey).getLast? = some (648 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_2 Internal.SnakyRows011B.named_envelope_597_9 (648 : ℤ) Internal.SnakyRows011B.named_envelope_597_9_last
def Internal.SnakyRows011B.named_envelope_597_19 : List Cell := ([(5, 9), (5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_19_chain : (named_envelope_597_19.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_19_head : (named_envelope_597_19.map Internal.SnakyRows011B.namedCellKey).head? = some (649 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_19_last : (named_envelope_597_19.map Internal.SnakyRows011B.namedCellKey).getLast? = some (774 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_20 : List Cell := ([(6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_20_chain : (named_envelope_597_20.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_20_head : (named_envelope_597_20.map Internal.SnakyRows011B.namedCellKey).head? = some (775 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_20_last : (named_envelope_597_20.map Internal.SnakyRows011B.namedCellKey).getLast? = some (899 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_18 : List Cell := Internal.SnakyRows011B.named_envelope_597_19 ++ Internal.SnakyRows011B.named_envelope_597_20
theorem Internal.SnakyRows011B.named_envelope_597_18_chain : (named_envelope_597_18.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_19 Internal.SnakyRows011B.named_envelope_597_20 (774 : ℤ) (775 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_19_chain Internal.SnakyRows011B.named_envelope_597_20_chain Internal.SnakyRows011B.named_envelope_597_19_last Internal.SnakyRows011B.named_envelope_597_20_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_18_head : (named_envelope_597_18.map Internal.SnakyRows011B.namedCellKey).head? = some (649 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_19 Internal.SnakyRows011B.named_envelope_597_20 (649 : ℤ) Internal.SnakyRows011B.named_envelope_597_19_head
theorem Internal.SnakyRows011B.named_envelope_597_18_last : (named_envelope_597_18.map Internal.SnakyRows011B.namedCellKey).getLast? = some (899 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_19 Internal.SnakyRows011B.named_envelope_597_20 (899 : ℤ) Internal.SnakyRows011B.named_envelope_597_20_last
def Internal.SnakyRows011B.named_envelope_597_22 : List Cell := ([(7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_22_chain : (named_envelope_597_22.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_22_head : (named_envelope_597_22.map Internal.SnakyRows011B.namedCellKey).head? = some (900 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_22_last : (named_envelope_597_22.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1024 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_23 : List Cell := ([(8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -5), (9, -4), (9, -3), (9, -2)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_23_chain : (named_envelope_597_23.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_23_head : (named_envelope_597_23.map Internal.SnakyRows011B.namedCellKey).head? = some (1025 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_23_last : (named_envelope_597_23.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1150 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_21 : List Cell := Internal.SnakyRows011B.named_envelope_597_22 ++ Internal.SnakyRows011B.named_envelope_597_23
theorem Internal.SnakyRows011B.named_envelope_597_21_chain : (named_envelope_597_21.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_22 Internal.SnakyRows011B.named_envelope_597_23 (1024 : ℤ) (1025 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_22_chain Internal.SnakyRows011B.named_envelope_597_23_chain Internal.SnakyRows011B.named_envelope_597_22_last Internal.SnakyRows011B.named_envelope_597_23_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_21_head : (named_envelope_597_21.map Internal.SnakyRows011B.namedCellKey).head? = some (900 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_22 Internal.SnakyRows011B.named_envelope_597_23 (900 : ℤ) Internal.SnakyRows011B.named_envelope_597_22_head
theorem Internal.SnakyRows011B.named_envelope_597_21_last : (named_envelope_597_21.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1150 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_22 Internal.SnakyRows011B.named_envelope_597_23 (1150 : ℤ) Internal.SnakyRows011B.named_envelope_597_23_last
def Internal.SnakyRows011B.named_envelope_597_17 : List Cell := Internal.SnakyRows011B.named_envelope_597_18 ++ Internal.SnakyRows011B.named_envelope_597_21
theorem Internal.SnakyRows011B.named_envelope_597_17_chain : (named_envelope_597_17.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_18 Internal.SnakyRows011B.named_envelope_597_21 (899 : ℤ) (900 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_18_chain Internal.SnakyRows011B.named_envelope_597_21_chain Internal.SnakyRows011B.named_envelope_597_18_last Internal.SnakyRows011B.named_envelope_597_21_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_17_head : (named_envelope_597_17.map Internal.SnakyRows011B.namedCellKey).head? = some (649 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_18 Internal.SnakyRows011B.named_envelope_597_21 (649 : ℤ) Internal.SnakyRows011B.named_envelope_597_18_head
theorem Internal.SnakyRows011B.named_envelope_597_17_last : (named_envelope_597_17.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1150 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_18 Internal.SnakyRows011B.named_envelope_597_21 (1150 : ℤ) Internal.SnakyRows011B.named_envelope_597_21_last
def Internal.SnakyRows011B.named_envelope_597_26 : List Cell := ([(9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, -6), (10, -5), (10, -4), (10, -3)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_26_chain : (named_envelope_597_26.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_26_head : (named_envelope_597_26.map Internal.SnakyRows011B.namedCellKey).head? = some (1151 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_26_last : (named_envelope_597_26.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1277 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_27 : List Cell := ([(10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_27_chain : (named_envelope_597_27.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_27_head : (named_envelope_597_27.map Internal.SnakyRows011B.namedCellKey).head? = some (1278 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_27_last : (named_envelope_597_27.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1407 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_25 : List Cell := Internal.SnakyRows011B.named_envelope_597_26 ++ Internal.SnakyRows011B.named_envelope_597_27
theorem Internal.SnakyRows011B.named_envelope_597_25_chain : (named_envelope_597_25.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_26 Internal.SnakyRows011B.named_envelope_597_27 (1277 : ℤ) (1278 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_26_chain Internal.SnakyRows011B.named_envelope_597_27_chain Internal.SnakyRows011B.named_envelope_597_26_last Internal.SnakyRows011B.named_envelope_597_27_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_25_head : (named_envelope_597_25.map Internal.SnakyRows011B.namedCellKey).head? = some (1151 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_26 Internal.SnakyRows011B.named_envelope_597_27 (1151 : ℤ) Internal.SnakyRows011B.named_envelope_597_26_head
theorem Internal.SnakyRows011B.named_envelope_597_25_last : (named_envelope_597_25.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1407 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_26 Internal.SnakyRows011B.named_envelope_597_27 (1407 : ℤ) Internal.SnakyRows011B.named_envelope_597_27_last
def Internal.SnakyRows011B.named_envelope_597_29 : List Cell := ([(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_29_chain : (named_envelope_597_29.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_29_head : (named_envelope_597_29.map Internal.SnakyRows011B.namedCellKey).head? = some (1408 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_29_last : (named_envelope_597_29.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1539 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_30 : List Cell := ([(12, 4), (13, -4), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -2), (14, -1), (14, 0), (15, -2), (15, 0)] : List Cell)
theorem Internal.SnakyRows011B.named_envelope_597_30_chain : (named_envelope_597_30.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_30_head : (named_envelope_597_30.map Internal.SnakyRows011B.namedCellKey).head? = some (1540 : ℤ) := by decide
theorem Internal.SnakyRows011B.named_envelope_597_30_last : (named_envelope_597_30.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1920 : ℤ) := by decide
def Internal.SnakyRows011B.named_envelope_597_28 : List Cell := Internal.SnakyRows011B.named_envelope_597_29 ++ Internal.SnakyRows011B.named_envelope_597_30
theorem Internal.SnakyRows011B.named_envelope_597_28_chain : (named_envelope_597_28.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_29 Internal.SnakyRows011B.named_envelope_597_30 (1539 : ℤ) (1540 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_29_chain Internal.SnakyRows011B.named_envelope_597_30_chain Internal.SnakyRows011B.named_envelope_597_29_last Internal.SnakyRows011B.named_envelope_597_30_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_28_head : (named_envelope_597_28.map Internal.SnakyRows011B.namedCellKey).head? = some (1408 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_29 Internal.SnakyRows011B.named_envelope_597_30 (1408 : ℤ) Internal.SnakyRows011B.named_envelope_597_29_head
theorem Internal.SnakyRows011B.named_envelope_597_28_last : (named_envelope_597_28.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1920 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_29 Internal.SnakyRows011B.named_envelope_597_30 (1920 : ℤ) Internal.SnakyRows011B.named_envelope_597_30_last
def Internal.SnakyRows011B.named_envelope_597_24 : List Cell := Internal.SnakyRows011B.named_envelope_597_25 ++ Internal.SnakyRows011B.named_envelope_597_28
theorem Internal.SnakyRows011B.named_envelope_597_24_chain : (named_envelope_597_24.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_25 Internal.SnakyRows011B.named_envelope_597_28 (1407 : ℤ) (1408 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_25_chain Internal.SnakyRows011B.named_envelope_597_28_chain Internal.SnakyRows011B.named_envelope_597_25_last Internal.SnakyRows011B.named_envelope_597_28_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_24_head : (named_envelope_597_24.map Internal.SnakyRows011B.namedCellKey).head? = some (1151 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_25 Internal.SnakyRows011B.named_envelope_597_28 (1151 : ℤ) Internal.SnakyRows011B.named_envelope_597_25_head
theorem Internal.SnakyRows011B.named_envelope_597_24_last : (named_envelope_597_24.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1920 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_25 Internal.SnakyRows011B.named_envelope_597_28 (1920 : ℤ) Internal.SnakyRows011B.named_envelope_597_28_last
def Internal.SnakyRows011B.named_envelope_597_16 : List Cell := Internal.SnakyRows011B.named_envelope_597_17 ++ Internal.SnakyRows011B.named_envelope_597_24
theorem Internal.SnakyRows011B.named_envelope_597_16_chain : (named_envelope_597_16.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_17 Internal.SnakyRows011B.named_envelope_597_24 (1150 : ℤ) (1151 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_17_chain Internal.SnakyRows011B.named_envelope_597_24_chain Internal.SnakyRows011B.named_envelope_597_17_last Internal.SnakyRows011B.named_envelope_597_24_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_16_head : (named_envelope_597_16.map Internal.SnakyRows011B.namedCellKey).head? = some (649 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_17 Internal.SnakyRows011B.named_envelope_597_24 (649 : ℤ) Internal.SnakyRows011B.named_envelope_597_17_head
theorem Internal.SnakyRows011B.named_envelope_597_16_last : (named_envelope_597_16.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1920 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_17 Internal.SnakyRows011B.named_envelope_597_24 (1920 : ℤ) Internal.SnakyRows011B.named_envelope_597_24_last
def Internal.SnakyRows011B.named_envelope_597_0 : List Cell := Internal.SnakyRows011B.named_envelope_597_1 ++ Internal.SnakyRows011B.named_envelope_597_16
theorem Internal.SnakyRows011B.named_envelope_597_0_chain : (named_envelope_597_0.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011B.named_chain_append Internal.SnakyRows011B.named_envelope_597_1 Internal.SnakyRows011B.named_envelope_597_16 (648 : ℤ) (649 : ℤ)
    Internal.SnakyRows011B.named_envelope_597_1_chain Internal.SnakyRows011B.named_envelope_597_16_chain Internal.SnakyRows011B.named_envelope_597_1_last Internal.SnakyRows011B.named_envelope_597_16_head (by decide)
theorem Internal.SnakyRows011B.named_envelope_597_0_head : (named_envelope_597_0.map Internal.SnakyRows011B.namedCellKey).head? = some (-513 : ℤ) :=
  Internal.SnakyRows011B.named_head_append Internal.SnakyRows011B.named_envelope_597_1 Internal.SnakyRows011B.named_envelope_597_16 (-513 : ℤ) Internal.SnakyRows011B.named_envelope_597_1_head
theorem Internal.SnakyRows011B.named_envelope_597_0_last : (named_envelope_597_0.map Internal.SnakyRows011B.namedCellKey).getLast? = some (1920 : ℤ) :=
  Internal.SnakyRows011B.named_last_append Internal.SnakyRows011B.named_envelope_597_1 Internal.SnakyRows011B.named_envelope_597_16 (1920 : ℤ) Internal.SnakyRows011B.named_envelope_597_16_last
theorem Internal.SnakyRows011B.named_envelope_597_nodup : (Internal.SnakyRows011B.named_envelope_597_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011B.named_nodup_of_chain Internal.SnakyRows011B.named_envelope_597_0 Internal.SnakyRows011B.named_envelope_597_0_chain
def envelope_597 : Finset Cell := ⟨(Internal.SnakyRows011B.named_envelope_597_0 : Multiset Cell), Internal.SnakyRows011B.named_envelope_597_nodup⟩
def childrenC_597 : Fin 4 → Finset Cell := ![(placedSet 6 (-2, -1) required_24), (placedSet 0 (2, 0) required_221), (placedSet 3 (-2, 0) required_199), (placedSet 1 (2, 1) required_594)]
def childrenD_597 : Fin 4 → Finset Cell := ![(placedSet 6 (-2, -1) envelope_24), (placedSet 0 (2, 0) envelope_221), (placedSet 3 (-2, 0) envelope_199), (placedSet 1 (2, 1) envelope_594)]
theorem common_sub_597 : commonEnvelope childrenD_597 ⊆ insert (0, 0) required_597 := by decide
theorem child_required_sub_597 : ∀ j, childrenC_597 j ⊆ insert (0, 0) required_597 := by decide
theorem Internal.SnakyRows011B.containment_597_0 :
    placedSet 6 (-2, -1) envelope_24 ⊆ envelope_597 := by decide
theorem Internal.SnakyRows011B.containment_597_1 :
    placedSet 0 (2, 0) envelope_221 ⊆ envelope_597 := by decide
theorem Internal.SnakyRows011B.containment_597_2 :
    placedSet 3 (-2, 0) envelope_199 ⊆ envelope_597 := by decide
theorem Internal.SnakyRows011B.containment_597_3 :
    placedSet 1 (2, 1) envelope_594 ⊆ envelope_597 := by decide +kernel
theorem child_envelope_sub_597 : ∀ j, childrenD_597 j ⊆ envelope_597 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows011B.containment_597_0
  · exact Internal.SnakyRows011B.containment_597_1
  · exact Internal.SnakyRows011B.containment_597_2
  · exact Internal.SnakyRows011B.containment_597_3
theorem pivot_mem_597 : (0, 0) ∈ envelope_597 := by decide
theorem children_work_597 : ∀ j, Template HasSnaky 28 (childrenC_597 j) (childrenD_597 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_24 6 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_221 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_199 3 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_594 1 (2, 1)).mono (by decide)
theorem row_works_597 : Template HasSnaky 29 required_597 envelope_597 := by
  refine compose HasSnaky 28 childrenC_597 childrenD_597 children_work_597 (0, 0)
    required_597 envelope_597 pivot_mem_597 child_required_sub_597 child_envelope_sub_597 ?_
  intro b hb; exact common_sub_597 (mem_commonEnvelope childrenD_597 b hb)
end SnakyConditional

end OAI
