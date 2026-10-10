import OAI.GameTheory.SnakyConditional.Regions.Region595
import OAI.GameTheory.SnakyConditional.Templates.Level19Part04
import OAI.GameTheory.SnakyConditional.Templates.Level23Part01
import OAI.GameTheory.SnakyConditional.Templates.Level23Part06
import OAI.GameTheory.SnakyConditional.Templates.Level23Part07
import OAI.GameTheory.SnakyConditional.Templates.Level26Part02
import OAI.GameTheory.SnakyConditional.Templates.Level27Part05

namespace OAI

namespace SnakyConditional
def required_586 : Finset Cell := ⟨(([(0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def Internal.SnakyRows010.named_envelope_586_4 : List Cell := ([(-7, 3), (-7, 4), (-7, 6), (-6, 1), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-5, -1), (-5, 0), (-5, 1), (-5, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_4_chain : (named_envelope_586_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_4_head : (named_envelope_586_4.map Internal.SnakyRows010.namedCellKey).head? = some (-893 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_4_last : (named_envelope_586_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-638 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_5 : List Cell := ([(-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_5_chain : (named_envelope_586_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_5_head : (named_envelope_586_5.map Internal.SnakyRows010.namedCellKey).head? = some (-637 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_5_last : (named_envelope_586_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-509 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_3 : List Cell := Internal.SnakyRows010.named_envelope_586_4 ++ Internal.SnakyRows010.named_envelope_586_5
theorem Internal.SnakyRows010.named_envelope_586_3_chain : (named_envelope_586_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_4 Internal.SnakyRows010.named_envelope_586_5 (-638 : ℤ) (-637 : ℤ)
    Internal.SnakyRows010.named_envelope_586_4_chain Internal.SnakyRows010.named_envelope_586_5_chain Internal.SnakyRows010.named_envelope_586_4_last Internal.SnakyRows010.named_envelope_586_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_3_head : (named_envelope_586_3.map Internal.SnakyRows010.namedCellKey).head? = some (-893 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_4 Internal.SnakyRows010.named_envelope_586_5 (-893 : ℤ) Internal.SnakyRows010.named_envelope_586_4_head
theorem Internal.SnakyRows010.named_envelope_586_3_last : (named_envelope_586_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-509 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_4 Internal.SnakyRows010.named_envelope_586_5 (-509 : ℤ) Internal.SnakyRows010.named_envelope_586_5_last
def Internal.SnakyRows010.named_envelope_586_7 : List Cell := ([(-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_7_chain : (named_envelope_586_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_7_head : (named_envelope_586_7.map Internal.SnakyRows010.namedCellKey).head? = some (-508 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_7_last : (named_envelope_586_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-379 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_8 : List Cell := ([(-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_8_chain : (named_envelope_586_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_8_head : (named_envelope_586_8.map Internal.SnakyRows010.namedCellKey).head? = some (-378 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_8_last : (named_envelope_586_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-252 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_6 : List Cell := Internal.SnakyRows010.named_envelope_586_7 ++ Internal.SnakyRows010.named_envelope_586_8
theorem Internal.SnakyRows010.named_envelope_586_6_chain : (named_envelope_586_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_7 Internal.SnakyRows010.named_envelope_586_8 (-379 : ℤ) (-378 : ℤ)
    Internal.SnakyRows010.named_envelope_586_7_chain Internal.SnakyRows010.named_envelope_586_8_chain Internal.SnakyRows010.named_envelope_586_7_last Internal.SnakyRows010.named_envelope_586_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_6_head : (named_envelope_586_6.map Internal.SnakyRows010.namedCellKey).head? = some (-508 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_7 Internal.SnakyRows010.named_envelope_586_8 (-508 : ℤ) Internal.SnakyRows010.named_envelope_586_7_head
theorem Internal.SnakyRows010.named_envelope_586_6_last : (named_envelope_586_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-252 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_7 Internal.SnakyRows010.named_envelope_586_8 (-252 : ℤ) Internal.SnakyRows010.named_envelope_586_8_last
def Internal.SnakyRows010.named_envelope_586_2 : List Cell := Internal.SnakyRows010.named_envelope_586_3 ++ Internal.SnakyRows010.named_envelope_586_6
theorem Internal.SnakyRows010.named_envelope_586_2_chain : (named_envelope_586_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_3 Internal.SnakyRows010.named_envelope_586_6 (-509 : ℤ) (-508 : ℤ)
    Internal.SnakyRows010.named_envelope_586_3_chain Internal.SnakyRows010.named_envelope_586_6_chain Internal.SnakyRows010.named_envelope_586_3_last Internal.SnakyRows010.named_envelope_586_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_2_head : (named_envelope_586_2.map Internal.SnakyRows010.namedCellKey).head? = some (-893 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_3 Internal.SnakyRows010.named_envelope_586_6 (-893 : ℤ) Internal.SnakyRows010.named_envelope_586_3_head
theorem Internal.SnakyRows010.named_envelope_586_2_last : (named_envelope_586_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-252 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_3 Internal.SnakyRows010.named_envelope_586_6 (-252 : ℤ) Internal.SnakyRows010.named_envelope_586_6_last
def Internal.SnakyRows010.named_envelope_586_11 : List Cell := ([(-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_11_chain : (named_envelope_586_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_11_head : (named_envelope_586_11.map Internal.SnakyRows010.namedCellKey).head? = some (-251 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_11_last : (named_envelope_586_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (-124 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_12 : List Cell := ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_12_chain : (named_envelope_586_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_12_head : (named_envelope_586_12.map Internal.SnakyRows010.namedCellKey).head? = some (-123 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_12_last : (named_envelope_586_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (3 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_10 : List Cell := Internal.SnakyRows010.named_envelope_586_11 ++ Internal.SnakyRows010.named_envelope_586_12
theorem Internal.SnakyRows010.named_envelope_586_10_chain : (named_envelope_586_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_11 Internal.SnakyRows010.named_envelope_586_12 (-124 : ℤ) (-123 : ℤ)
    Internal.SnakyRows010.named_envelope_586_11_chain Internal.SnakyRows010.named_envelope_586_12_chain Internal.SnakyRows010.named_envelope_586_11_last Internal.SnakyRows010.named_envelope_586_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_10_head : (named_envelope_586_10.map Internal.SnakyRows010.namedCellKey).head? = some (-251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_11 Internal.SnakyRows010.named_envelope_586_12 (-251 : ℤ) Internal.SnakyRows010.named_envelope_586_11_head
theorem Internal.SnakyRows010.named_envelope_586_10_last : (named_envelope_586_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (3 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_11 Internal.SnakyRows010.named_envelope_586_12 (3 : ℤ) Internal.SnakyRows010.named_envelope_586_12_last
def Internal.SnakyRows010.named_envelope_586_14 : List Cell := ([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_14_chain : (named_envelope_586_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_14_head : (named_envelope_586_14.map Internal.SnakyRows010.namedCellKey).head? = some (4 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_14_last : (named_envelope_586_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (127 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_15 : List Cell := ([(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -7), (2, -6), (2, -5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_15_chain : (named_envelope_586_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_15_head : (named_envelope_586_15.map Internal.SnakyRows010.namedCellKey).head? = some (128 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_15_last : (named_envelope_586_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_13 : List Cell := Internal.SnakyRows010.named_envelope_586_14 ++ Internal.SnakyRows010.named_envelope_586_15
theorem Internal.SnakyRows010.named_envelope_586_13_chain : (named_envelope_586_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_14 Internal.SnakyRows010.named_envelope_586_15 (127 : ℤ) (128 : ℤ)
    Internal.SnakyRows010.named_envelope_586_14_chain Internal.SnakyRows010.named_envelope_586_15_chain Internal.SnakyRows010.named_envelope_586_14_last Internal.SnakyRows010.named_envelope_586_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_13_head : (named_envelope_586_13.map Internal.SnakyRows010.namedCellKey).head? = some (4 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_14 Internal.SnakyRows010.named_envelope_586_15 (4 : ℤ) Internal.SnakyRows010.named_envelope_586_14_head
theorem Internal.SnakyRows010.named_envelope_586_13_last : (named_envelope_586_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_14 Internal.SnakyRows010.named_envelope_586_15 (251 : ℤ) Internal.SnakyRows010.named_envelope_586_15_last
def Internal.SnakyRows010.named_envelope_586_9 : List Cell := Internal.SnakyRows010.named_envelope_586_10 ++ Internal.SnakyRows010.named_envelope_586_13
theorem Internal.SnakyRows010.named_envelope_586_9_chain : (named_envelope_586_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_10 Internal.SnakyRows010.named_envelope_586_13 (3 : ℤ) (4 : ℤ)
    Internal.SnakyRows010.named_envelope_586_10_chain Internal.SnakyRows010.named_envelope_586_13_chain Internal.SnakyRows010.named_envelope_586_10_last Internal.SnakyRows010.named_envelope_586_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_9_head : (named_envelope_586_9.map Internal.SnakyRows010.namedCellKey).head? = some (-251 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_10 Internal.SnakyRows010.named_envelope_586_13 (-251 : ℤ) Internal.SnakyRows010.named_envelope_586_10_head
theorem Internal.SnakyRows010.named_envelope_586_9_last : (named_envelope_586_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_10 Internal.SnakyRows010.named_envelope_586_13 (251 : ℤ) Internal.SnakyRows010.named_envelope_586_13_last
def Internal.SnakyRows010.named_envelope_586_1 : List Cell := Internal.SnakyRows010.named_envelope_586_2 ++ Internal.SnakyRows010.named_envelope_586_9
theorem Internal.SnakyRows010.named_envelope_586_1_chain : (named_envelope_586_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_2 Internal.SnakyRows010.named_envelope_586_9 (-252 : ℤ) (-251 : ℤ)
    Internal.SnakyRows010.named_envelope_586_2_chain Internal.SnakyRows010.named_envelope_586_9_chain Internal.SnakyRows010.named_envelope_586_2_last Internal.SnakyRows010.named_envelope_586_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_1_head : (named_envelope_586_1.map Internal.SnakyRows010.namedCellKey).head? = some (-893 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_2 Internal.SnakyRows010.named_envelope_586_9 (-893 : ℤ) Internal.SnakyRows010.named_envelope_586_2_head
theorem Internal.SnakyRows010.named_envelope_586_1_last : (named_envelope_586_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (251 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_2 Internal.SnakyRows010.named_envelope_586_9 (251 : ℤ) Internal.SnakyRows010.named_envelope_586_9_last
def Internal.SnakyRows010.named_envelope_586_19 : List Cell := ([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_19_chain : (named_envelope_586_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_19_head : (named_envelope_586_19.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_19_last : (named_envelope_586_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (263 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_20 : List Cell := ([(2, 8), (2, 9), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_20_chain : (named_envelope_586_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_20_head : (named_envelope_586_20.map Internal.SnakyRows010.namedCellKey).head? = some (264 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_20_last : (named_envelope_586_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_18 : List Cell := Internal.SnakyRows010.named_envelope_586_19 ++ Internal.SnakyRows010.named_envelope_586_20
theorem Internal.SnakyRows010.named_envelope_586_18_chain : (named_envelope_586_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_19 Internal.SnakyRows010.named_envelope_586_20 (263 : ℤ) (264 : ℤ)
    Internal.SnakyRows010.named_envelope_586_19_chain Internal.SnakyRows010.named_envelope_586_20_chain Internal.SnakyRows010.named_envelope_586_19_last Internal.SnakyRows010.named_envelope_586_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_18_head : (named_envelope_586_18.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_19 Internal.SnakyRows010.named_envelope_586_20 (252 : ℤ) Internal.SnakyRows010.named_envelope_586_19_head
theorem Internal.SnakyRows010.named_envelope_586_18_last : (named_envelope_586_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (387 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_19 Internal.SnakyRows010.named_envelope_586_20 (387 : ℤ) Internal.SnakyRows010.named_envelope_586_20_last
def Internal.SnakyRows010.named_envelope_586_22 : List Cell := ([(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_22_chain : (named_envelope_586_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_22_head : (named_envelope_586_22.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_22_last : (named_envelope_586_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (510 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_23 : List Cell := ([(4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -5), (5, -4), (5, -3), (5, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_23_chain : (named_envelope_586_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_23_head : (named_envelope_586_23.map Internal.SnakyRows010.namedCellKey).head? = some (511 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_23_last : (named_envelope_586_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (638 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_21 : List Cell := Internal.SnakyRows010.named_envelope_586_22 ++ Internal.SnakyRows010.named_envelope_586_23
theorem Internal.SnakyRows010.named_envelope_586_21_chain : (named_envelope_586_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_22 Internal.SnakyRows010.named_envelope_586_23 (510 : ℤ) (511 : ℤ)
    Internal.SnakyRows010.named_envelope_586_22_chain Internal.SnakyRows010.named_envelope_586_23_chain Internal.SnakyRows010.named_envelope_586_22_last Internal.SnakyRows010.named_envelope_586_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_21_head : (named_envelope_586_21.map Internal.SnakyRows010.namedCellKey).head? = some (388 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_22 Internal.SnakyRows010.named_envelope_586_23 (388 : ℤ) Internal.SnakyRows010.named_envelope_586_22_head
theorem Internal.SnakyRows010.named_envelope_586_21_last : (named_envelope_586_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (638 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_22 Internal.SnakyRows010.named_envelope_586_23 (638 : ℤ) Internal.SnakyRows010.named_envelope_586_23_last
def Internal.SnakyRows010.named_envelope_586_17 : List Cell := Internal.SnakyRows010.named_envelope_586_18 ++ Internal.SnakyRows010.named_envelope_586_21
theorem Internal.SnakyRows010.named_envelope_586_17_chain : (named_envelope_586_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_18 Internal.SnakyRows010.named_envelope_586_21 (387 : ℤ) (388 : ℤ)
    Internal.SnakyRows010.named_envelope_586_18_chain Internal.SnakyRows010.named_envelope_586_21_chain Internal.SnakyRows010.named_envelope_586_18_last Internal.SnakyRows010.named_envelope_586_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_17_head : (named_envelope_586_17.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_18 Internal.SnakyRows010.named_envelope_586_21 (252 : ℤ) Internal.SnakyRows010.named_envelope_586_18_head
theorem Internal.SnakyRows010.named_envelope_586_17_last : (named_envelope_586_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (638 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_18 Internal.SnakyRows010.named_envelope_586_21 (638 : ℤ) Internal.SnakyRows010.named_envelope_586_21_last
def Internal.SnakyRows010.named_envelope_586_26 : List Cell := ([(5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -5), (6, -4), (6, -3), (6, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_26_chain : (named_envelope_586_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_26_head : (named_envelope_586_26.map Internal.SnakyRows010.namedCellKey).head? = some (639 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_26_last : (named_envelope_586_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (766 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_27 : List Cell := ([(6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_27_chain : (named_envelope_586_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_27_head : (named_envelope_586_27.map Internal.SnakyRows010.namedCellKey).head? = some (767 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_27_last : (named_envelope_586_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (895 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_25 : List Cell := Internal.SnakyRows010.named_envelope_586_26 ++ Internal.SnakyRows010.named_envelope_586_27
theorem Internal.SnakyRows010.named_envelope_586_25_chain : (named_envelope_586_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_26 Internal.SnakyRows010.named_envelope_586_27 (766 : ℤ) (767 : ℤ)
    Internal.SnakyRows010.named_envelope_586_26_chain Internal.SnakyRows010.named_envelope_586_27_chain Internal.SnakyRows010.named_envelope_586_26_last Internal.SnakyRows010.named_envelope_586_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_25_head : (named_envelope_586_25.map Internal.SnakyRows010.namedCellKey).head? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_26 Internal.SnakyRows010.named_envelope_586_27 (639 : ℤ) Internal.SnakyRows010.named_envelope_586_26_head
theorem Internal.SnakyRows010.named_envelope_586_25_last : (named_envelope_586_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (895 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_26 Internal.SnakyRows010.named_envelope_586_27 (895 : ℤ) Internal.SnakyRows010.named_envelope_586_27_last
def Internal.SnakyRows010.named_envelope_586_29 : List Cell := ([(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_29_chain : (named_envelope_586_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_29_head : (named_envelope_586_29.map Internal.SnakyRows010.namedCellKey).head? = some (896 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_29_last : (named_envelope_586_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (1027 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_30 : List Cell := ([(8, 4), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (10, -2), (10, -1), (10, 0), (11, -2), (11, 0)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_586_30_chain : (named_envelope_586_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_586_30_head : (named_envelope_586_30.map Internal.SnakyRows010.namedCellKey).head? = some (1028 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_586_30_last : (named_envelope_586_30.map Internal.SnakyRows010.namedCellKey).getLast? = some (1408 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_586_28 : List Cell := Internal.SnakyRows010.named_envelope_586_29 ++ Internal.SnakyRows010.named_envelope_586_30
theorem Internal.SnakyRows010.named_envelope_586_28_chain : (named_envelope_586_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_29 Internal.SnakyRows010.named_envelope_586_30 (1027 : ℤ) (1028 : ℤ)
    Internal.SnakyRows010.named_envelope_586_29_chain Internal.SnakyRows010.named_envelope_586_30_chain Internal.SnakyRows010.named_envelope_586_29_last Internal.SnakyRows010.named_envelope_586_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_28_head : (named_envelope_586_28.map Internal.SnakyRows010.namedCellKey).head? = some (896 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_29 Internal.SnakyRows010.named_envelope_586_30 (896 : ℤ) Internal.SnakyRows010.named_envelope_586_29_head
theorem Internal.SnakyRows010.named_envelope_586_28_last : (named_envelope_586_28.map Internal.SnakyRows010.namedCellKey).getLast? = some (1408 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_29 Internal.SnakyRows010.named_envelope_586_30 (1408 : ℤ) Internal.SnakyRows010.named_envelope_586_30_last
def Internal.SnakyRows010.named_envelope_586_24 : List Cell := Internal.SnakyRows010.named_envelope_586_25 ++ Internal.SnakyRows010.named_envelope_586_28
theorem Internal.SnakyRows010.named_envelope_586_24_chain : (named_envelope_586_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_25 Internal.SnakyRows010.named_envelope_586_28 (895 : ℤ) (896 : ℤ)
    Internal.SnakyRows010.named_envelope_586_25_chain Internal.SnakyRows010.named_envelope_586_28_chain Internal.SnakyRows010.named_envelope_586_25_last Internal.SnakyRows010.named_envelope_586_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_24_head : (named_envelope_586_24.map Internal.SnakyRows010.namedCellKey).head? = some (639 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_25 Internal.SnakyRows010.named_envelope_586_28 (639 : ℤ) Internal.SnakyRows010.named_envelope_586_25_head
theorem Internal.SnakyRows010.named_envelope_586_24_last : (named_envelope_586_24.map Internal.SnakyRows010.namedCellKey).getLast? = some (1408 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_25 Internal.SnakyRows010.named_envelope_586_28 (1408 : ℤ) Internal.SnakyRows010.named_envelope_586_28_last
def Internal.SnakyRows010.named_envelope_586_16 : List Cell := Internal.SnakyRows010.named_envelope_586_17 ++ Internal.SnakyRows010.named_envelope_586_24
theorem Internal.SnakyRows010.named_envelope_586_16_chain : (named_envelope_586_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_17 Internal.SnakyRows010.named_envelope_586_24 (638 : ℤ) (639 : ℤ)
    Internal.SnakyRows010.named_envelope_586_17_chain Internal.SnakyRows010.named_envelope_586_24_chain Internal.SnakyRows010.named_envelope_586_17_last Internal.SnakyRows010.named_envelope_586_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_16_head : (named_envelope_586_16.map Internal.SnakyRows010.namedCellKey).head? = some (252 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_17 Internal.SnakyRows010.named_envelope_586_24 (252 : ℤ) Internal.SnakyRows010.named_envelope_586_17_head
theorem Internal.SnakyRows010.named_envelope_586_16_last : (named_envelope_586_16.map Internal.SnakyRows010.namedCellKey).getLast? = some (1408 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_17 Internal.SnakyRows010.named_envelope_586_24 (1408 : ℤ) Internal.SnakyRows010.named_envelope_586_24_last
def Internal.SnakyRows010.named_envelope_586_0 : List Cell := Internal.SnakyRows010.named_envelope_586_1 ++ Internal.SnakyRows010.named_envelope_586_16
theorem Internal.SnakyRows010.named_envelope_586_0_chain : (named_envelope_586_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_586_1 Internal.SnakyRows010.named_envelope_586_16 (251 : ℤ) (252 : ℤ)
    Internal.SnakyRows010.named_envelope_586_1_chain Internal.SnakyRows010.named_envelope_586_16_chain Internal.SnakyRows010.named_envelope_586_1_last Internal.SnakyRows010.named_envelope_586_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_586_0_head : (named_envelope_586_0.map Internal.SnakyRows010.namedCellKey).head? = some (-893 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_586_1 Internal.SnakyRows010.named_envelope_586_16 (-893 : ℤ) Internal.SnakyRows010.named_envelope_586_1_head
theorem Internal.SnakyRows010.named_envelope_586_0_last : (named_envelope_586_0.map Internal.SnakyRows010.namedCellKey).getLast? = some (1408 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_586_1 Internal.SnakyRows010.named_envelope_586_16 (1408 : ℤ) Internal.SnakyRows010.named_envelope_586_16_last
theorem Internal.SnakyRows010.named_envelope_586_nodup : (Internal.SnakyRows010.named_envelope_586_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_586_0 Internal.SnakyRows010.named_envelope_586_0_chain
def envelope_586 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_586_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_586_nodup⟩
def childrenC_586 : Fin 13 → Finset Cell := ![(placedSet 4 (0, 1) required_465), (placedSet 1 (0, 1) required_558), (placedSet 1 (0, 1) required_385), (placedSet 4 (0, 1) required_379), (placedSet 0 (0, 1) required_524), (placedSet 2 (0, 1) required_469), (placedSet 2 (0, 1) required_467), (placedSet 4 (1, 1) required_527), (placedSet 0 (0, 1) required_553), (placedSet 1 (0, 1) required_552), (placedSet 1 (0, 1) required_555), (placedSet 0 (2, 0) required_564), (placedSet 0 (1, -2) required_583)]
def childrenD_586 : Fin 13 → Finset Cell := ![(placedSet 4 (0, 1) envelope_465), (placedSet 1 (0, 1) envelope_558), (placedSet 1 (0, 1) envelope_385), (placedSet 4 (0, 1) envelope_379), (placedSet 0 (0, 1) envelope_524), (placedSet 2 (0, 1) envelope_469), (placedSet 2 (0, 1) envelope_467), (placedSet 4 (1, 1) envelope_527), (placedSet 0 (0, 1) envelope_553), (placedSet 1 (0, 1) envelope_552), (placedSet 1 (0, 1) envelope_555), (placedSet 0 (2, 0) envelope_564), (placedSet 0 (1, -2) envelope_583)]
theorem common_sub_586 : commonEnvelope childrenD_586 ⊆ insert (0, 0) required_586 := by decide
theorem child_required_sub_586 : ∀ j, childrenC_586 j ⊆ insert (0, 0) required_586 := by decide
theorem Internal.SnakyRows010.containment_586_0 :
    placedSet 4 (0, 1) envelope_465 ⊆ envelope_586 := by decide
theorem Internal.SnakyRows010.containment_586_1 :
    placedSet 1 (0, 1) envelope_558 ⊆ envelope_586 := by decide +kernel
theorem Internal.SnakyRows010.containment_586_2 :
    placedSet 1 (0, 1) envelope_385 ⊆ envelope_586 := by decide
theorem Internal.SnakyRows010.containment_586_3 :
    placedSet 4 (0, 1) envelope_379 ⊆ envelope_586 := by decide
theorem Internal.SnakyRows010.containment_586_4 :
    placedSet 0 (0, 1) envelope_524 ⊆ envelope_586 := by decide
theorem Internal.SnakyRows010.containment_586_5 :
    placedSet 2 (0, 1) envelope_469 ⊆ envelope_586 := by decide +kernel
theorem Internal.SnakyRows010.containment_586_6 :
    placedSet 2 (0, 1) envelope_467 ⊆ envelope_586 := by decide +kernel
theorem Internal.SnakyRows010.containment_586_7 :
    placedSet 4 (1, 1) envelope_527 ⊆ envelope_586 := by decide
theorem Internal.SnakyRows010.containment_586_8 :
    placedSet 0 (0, 1) envelope_553 ⊆ envelope_586 := by decide +kernel
theorem Internal.SnakyRows010.containment_586_9 :
    placedSet 1 (0, 1) envelope_552 ⊆ envelope_586 := by decide +kernel
theorem Internal.SnakyRows010.containment_586_10 :
    placedSet 1 (0, 1) envelope_555 ⊆ envelope_586 := by decide +kernel
theorem Internal.SnakyRows010.containment_586_11 :
    placedSet 0 (2, 0) envelope_564 ⊆ envelope_586 := by decide +kernel
theorem Internal.SnakyRows010.containment_586_12 :
    placedSet 0 (1, -2) envelope_583 ⊆ envelope_586 := by decide +kernel
theorem child_envelope_sub_586 : ∀ j, childrenD_586 j ⊆ envelope_586 := by
  intro j
  fin_cases j
  · exact Internal.SnakyRows010.containment_586_0
  · exact Internal.SnakyRows010.containment_586_1
  · exact Internal.SnakyRows010.containment_586_2
  · exact Internal.SnakyRows010.containment_586_3
  · exact Internal.SnakyRows010.containment_586_4
  · exact Internal.SnakyRows010.containment_586_5
  · exact Internal.SnakyRows010.containment_586_6
  · exact Internal.SnakyRows010.containment_586_7
  · exact Internal.SnakyRows010.containment_586_8
  · exact Internal.SnakyRows010.containment_586_9
  · exact Internal.SnakyRows010.containment_586_10
  · exact Internal.SnakyRows010.containment_586_11
  · exact Internal.SnakyRows010.containment_586_12
theorem pivot_mem_586 : (0, 0) ∈ envelope_586 := by decide
theorem children_work_586 : ∀ j, Template HasSnaky 25 (childrenC_586 j) (childrenD_586 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_465 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_558 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_385 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_379 4 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_524 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_469 2 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_467 2 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_527 4 (1, 1)).mono (by decide)
  · exact (placed_template_map row_works_553 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_552 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_555 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_564 0 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_583 0 (1, -2)).mono (by decide)
theorem row_works_586 : Template HasSnaky 26 required_586 envelope_586 := by
  refine compose HasSnaky 25 childrenC_586 childrenD_586 children_work_586 (0, 0)
    required_586 envelope_586 pivot_mem_586 child_required_sub_586 child_envelope_sub_586 ?_
  intro b hb; exact common_sub_586 (mem_commonEnvelope childrenD_586 b hb)
end SnakyConditional

end OAI
