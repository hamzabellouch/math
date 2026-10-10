import OAI.GameTheory.SnakyConditional.Model

namespace OAI

namespace SnakyConditional
def Internal.SnakyRows011H.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011H.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011H.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011H.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011H.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011H.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011H.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011H.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011H.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011H.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011H.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011H.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows011H.required_603_nodup :
    (([(-1, 0)] : List Cell) : Multiset Cell).Nodup := by decide
def required_603 : Finset Cell :=
  ⟨(([(-1, 0)] : List Cell) : Multiset Cell), Internal.SnakyRows011H.required_603_nodup⟩
def Internal.SnakyRows011H.named_envelope_603_5 : List Cell := ([(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-6, 2), (-6, 3), (-6, 4)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_5_chain : (named_envelope_603_5.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_5_last : (named_envelope_603_5.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-764 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_6 : List Cell := ([(-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -7)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_6_chain : (named_envelope_603_6.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_6_head : (named_envelope_603_6.map Internal.SnakyRows011H.namedCellKey).head? = some (-644 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_6_last : (named_envelope_603_6.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-519 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_4 : List Cell := Internal.SnakyRows011H.named_envelope_603_5 ++ Internal.SnakyRows011H.named_envelope_603_6
theorem Internal.SnakyRows011H.named_envelope_603_4_chain : (named_envelope_603_4.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_5 Internal.SnakyRows011H.named_envelope_603_6 (-764 : ℤ) (-644 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_5_chain Internal.SnakyRows011H.named_envelope_603_6_chain Internal.SnakyRows011H.named_envelope_603_5_last Internal.SnakyRows011H.named_envelope_603_6_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_4_last : (named_envelope_603_4.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-519 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_5 Internal.SnakyRows011H.named_envelope_603_6 (-519 : ℤ) Internal.SnakyRows011H.named_envelope_603_6_last
def Internal.SnakyRows011H.named_envelope_603_8 : List Cell := ([(-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 1), (-4, 2)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_8_chain : (named_envelope_603_8.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_8_head : (named_envelope_603_8.map Internal.SnakyRows011H.namedCellKey).head? = some (-518 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_8_last : (named_envelope_603_8.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-510 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_9 : List Cell := ([(-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -8), (-3, -7), (-3, -6), (-3, -5)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_9_chain : (named_envelope_603_9.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_9_head : (named_envelope_603_9.map Internal.SnakyRows011H.namedCellKey).head? = some (-509 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_9_last : (named_envelope_603_9.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-389 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_7 : List Cell := Internal.SnakyRows011H.named_envelope_603_8 ++ Internal.SnakyRows011H.named_envelope_603_9
theorem Internal.SnakyRows011H.named_envelope_603_7_chain : (named_envelope_603_7.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_8 Internal.SnakyRows011H.named_envelope_603_9 (-510 : ℤ) (-509 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_8_chain Internal.SnakyRows011H.named_envelope_603_9_chain Internal.SnakyRows011H.named_envelope_603_8_last Internal.SnakyRows011H.named_envelope_603_9_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_7_head : (named_envelope_603_7.map Internal.SnakyRows011H.namedCellKey).head? = some (-518 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_8 Internal.SnakyRows011H.named_envelope_603_9 (-518 : ℤ) Internal.SnakyRows011H.named_envelope_603_8_head
theorem Internal.SnakyRows011H.named_envelope_603_7_last : (named_envelope_603_7.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-389 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_8 Internal.SnakyRows011H.named_envelope_603_9 (-389 : ℤ) Internal.SnakyRows011H.named_envelope_603_9_last
def Internal.SnakyRows011H.named_envelope_603_3 : List Cell := Internal.SnakyRows011H.named_envelope_603_4 ++ Internal.SnakyRows011H.named_envelope_603_7
theorem Internal.SnakyRows011H.named_envelope_603_3_chain : (named_envelope_603_3.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_4 Internal.SnakyRows011H.named_envelope_603_7 (-519 : ℤ) (-518 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_4_chain Internal.SnakyRows011H.named_envelope_603_7_chain Internal.SnakyRows011H.named_envelope_603_4_last Internal.SnakyRows011H.named_envelope_603_7_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_3_last : (named_envelope_603_3.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-389 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_4 Internal.SnakyRows011H.named_envelope_603_7 (-389 : ℤ) Internal.SnakyRows011H.named_envelope_603_7_last
def Internal.SnakyRows011H.named_envelope_603_12 : List Cell := ([(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_12_chain : (named_envelope_603_12.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_12_head : (named_envelope_603_12.map Internal.SnakyRows011H.namedCellKey).head? = some (-388 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_12_last : (named_envelope_603_12.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-380 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_13 : List Cell := ([(-3, 5), (-3, 6), (-3, 7), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_13_chain : (named_envelope_603_13.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_13_head : (named_envelope_603_13.map Internal.SnakyRows011H.namedCellKey).head? = some (-379 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_13_last : (named_envelope_603_13.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-259 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_11 : List Cell := Internal.SnakyRows011H.named_envelope_603_12 ++ Internal.SnakyRows011H.named_envelope_603_13
theorem Internal.SnakyRows011H.named_envelope_603_11_chain : (named_envelope_603_11.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_12 Internal.SnakyRows011H.named_envelope_603_13 (-380 : ℤ) (-379 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_12_chain Internal.SnakyRows011H.named_envelope_603_13_chain Internal.SnakyRows011H.named_envelope_603_12_last Internal.SnakyRows011H.named_envelope_603_13_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_11_head : (named_envelope_603_11.map Internal.SnakyRows011H.namedCellKey).head? = some (-388 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_12 Internal.SnakyRows011H.named_envelope_603_13 (-388 : ℤ) Internal.SnakyRows011H.named_envelope_603_12_head
theorem Internal.SnakyRows011H.named_envelope_603_11_last : (named_envelope_603_11.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-259 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_12 Internal.SnakyRows011H.named_envelope_603_13 (-259 : ℤ) Internal.SnakyRows011H.named_envelope_603_13_last
def Internal.SnakyRows011H.named_envelope_603_15 : List Cell := ([(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_15_chain : (named_envelope_603_15.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_15_head : (named_envelope_603_15.map Internal.SnakyRows011H.namedCellKey).head? = some (-258 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_15_last : (named_envelope_603_15.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-251 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_16 : List Cell := ([(-2, 6), (-2, 7), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_16_chain : (named_envelope_603_16.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_16_head : (named_envelope_603_16.map Internal.SnakyRows011H.namedCellKey).head? = some (-250 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_16_last : (named_envelope_603_16.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-133 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_14 : List Cell := Internal.SnakyRows011H.named_envelope_603_15 ++ Internal.SnakyRows011H.named_envelope_603_16
theorem Internal.SnakyRows011H.named_envelope_603_14_chain : (named_envelope_603_14.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_15 Internal.SnakyRows011H.named_envelope_603_16 (-251 : ℤ) (-250 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_15_chain Internal.SnakyRows011H.named_envelope_603_16_chain Internal.SnakyRows011H.named_envelope_603_15_last Internal.SnakyRows011H.named_envelope_603_16_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_14_head : (named_envelope_603_14.map Internal.SnakyRows011H.namedCellKey).head? = some (-258 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_15 Internal.SnakyRows011H.named_envelope_603_16 (-258 : ℤ) Internal.SnakyRows011H.named_envelope_603_15_head
theorem Internal.SnakyRows011H.named_envelope_603_14_last : (named_envelope_603_14.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-133 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_15 Internal.SnakyRows011H.named_envelope_603_16 (-133 : ℤ) Internal.SnakyRows011H.named_envelope_603_16_last
def Internal.SnakyRows011H.named_envelope_603_10 : List Cell := Internal.SnakyRows011H.named_envelope_603_11 ++ Internal.SnakyRows011H.named_envelope_603_14
theorem Internal.SnakyRows011H.named_envelope_603_10_chain : (named_envelope_603_10.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_11 Internal.SnakyRows011H.named_envelope_603_14 (-259 : ℤ) (-258 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_11_chain Internal.SnakyRows011H.named_envelope_603_14_chain Internal.SnakyRows011H.named_envelope_603_11_last Internal.SnakyRows011H.named_envelope_603_14_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_10_head : (named_envelope_603_10.map Internal.SnakyRows011H.namedCellKey).head? = some (-388 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_11 Internal.SnakyRows011H.named_envelope_603_14 (-388 : ℤ) Internal.SnakyRows011H.named_envelope_603_11_head
theorem Internal.SnakyRows011H.named_envelope_603_10_last : (named_envelope_603_10.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-133 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_11 Internal.SnakyRows011H.named_envelope_603_14 (-133 : ℤ) Internal.SnakyRows011H.named_envelope_603_14_last
def Internal.SnakyRows011H.named_envelope_603_2 : List Cell := Internal.SnakyRows011H.named_envelope_603_3 ++ Internal.SnakyRows011H.named_envelope_603_10
theorem Internal.SnakyRows011H.named_envelope_603_2_chain : (named_envelope_603_2.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_3 Internal.SnakyRows011H.named_envelope_603_10 (-389 : ℤ) (-388 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_3_chain Internal.SnakyRows011H.named_envelope_603_10_chain Internal.SnakyRows011H.named_envelope_603_3_last Internal.SnakyRows011H.named_envelope_603_10_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_2_last : (named_envelope_603_2.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-133 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_3 Internal.SnakyRows011H.named_envelope_603_10 (-133 : ℤ) Internal.SnakyRows011H.named_envelope_603_10_last
def Internal.SnakyRows011H.named_envelope_603_20 : List Cell := ([(-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_20_chain : (named_envelope_603_20.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_20_head : (named_envelope_603_20.map Internal.SnakyRows011H.namedCellKey).head? = some (-132 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_20_last : (named_envelope_603_20.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-125 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_21 : List Cell := ([(-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -10)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_21_chain : (named_envelope_603_21.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_21_head : (named_envelope_603_21.map Internal.SnakyRows011H.namedCellKey).head? = some (-124 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_21_last : (named_envelope_603_21.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-10 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_19 : List Cell := Internal.SnakyRows011H.named_envelope_603_20 ++ Internal.SnakyRows011H.named_envelope_603_21
theorem Internal.SnakyRows011H.named_envelope_603_19_chain : (named_envelope_603_19.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_20 Internal.SnakyRows011H.named_envelope_603_21 (-125 : ℤ) (-124 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_20_chain Internal.SnakyRows011H.named_envelope_603_21_chain Internal.SnakyRows011H.named_envelope_603_20_last Internal.SnakyRows011H.named_envelope_603_21_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_19_head : (named_envelope_603_19.map Internal.SnakyRows011H.namedCellKey).head? = some (-132 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_20 Internal.SnakyRows011H.named_envelope_603_21 (-132 : ℤ) Internal.SnakyRows011H.named_envelope_603_20_head
theorem Internal.SnakyRows011H.named_envelope_603_19_last : (named_envelope_603_19.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-10 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_20 Internal.SnakyRows011H.named_envelope_603_21 (-10 : ℤ) Internal.SnakyRows011H.named_envelope_603_21_last
def Internal.SnakyRows011H.named_envelope_603_23 : List Cell := ([(0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_23_chain : (named_envelope_603_23.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_23_head : (named_envelope_603_23.map Internal.SnakyRows011H.namedCellKey).head? = some (-9 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_23_last : (named_envelope_603_23.map Internal.SnakyRows011H.namedCellKey).getLast? = some (-2 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_24 : List Cell := ([(0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_24_chain : (named_envelope_603_24.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_24_head : (named_envelope_603_24.map Internal.SnakyRows011H.namedCellKey).head? = some (-1 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_24_last : (named_envelope_603_24.map Internal.SnakyRows011H.namedCellKey).getLast? = some (7 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_22 : List Cell := Internal.SnakyRows011H.named_envelope_603_23 ++ Internal.SnakyRows011H.named_envelope_603_24
theorem Internal.SnakyRows011H.named_envelope_603_22_chain : (named_envelope_603_22.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_23 Internal.SnakyRows011H.named_envelope_603_24 (-2 : ℤ) (-1 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_23_chain Internal.SnakyRows011H.named_envelope_603_24_chain Internal.SnakyRows011H.named_envelope_603_23_last Internal.SnakyRows011H.named_envelope_603_24_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_22_head : (named_envelope_603_22.map Internal.SnakyRows011H.namedCellKey).head? = some (-9 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_23 Internal.SnakyRows011H.named_envelope_603_24 (-9 : ℤ) Internal.SnakyRows011H.named_envelope_603_23_head
theorem Internal.SnakyRows011H.named_envelope_603_22_last : (named_envelope_603_22.map Internal.SnakyRows011H.namedCellKey).getLast? = some (7 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_23 Internal.SnakyRows011H.named_envelope_603_24 (7 : ℤ) Internal.SnakyRows011H.named_envelope_603_24_last
def Internal.SnakyRows011H.named_envelope_603_18 : List Cell := Internal.SnakyRows011H.named_envelope_603_19 ++ Internal.SnakyRows011H.named_envelope_603_22
theorem Internal.SnakyRows011H.named_envelope_603_18_chain : (named_envelope_603_18.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_19 Internal.SnakyRows011H.named_envelope_603_22 (-10 : ℤ) (-9 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_19_chain Internal.SnakyRows011H.named_envelope_603_22_chain Internal.SnakyRows011H.named_envelope_603_19_last Internal.SnakyRows011H.named_envelope_603_22_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_18_head : (named_envelope_603_18.map Internal.SnakyRows011H.namedCellKey).head? = some (-132 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_19 Internal.SnakyRows011H.named_envelope_603_22 (-132 : ℤ) Internal.SnakyRows011H.named_envelope_603_19_head
theorem Internal.SnakyRows011H.named_envelope_603_18_last : (named_envelope_603_18.map Internal.SnakyRows011H.namedCellKey).getLast? = some (7 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_19 Internal.SnakyRows011H.named_envelope_603_22 (7 : ℤ) Internal.SnakyRows011H.named_envelope_603_22_last
def Internal.SnakyRows011H.named_envelope_603_27 : List Cell := ([(0, 8), (0, 9), (0, 10), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_27_chain : (named_envelope_603_27.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_27_head : (named_envelope_603_27.map Internal.SnakyRows011H.namedCellKey).head? = some (8 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_27_last : (named_envelope_603_27.map Internal.SnakyRows011H.namedCellKey).getLast? = some (121 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_28 : List Cell := ([(1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_28_chain : (named_envelope_603_28.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_28_head : (named_envelope_603_28.map Internal.SnakyRows011H.namedCellKey).head? = some (122 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_28_last : (named_envelope_603_28.map Internal.SnakyRows011H.namedCellKey).getLast? = some (130 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_26 : List Cell := Internal.SnakyRows011H.named_envelope_603_27 ++ Internal.SnakyRows011H.named_envelope_603_28
theorem Internal.SnakyRows011H.named_envelope_603_26_chain : (named_envelope_603_26.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_27 Internal.SnakyRows011H.named_envelope_603_28 (121 : ℤ) (122 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_27_chain Internal.SnakyRows011H.named_envelope_603_28_chain Internal.SnakyRows011H.named_envelope_603_27_last Internal.SnakyRows011H.named_envelope_603_28_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_26_head : (named_envelope_603_26.map Internal.SnakyRows011H.namedCellKey).head? = some (8 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_27 Internal.SnakyRows011H.named_envelope_603_28 (8 : ℤ) Internal.SnakyRows011H.named_envelope_603_27_head
theorem Internal.SnakyRows011H.named_envelope_603_26_last : (named_envelope_603_26.map Internal.SnakyRows011H.namedCellKey).getLast? = some (130 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_27 Internal.SnakyRows011H.named_envelope_603_28 (130 : ℤ) Internal.SnakyRows011H.named_envelope_603_28_last
def Internal.SnakyRows011H.named_envelope_603_30 : List Cell := ([(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_30_chain : (named_envelope_603_30.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_30_head : (named_envelope_603_30.map Internal.SnakyRows011H.namedCellKey).head? = some (131 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_30_last : (named_envelope_603_30.map Internal.SnakyRows011H.namedCellKey).getLast? = some (139 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_31 : List Cell := ([(2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_31_chain : (named_envelope_603_31.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_31_head : (named_envelope_603_31.map Internal.SnakyRows011H.namedCellKey).head? = some (247 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_31_last : (named_envelope_603_31.map Internal.SnakyRows011H.namedCellKey).getLast? = some (255 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_29 : List Cell := Internal.SnakyRows011H.named_envelope_603_30 ++ Internal.SnakyRows011H.named_envelope_603_31
theorem Internal.SnakyRows011H.named_envelope_603_29_chain : (named_envelope_603_29.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_30 Internal.SnakyRows011H.named_envelope_603_31 (139 : ℤ) (247 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_30_chain Internal.SnakyRows011H.named_envelope_603_31_chain Internal.SnakyRows011H.named_envelope_603_30_last Internal.SnakyRows011H.named_envelope_603_31_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_29_head : (named_envelope_603_29.map Internal.SnakyRows011H.namedCellKey).head? = some (131 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_30 Internal.SnakyRows011H.named_envelope_603_31 (131 : ℤ) Internal.SnakyRows011H.named_envelope_603_30_head
theorem Internal.SnakyRows011H.named_envelope_603_29_last : (named_envelope_603_29.map Internal.SnakyRows011H.namedCellKey).getLast? = some (255 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_30 Internal.SnakyRows011H.named_envelope_603_31 (255 : ℤ) Internal.SnakyRows011H.named_envelope_603_31_last
def Internal.SnakyRows011H.named_envelope_603_25 : List Cell := Internal.SnakyRows011H.named_envelope_603_26 ++ Internal.SnakyRows011H.named_envelope_603_29
theorem Internal.SnakyRows011H.named_envelope_603_25_chain : (named_envelope_603_25.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_26 Internal.SnakyRows011H.named_envelope_603_29 (130 : ℤ) (131 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_26_chain Internal.SnakyRows011H.named_envelope_603_29_chain Internal.SnakyRows011H.named_envelope_603_26_last Internal.SnakyRows011H.named_envelope_603_29_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_25_head : (named_envelope_603_25.map Internal.SnakyRows011H.namedCellKey).head? = some (8 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_26 Internal.SnakyRows011H.named_envelope_603_29 (8 : ℤ) Internal.SnakyRows011H.named_envelope_603_26_head
theorem Internal.SnakyRows011H.named_envelope_603_25_last : (named_envelope_603_25.map Internal.SnakyRows011H.namedCellKey).getLast? = some (255 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_26 Internal.SnakyRows011H.named_envelope_603_29 (255 : ℤ) Internal.SnakyRows011H.named_envelope_603_29_last
def Internal.SnakyRows011H.named_envelope_603_17 : List Cell := Internal.SnakyRows011H.named_envelope_603_18 ++ Internal.SnakyRows011H.named_envelope_603_25
theorem Internal.SnakyRows011H.named_envelope_603_17_chain : (named_envelope_603_17.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_18 Internal.SnakyRows011H.named_envelope_603_25 (7 : ℤ) (8 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_18_chain Internal.SnakyRows011H.named_envelope_603_25_chain Internal.SnakyRows011H.named_envelope_603_18_last Internal.SnakyRows011H.named_envelope_603_25_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_17_head : (named_envelope_603_17.map Internal.SnakyRows011H.namedCellKey).head? = some (-132 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_18 Internal.SnakyRows011H.named_envelope_603_25 (-132 : ℤ) Internal.SnakyRows011H.named_envelope_603_18_head
theorem Internal.SnakyRows011H.named_envelope_603_17_last : (named_envelope_603_17.map Internal.SnakyRows011H.namedCellKey).getLast? = some (255 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_18 Internal.SnakyRows011H.named_envelope_603_25 (255 : ℤ) Internal.SnakyRows011H.named_envelope_603_25_last
def Internal.SnakyRows011H.named_envelope_603_1 : List Cell := Internal.SnakyRows011H.named_envelope_603_2 ++ Internal.SnakyRows011H.named_envelope_603_17
theorem Internal.SnakyRows011H.named_envelope_603_1_chain : (named_envelope_603_1.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_2 Internal.SnakyRows011H.named_envelope_603_17 (-133 : ℤ) (-132 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_2_chain Internal.SnakyRows011H.named_envelope_603_17_chain Internal.SnakyRows011H.named_envelope_603_2_last Internal.SnakyRows011H.named_envelope_603_17_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_1_last : (named_envelope_603_1.map Internal.SnakyRows011H.namedCellKey).getLast? = some (255 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_2 Internal.SnakyRows011H.named_envelope_603_17 (255 : ℤ) Internal.SnakyRows011H.named_envelope_603_17_last
def Internal.SnakyRows011H.named_envelope_603_36 : List Cell := ([(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_36_chain : (named_envelope_603_36.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_36_head : (named_envelope_603_36.map Internal.SnakyRows011H.namedCellKey).head? = some (256 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_36_last : (named_envelope_603_36.map Internal.SnakyRows011H.namedCellKey).getLast? = some (263 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_37 : List Cell := ([(2, 8), (2, 9), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_37_chain : (named_envelope_603_37.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_37_head : (named_envelope_603_37.map Internal.SnakyRows011H.namedCellKey).head? = some (264 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_37_last : (named_envelope_603_37.map Internal.SnakyRows011H.namedCellKey).getLast? = some (381 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_35 : List Cell := Internal.SnakyRows011H.named_envelope_603_36 ++ Internal.SnakyRows011H.named_envelope_603_37
theorem Internal.SnakyRows011H.named_envelope_603_35_chain : (named_envelope_603_35.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_36 Internal.SnakyRows011H.named_envelope_603_37 (263 : ℤ) (264 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_36_chain Internal.SnakyRows011H.named_envelope_603_37_chain Internal.SnakyRows011H.named_envelope_603_36_last Internal.SnakyRows011H.named_envelope_603_37_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_35_head : (named_envelope_603_35.map Internal.SnakyRows011H.namedCellKey).head? = some (256 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_36 Internal.SnakyRows011H.named_envelope_603_37 (256 : ℤ) Internal.SnakyRows011H.named_envelope_603_36_head
theorem Internal.SnakyRows011H.named_envelope_603_35_last : (named_envelope_603_35.map Internal.SnakyRows011H.namedCellKey).getLast? = some (381 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_36 Internal.SnakyRows011H.named_envelope_603_37 (381 : ℤ) Internal.SnakyRows011H.named_envelope_603_37_last
def Internal.SnakyRows011H.named_envelope_603_39 : List Cell := ([(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_39_chain : (named_envelope_603_39.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_39_head : (named_envelope_603_39.map Internal.SnakyRows011H.namedCellKey).head? = some (382 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_39_last : (named_envelope_603_39.map Internal.SnakyRows011H.namedCellKey).getLast? = some (389 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_40 : List Cell := ([(3, 6), (3, 7), (3, 8), (3, 9), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_40_chain : (named_envelope_603_40.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_40_head : (named_envelope_603_40.map Internal.SnakyRows011H.namedCellKey).head? = some (390 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_40_last : (named_envelope_603_40.map Internal.SnakyRows011H.namedCellKey).getLast? = some (507 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_38 : List Cell := Internal.SnakyRows011H.named_envelope_603_39 ++ Internal.SnakyRows011H.named_envelope_603_40
theorem Internal.SnakyRows011H.named_envelope_603_38_chain : (named_envelope_603_38.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_39 Internal.SnakyRows011H.named_envelope_603_40 (389 : ℤ) (390 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_39_chain Internal.SnakyRows011H.named_envelope_603_40_chain Internal.SnakyRows011H.named_envelope_603_39_last Internal.SnakyRows011H.named_envelope_603_40_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_38_head : (named_envelope_603_38.map Internal.SnakyRows011H.namedCellKey).head? = some (382 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_39 Internal.SnakyRows011H.named_envelope_603_40 (382 : ℤ) Internal.SnakyRows011H.named_envelope_603_39_head
theorem Internal.SnakyRows011H.named_envelope_603_38_last : (named_envelope_603_38.map Internal.SnakyRows011H.namedCellKey).getLast? = some (507 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_39 Internal.SnakyRows011H.named_envelope_603_40 (507 : ℤ) Internal.SnakyRows011H.named_envelope_603_40_last
def Internal.SnakyRows011H.named_envelope_603_34 : List Cell := Internal.SnakyRows011H.named_envelope_603_35 ++ Internal.SnakyRows011H.named_envelope_603_38
theorem Internal.SnakyRows011H.named_envelope_603_34_chain : (named_envelope_603_34.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_35 Internal.SnakyRows011H.named_envelope_603_38 (381 : ℤ) (382 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_35_chain Internal.SnakyRows011H.named_envelope_603_38_chain Internal.SnakyRows011H.named_envelope_603_35_last Internal.SnakyRows011H.named_envelope_603_38_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_34_head : (named_envelope_603_34.map Internal.SnakyRows011H.namedCellKey).head? = some (256 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_35 Internal.SnakyRows011H.named_envelope_603_38 (256 : ℤ) Internal.SnakyRows011H.named_envelope_603_35_head
theorem Internal.SnakyRows011H.named_envelope_603_34_last : (named_envelope_603_34.map Internal.SnakyRows011H.namedCellKey).getLast? = some (507 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_35 Internal.SnakyRows011H.named_envelope_603_38 (507 : ℤ) Internal.SnakyRows011H.named_envelope_603_38_last
def Internal.SnakyRows011H.named_envelope_603_43 : List Cell := ([(4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_43_chain : (named_envelope_603_43.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_43_head : (named_envelope_603_43.map Internal.SnakyRows011H.namedCellKey).head? = some (508 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_43_last : (named_envelope_603_43.map Internal.SnakyRows011H.namedCellKey).getLast? = some (515 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_44 : List Cell := ([(4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -9), (5, -8), (5, -7)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_44_chain : (named_envelope_603_44.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_44_head : (named_envelope_603_44.map Internal.SnakyRows011H.namedCellKey).head? = some (516 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_44_last : (named_envelope_603_44.map Internal.SnakyRows011H.namedCellKey).getLast? = some (633 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_42 : List Cell := Internal.SnakyRows011H.named_envelope_603_43 ++ Internal.SnakyRows011H.named_envelope_603_44
theorem Internal.SnakyRows011H.named_envelope_603_42_chain : (named_envelope_603_42.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_43 Internal.SnakyRows011H.named_envelope_603_44 (515 : ℤ) (516 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_43_chain Internal.SnakyRows011H.named_envelope_603_44_chain Internal.SnakyRows011H.named_envelope_603_43_last Internal.SnakyRows011H.named_envelope_603_44_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_42_head : (named_envelope_603_42.map Internal.SnakyRows011H.namedCellKey).head? = some (508 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_43 Internal.SnakyRows011H.named_envelope_603_44 (508 : ℤ) Internal.SnakyRows011H.named_envelope_603_43_head
theorem Internal.SnakyRows011H.named_envelope_603_42_last : (named_envelope_603_42.map Internal.SnakyRows011H.namedCellKey).getLast? = some (633 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_43 Internal.SnakyRows011H.named_envelope_603_44 (633 : ℤ) Internal.SnakyRows011H.named_envelope_603_44_last
def Internal.SnakyRows011H.named_envelope_603_46 : List Cell := ([(5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_46_chain : (named_envelope_603_46.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_46_head : (named_envelope_603_46.map Internal.SnakyRows011H.namedCellKey).head? = some (634 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_46_last : (named_envelope_603_46.map Internal.SnakyRows011H.namedCellKey).getLast? = some (642 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_47 : List Cell := ([(5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -7), (6, -6)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_47_chain : (named_envelope_603_47.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_47_head : (named_envelope_603_47.map Internal.SnakyRows011H.namedCellKey).head? = some (643 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_47_last : (named_envelope_603_47.map Internal.SnakyRows011H.namedCellKey).getLast? = some (762 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_45 : List Cell := Internal.SnakyRows011H.named_envelope_603_46 ++ Internal.SnakyRows011H.named_envelope_603_47
theorem Internal.SnakyRows011H.named_envelope_603_45_chain : (named_envelope_603_45.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_46 Internal.SnakyRows011H.named_envelope_603_47 (642 : ℤ) (643 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_46_chain Internal.SnakyRows011H.named_envelope_603_47_chain Internal.SnakyRows011H.named_envelope_603_46_last Internal.SnakyRows011H.named_envelope_603_47_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_45_head : (named_envelope_603_45.map Internal.SnakyRows011H.namedCellKey).head? = some (634 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_46 Internal.SnakyRows011H.named_envelope_603_47 (634 : ℤ) Internal.SnakyRows011H.named_envelope_603_46_head
theorem Internal.SnakyRows011H.named_envelope_603_45_last : (named_envelope_603_45.map Internal.SnakyRows011H.namedCellKey).getLast? = some (762 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_46 Internal.SnakyRows011H.named_envelope_603_47 (762 : ℤ) Internal.SnakyRows011H.named_envelope_603_47_last
def Internal.SnakyRows011H.named_envelope_603_41 : List Cell := Internal.SnakyRows011H.named_envelope_603_42 ++ Internal.SnakyRows011H.named_envelope_603_45
theorem Internal.SnakyRows011H.named_envelope_603_41_chain : (named_envelope_603_41.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_42 Internal.SnakyRows011H.named_envelope_603_45 (633 : ℤ) (634 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_42_chain Internal.SnakyRows011H.named_envelope_603_45_chain Internal.SnakyRows011H.named_envelope_603_42_last Internal.SnakyRows011H.named_envelope_603_45_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_41_head : (named_envelope_603_41.map Internal.SnakyRows011H.namedCellKey).head? = some (508 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_42 Internal.SnakyRows011H.named_envelope_603_45 (508 : ℤ) Internal.SnakyRows011H.named_envelope_603_42_head
theorem Internal.SnakyRows011H.named_envelope_603_41_last : (named_envelope_603_41.map Internal.SnakyRows011H.namedCellKey).getLast? = some (762 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_42 Internal.SnakyRows011H.named_envelope_603_45 (762 : ℤ) Internal.SnakyRows011H.named_envelope_603_45_last
def Internal.SnakyRows011H.named_envelope_603_33 : List Cell := Internal.SnakyRows011H.named_envelope_603_34 ++ Internal.SnakyRows011H.named_envelope_603_41
theorem Internal.SnakyRows011H.named_envelope_603_33_chain : (named_envelope_603_33.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_34 Internal.SnakyRows011H.named_envelope_603_41 (507 : ℤ) (508 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_34_chain Internal.SnakyRows011H.named_envelope_603_41_chain Internal.SnakyRows011H.named_envelope_603_34_last Internal.SnakyRows011H.named_envelope_603_41_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_33_head : (named_envelope_603_33.map Internal.SnakyRows011H.namedCellKey).head? = some (256 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_34 Internal.SnakyRows011H.named_envelope_603_41 (256 : ℤ) Internal.SnakyRows011H.named_envelope_603_34_head
theorem Internal.SnakyRows011H.named_envelope_603_33_last : (named_envelope_603_33.map Internal.SnakyRows011H.namedCellKey).getLast? = some (762 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_34 Internal.SnakyRows011H.named_envelope_603_41 (762 : ℤ) Internal.SnakyRows011H.named_envelope_603_41_last
def Internal.SnakyRows011H.named_envelope_603_51 : List Cell := ([(6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_51_chain : (named_envelope_603_51.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_51_head : (named_envelope_603_51.map Internal.SnakyRows011H.namedCellKey).head? = some (763 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_51_last : (named_envelope_603_51.map Internal.SnakyRows011H.namedCellKey).getLast? = some (770 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_52 : List Cell := ([(6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_52_chain : (named_envelope_603_52.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_52_head : (named_envelope_603_52.map Internal.SnakyRows011H.namedCellKey).head? = some (771 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_52_last : (named_envelope_603_52.map Internal.SnakyRows011H.namedCellKey).getLast? = some (892 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_50 : List Cell := Internal.SnakyRows011H.named_envelope_603_51 ++ Internal.SnakyRows011H.named_envelope_603_52
theorem Internal.SnakyRows011H.named_envelope_603_50_chain : (named_envelope_603_50.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_51 Internal.SnakyRows011H.named_envelope_603_52 (770 : ℤ) (771 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_51_chain Internal.SnakyRows011H.named_envelope_603_52_chain Internal.SnakyRows011H.named_envelope_603_51_last Internal.SnakyRows011H.named_envelope_603_52_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_50_head : (named_envelope_603_50.map Internal.SnakyRows011H.namedCellKey).head? = some (763 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_51 Internal.SnakyRows011H.named_envelope_603_52 (763 : ℤ) Internal.SnakyRows011H.named_envelope_603_51_head
theorem Internal.SnakyRows011H.named_envelope_603_50_last : (named_envelope_603_50.map Internal.SnakyRows011H.namedCellKey).getLast? = some (892 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_51 Internal.SnakyRows011H.named_envelope_603_52 (892 : ℤ) Internal.SnakyRows011H.named_envelope_603_52_last
def Internal.SnakyRows011H.named_envelope_603_54 : List Cell := ([(7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_54_chain : (named_envelope_603_54.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_54_head : (named_envelope_603_54.map Internal.SnakyRows011H.namedCellKey).head? = some (893 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_54_last : (named_envelope_603_54.map Internal.SnakyRows011H.namedCellKey).getLast? = some (900 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_55 : List Cell := ([(7, 5), (7, 6), (7, 7), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_55_chain : (named_envelope_603_55.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_55_head : (named_envelope_603_55.map Internal.SnakyRows011H.namedCellKey).head? = some (901 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_55_last : (named_envelope_603_55.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1024 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_53 : List Cell := Internal.SnakyRows011H.named_envelope_603_54 ++ Internal.SnakyRows011H.named_envelope_603_55
theorem Internal.SnakyRows011H.named_envelope_603_53_chain : (named_envelope_603_53.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_54 Internal.SnakyRows011H.named_envelope_603_55 (900 : ℤ) (901 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_54_chain Internal.SnakyRows011H.named_envelope_603_55_chain Internal.SnakyRows011H.named_envelope_603_54_last Internal.SnakyRows011H.named_envelope_603_55_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_53_head : (named_envelope_603_53.map Internal.SnakyRows011H.namedCellKey).head? = some (893 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_54 Internal.SnakyRows011H.named_envelope_603_55 (893 : ℤ) Internal.SnakyRows011H.named_envelope_603_54_head
theorem Internal.SnakyRows011H.named_envelope_603_53_last : (named_envelope_603_53.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1024 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_54 Internal.SnakyRows011H.named_envelope_603_55 (1024 : ℤ) Internal.SnakyRows011H.named_envelope_603_55_last
def Internal.SnakyRows011H.named_envelope_603_49 : List Cell := Internal.SnakyRows011H.named_envelope_603_50 ++ Internal.SnakyRows011H.named_envelope_603_53
theorem Internal.SnakyRows011H.named_envelope_603_49_chain : (named_envelope_603_49.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_50 Internal.SnakyRows011H.named_envelope_603_53 (892 : ℤ) (893 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_50_chain Internal.SnakyRows011H.named_envelope_603_53_chain Internal.SnakyRows011H.named_envelope_603_50_last Internal.SnakyRows011H.named_envelope_603_53_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_49_head : (named_envelope_603_49.map Internal.SnakyRows011H.namedCellKey).head? = some (763 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_50 Internal.SnakyRows011H.named_envelope_603_53 (763 : ℤ) Internal.SnakyRows011H.named_envelope_603_50_head
theorem Internal.SnakyRows011H.named_envelope_603_49_last : (named_envelope_603_49.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1024 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_50 Internal.SnakyRows011H.named_envelope_603_53 (1024 : ℤ) Internal.SnakyRows011H.named_envelope_603_53_last
def Internal.SnakyRows011H.named_envelope_603_58 : List Cell := ([(8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -5), (9, -4), (9, -3)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_58_chain : (named_envelope_603_58.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_58_head : (named_envelope_603_58.map Internal.SnakyRows011H.namedCellKey).head? = some (1025 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_58_last : (named_envelope_603_58.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1149 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_59 : List Cell := ([(9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -5)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_59_chain : (named_envelope_603_59.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_59_head : (named_envelope_603_59.map Internal.SnakyRows011H.namedCellKey).head? = some (1150 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_59_last : (named_envelope_603_59.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1275 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_57 : List Cell := Internal.SnakyRows011H.named_envelope_603_58 ++ Internal.SnakyRows011H.named_envelope_603_59
theorem Internal.SnakyRows011H.named_envelope_603_57_chain : (named_envelope_603_57.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_58 Internal.SnakyRows011H.named_envelope_603_59 (1149 : ℤ) (1150 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_58_chain Internal.SnakyRows011H.named_envelope_603_59_chain Internal.SnakyRows011H.named_envelope_603_58_last Internal.SnakyRows011H.named_envelope_603_59_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_57_head : (named_envelope_603_57.map Internal.SnakyRows011H.namedCellKey).head? = some (1025 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_58 Internal.SnakyRows011H.named_envelope_603_59 (1025 : ℤ) Internal.SnakyRows011H.named_envelope_603_58_head
theorem Internal.SnakyRows011H.named_envelope_603_57_last : (named_envelope_603_57.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1275 : ℤ) :=
  Internal.SnakyRows011H.named_last_append Internal.SnakyRows011H.named_envelope_603_58 Internal.SnakyRows011H.named_envelope_603_59 (1275 : ℤ) Internal.SnakyRows011H.named_envelope_603_59_last
def Internal.SnakyRows011H.named_envelope_603_61 : List Cell := ([(10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 5), (11, -3)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_61_chain : (named_envelope_603_61.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_61_head : (named_envelope_603_61.map Internal.SnakyRows011H.namedCellKey).head? = some (1277 : ℤ) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_61_last : (named_envelope_603_61.map Internal.SnakyRows011H.namedCellKey).getLast? = some (1405 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_62 : List Cell := ([(11, -2), (11, -1), (11, 1), (11, 2), (11, 3), (12, -3), (12, -1), (12, 1), (12, 3)] : List Cell)
theorem Internal.SnakyRows011H.named_envelope_603_62_chain : (named_envelope_603_62.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows011H.named_envelope_603_62_head : (named_envelope_603_62.map Internal.SnakyRows011H.namedCellKey).head? = some (1406 : ℤ) := by decide
def Internal.SnakyRows011H.named_envelope_603_60 : List Cell := Internal.SnakyRows011H.named_envelope_603_61 ++ Internal.SnakyRows011H.named_envelope_603_62
theorem Internal.SnakyRows011H.named_envelope_603_60_chain : (named_envelope_603_60.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_61 Internal.SnakyRows011H.named_envelope_603_62 (1405 : ℤ) (1406 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_61_chain Internal.SnakyRows011H.named_envelope_603_62_chain Internal.SnakyRows011H.named_envelope_603_61_last Internal.SnakyRows011H.named_envelope_603_62_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_60_head : (named_envelope_603_60.map Internal.SnakyRows011H.namedCellKey).head? = some (1277 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_61 Internal.SnakyRows011H.named_envelope_603_62 (1277 : ℤ) Internal.SnakyRows011H.named_envelope_603_61_head
def Internal.SnakyRows011H.named_envelope_603_56 : List Cell := Internal.SnakyRows011H.named_envelope_603_57 ++ Internal.SnakyRows011H.named_envelope_603_60
theorem Internal.SnakyRows011H.named_envelope_603_56_chain : (named_envelope_603_56.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_57 Internal.SnakyRows011H.named_envelope_603_60 (1275 : ℤ) (1277 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_57_chain Internal.SnakyRows011H.named_envelope_603_60_chain Internal.SnakyRows011H.named_envelope_603_57_last Internal.SnakyRows011H.named_envelope_603_60_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_56_head : (named_envelope_603_56.map Internal.SnakyRows011H.namedCellKey).head? = some (1025 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_57 Internal.SnakyRows011H.named_envelope_603_60 (1025 : ℤ) Internal.SnakyRows011H.named_envelope_603_57_head
def Internal.SnakyRows011H.named_envelope_603_48 : List Cell := Internal.SnakyRows011H.named_envelope_603_49 ++ Internal.SnakyRows011H.named_envelope_603_56
theorem Internal.SnakyRows011H.named_envelope_603_48_chain : (named_envelope_603_48.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_49 Internal.SnakyRows011H.named_envelope_603_56 (1024 : ℤ) (1025 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_49_chain Internal.SnakyRows011H.named_envelope_603_56_chain Internal.SnakyRows011H.named_envelope_603_49_last Internal.SnakyRows011H.named_envelope_603_56_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_48_head : (named_envelope_603_48.map Internal.SnakyRows011H.namedCellKey).head? = some (763 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_49 Internal.SnakyRows011H.named_envelope_603_56 (763 : ℤ) Internal.SnakyRows011H.named_envelope_603_49_head
def Internal.SnakyRows011H.named_envelope_603_32 : List Cell := Internal.SnakyRows011H.named_envelope_603_33 ++ Internal.SnakyRows011H.named_envelope_603_48
theorem Internal.SnakyRows011H.named_envelope_603_32_chain : (named_envelope_603_32.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_33 Internal.SnakyRows011H.named_envelope_603_48 (762 : ℤ) (763 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_33_chain Internal.SnakyRows011H.named_envelope_603_48_chain Internal.SnakyRows011H.named_envelope_603_33_last Internal.SnakyRows011H.named_envelope_603_48_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_32_head : (named_envelope_603_32.map Internal.SnakyRows011H.namedCellKey).head? = some (256 : ℤ) :=
  Internal.SnakyRows011H.named_head_append Internal.SnakyRows011H.named_envelope_603_33 Internal.SnakyRows011H.named_envelope_603_48 (256 : ℤ) Internal.SnakyRows011H.named_envelope_603_33_head
def Internal.SnakyRows011H.named_envelope_603_0 : List Cell := Internal.SnakyRows011H.named_envelope_603_1 ++ Internal.SnakyRows011H.named_envelope_603_32
theorem Internal.SnakyRows011H.named_envelope_603_0_chain : (named_envelope_603_0.map Internal.SnakyRows011H.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows011H.named_chain_append Internal.SnakyRows011H.named_envelope_603_1 Internal.SnakyRows011H.named_envelope_603_32 (255 : ℤ) (256 : ℤ)
    Internal.SnakyRows011H.named_envelope_603_1_chain Internal.SnakyRows011H.named_envelope_603_32_chain Internal.SnakyRows011H.named_envelope_603_1_last Internal.SnakyRows011H.named_envelope_603_32_head (by decide)
theorem Internal.SnakyRows011H.named_envelope_603_nodup : (Internal.SnakyRows011H.named_envelope_603_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows011H.named_nodup_of_chain Internal.SnakyRows011H.named_envelope_603_0 Internal.SnakyRows011H.named_envelope_603_0_chain
def envelope_603 : Finset Cell := ⟨(Internal.SnakyRows011H.named_envelope_603_0 : Multiset Cell), Internal.SnakyRows011H.named_envelope_603_nodup⟩
end SnakyConditional

end OAI
