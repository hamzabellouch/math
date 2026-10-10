import OAI.GameTheory.SnakyConditional.Model

namespace OAI

namespace SnakyConditional
def Internal.SnakyRows010.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows010.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows010.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows010.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows010.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows010.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows010.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows010.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows010.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows010.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows010.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows010.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows010.required_595_nodup :
    (([(-1, 0)] : List Cell) : Multiset Cell).Nodup := by decide
def required_595 : Finset Cell :=
  ⟨(([(-1, 0)] : List Cell) : Multiset Cell), Internal.SnakyRows010.required_595_nodup⟩
def Internal.SnakyRows010.named_envelope_595_4 : List Cell := ([(-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_4_chain : (named_envelope_595_4.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_4_last : (named_envelope_595_4.map Internal.SnakyRows010.namedCellKey).getLast? = some (-513 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_5 : List Cell := ([(-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_5_chain : (named_envelope_595_5.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_5_head : (named_envelope_595_5.map Internal.SnakyRows010.namedCellKey).head? = some (-512 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_5_last : (named_envelope_595_5.map Internal.SnakyRows010.namedCellKey).getLast? = some (-382 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_3 : List Cell := Internal.SnakyRows010.named_envelope_595_4 ++ Internal.SnakyRows010.named_envelope_595_5
theorem Internal.SnakyRows010.named_envelope_595_3_chain : (named_envelope_595_3.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_4 Internal.SnakyRows010.named_envelope_595_5 (-513 : ℤ) (-512 : ℤ)
    Internal.SnakyRows010.named_envelope_595_4_chain Internal.SnakyRows010.named_envelope_595_5_chain Internal.SnakyRows010.named_envelope_595_4_last Internal.SnakyRows010.named_envelope_595_5_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_3_last : (named_envelope_595_3.map Internal.SnakyRows010.namedCellKey).getLast? = some (-382 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_4 Internal.SnakyRows010.named_envelope_595_5 (-382 : ℤ) Internal.SnakyRows010.named_envelope_595_5_last
def Internal.SnakyRows010.named_envelope_595_7 : List Cell := ([(-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_7_chain : (named_envelope_595_7.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_7_head : (named_envelope_595_7.map Internal.SnakyRows010.namedCellKey).head? = some (-381 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_7_last : (named_envelope_595_7.map Internal.SnakyRows010.namedCellKey).getLast? = some (-249 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_8 : List Cell := ([(-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_8_chain : (named_envelope_595_8.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_8_head : (named_envelope_595_8.map Internal.SnakyRows010.namedCellKey).head? = some (-248 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_8_last : (named_envelope_595_8.map Internal.SnakyRows010.namedCellKey).getLast? = some (-124 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_6 : List Cell := Internal.SnakyRows010.named_envelope_595_7 ++ Internal.SnakyRows010.named_envelope_595_8
theorem Internal.SnakyRows010.named_envelope_595_6_chain : (named_envelope_595_6.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_7 Internal.SnakyRows010.named_envelope_595_8 (-249 : ℤ) (-248 : ℤ)
    Internal.SnakyRows010.named_envelope_595_7_chain Internal.SnakyRows010.named_envelope_595_8_chain Internal.SnakyRows010.named_envelope_595_7_last Internal.SnakyRows010.named_envelope_595_8_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_6_head : (named_envelope_595_6.map Internal.SnakyRows010.namedCellKey).head? = some (-381 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_7 Internal.SnakyRows010.named_envelope_595_8 (-381 : ℤ) Internal.SnakyRows010.named_envelope_595_7_head
theorem Internal.SnakyRows010.named_envelope_595_6_last : (named_envelope_595_6.map Internal.SnakyRows010.namedCellKey).getLast? = some (-124 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_7 Internal.SnakyRows010.named_envelope_595_8 (-124 : ℤ) Internal.SnakyRows010.named_envelope_595_8_last
def Internal.SnakyRows010.named_envelope_595_2 : List Cell := Internal.SnakyRows010.named_envelope_595_3 ++ Internal.SnakyRows010.named_envelope_595_6
theorem Internal.SnakyRows010.named_envelope_595_2_chain : (named_envelope_595_2.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_3 Internal.SnakyRows010.named_envelope_595_6 (-382 : ℤ) (-381 : ℤ)
    Internal.SnakyRows010.named_envelope_595_3_chain Internal.SnakyRows010.named_envelope_595_6_chain Internal.SnakyRows010.named_envelope_595_3_last Internal.SnakyRows010.named_envelope_595_6_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_2_last : (named_envelope_595_2.map Internal.SnakyRows010.namedCellKey).getLast? = some (-124 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_3 Internal.SnakyRows010.named_envelope_595_6 (-124 : ℤ) Internal.SnakyRows010.named_envelope_595_6_last
def Internal.SnakyRows010.named_envelope_595_11 : List Cell := ([(-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_11_chain : (named_envelope_595_11.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_11_head : (named_envelope_595_11.map Internal.SnakyRows010.namedCellKey).head? = some (-123 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_11_last : (named_envelope_595_11.map Internal.SnakyRows010.namedCellKey).getLast? = some (1 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_12 : List Cell := ([(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_12_chain : (named_envelope_595_12.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_12_head : (named_envelope_595_12.map Internal.SnakyRows010.namedCellKey).head? = some (2 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_12_last : (named_envelope_595_12.map Internal.SnakyRows010.namedCellKey).getLast? = some (125 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_10 : List Cell := Internal.SnakyRows010.named_envelope_595_11 ++ Internal.SnakyRows010.named_envelope_595_12
theorem Internal.SnakyRows010.named_envelope_595_10_chain : (named_envelope_595_10.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_11 Internal.SnakyRows010.named_envelope_595_12 (1 : ℤ) (2 : ℤ)
    Internal.SnakyRows010.named_envelope_595_11_chain Internal.SnakyRows010.named_envelope_595_12_chain Internal.SnakyRows010.named_envelope_595_11_last Internal.SnakyRows010.named_envelope_595_12_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_10_head : (named_envelope_595_10.map Internal.SnakyRows010.namedCellKey).head? = some (-123 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_11 Internal.SnakyRows010.named_envelope_595_12 (-123 : ℤ) Internal.SnakyRows010.named_envelope_595_11_head
theorem Internal.SnakyRows010.named_envelope_595_10_last : (named_envelope_595_10.map Internal.SnakyRows010.namedCellKey).getLast? = some (125 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_11 Internal.SnakyRows010.named_envelope_595_12 (125 : ℤ) Internal.SnakyRows010.named_envelope_595_12_last
def Internal.SnakyRows010.named_envelope_595_14 : List Cell := ([(1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_14_chain : (named_envelope_595_14.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_14_head : (named_envelope_595_14.map Internal.SnakyRows010.namedCellKey).head? = some (126 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_14_last : (named_envelope_595_14.map Internal.SnakyRows010.namedCellKey).getLast? = some (139 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_15 : List Cell := ([(2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_15_chain : (named_envelope_595_15.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_15_head : (named_envelope_595_15.map Internal.SnakyRows010.namedCellKey).head? = some (250 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_15_last : (named_envelope_595_15.map Internal.SnakyRows010.namedCellKey).getLast? = some (263 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_13 : List Cell := Internal.SnakyRows010.named_envelope_595_14 ++ Internal.SnakyRows010.named_envelope_595_15
theorem Internal.SnakyRows010.named_envelope_595_13_chain : (named_envelope_595_13.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_14 Internal.SnakyRows010.named_envelope_595_15 (139 : ℤ) (250 : ℤ)
    Internal.SnakyRows010.named_envelope_595_14_chain Internal.SnakyRows010.named_envelope_595_15_chain Internal.SnakyRows010.named_envelope_595_14_last Internal.SnakyRows010.named_envelope_595_15_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_13_head : (named_envelope_595_13.map Internal.SnakyRows010.namedCellKey).head? = some (126 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_14 Internal.SnakyRows010.named_envelope_595_15 (126 : ℤ) Internal.SnakyRows010.named_envelope_595_14_head
theorem Internal.SnakyRows010.named_envelope_595_13_last : (named_envelope_595_13.map Internal.SnakyRows010.namedCellKey).getLast? = some (263 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_14 Internal.SnakyRows010.named_envelope_595_15 (263 : ℤ) Internal.SnakyRows010.named_envelope_595_15_last
def Internal.SnakyRows010.named_envelope_595_9 : List Cell := Internal.SnakyRows010.named_envelope_595_10 ++ Internal.SnakyRows010.named_envelope_595_13
theorem Internal.SnakyRows010.named_envelope_595_9_chain : (named_envelope_595_9.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_10 Internal.SnakyRows010.named_envelope_595_13 (125 : ℤ) (126 : ℤ)
    Internal.SnakyRows010.named_envelope_595_10_chain Internal.SnakyRows010.named_envelope_595_13_chain Internal.SnakyRows010.named_envelope_595_10_last Internal.SnakyRows010.named_envelope_595_13_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_9_head : (named_envelope_595_9.map Internal.SnakyRows010.namedCellKey).head? = some (-123 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_10 Internal.SnakyRows010.named_envelope_595_13 (-123 : ℤ) Internal.SnakyRows010.named_envelope_595_10_head
theorem Internal.SnakyRows010.named_envelope_595_9_last : (named_envelope_595_9.map Internal.SnakyRows010.namedCellKey).getLast? = some (263 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_10 Internal.SnakyRows010.named_envelope_595_13 (263 : ℤ) Internal.SnakyRows010.named_envelope_595_13_last
def Internal.SnakyRows010.named_envelope_595_1 : List Cell := Internal.SnakyRows010.named_envelope_595_2 ++ Internal.SnakyRows010.named_envelope_595_9
theorem Internal.SnakyRows010.named_envelope_595_1_chain : (named_envelope_595_1.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_2 Internal.SnakyRows010.named_envelope_595_9 (-124 : ℤ) (-123 : ℤ)
    Internal.SnakyRows010.named_envelope_595_2_chain Internal.SnakyRows010.named_envelope_595_9_chain Internal.SnakyRows010.named_envelope_595_2_last Internal.SnakyRows010.named_envelope_595_9_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_1_last : (named_envelope_595_1.map Internal.SnakyRows010.namedCellKey).getLast? = some (263 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_2 Internal.SnakyRows010.named_envelope_595_9 (263 : ℤ) Internal.SnakyRows010.named_envelope_595_9_last
def Internal.SnakyRows010.named_envelope_595_19 : List Cell := ([(2, 8), (2, 9), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_19_chain : (named_envelope_595_19.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_19_head : (named_envelope_595_19.map Internal.SnakyRows010.namedCellKey).head? = some (264 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_19_last : (named_envelope_595_19.map Internal.SnakyRows010.namedCellKey).getLast? = some (389 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_20 : List Cell := ([(3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_20_chain : (named_envelope_595_20.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_20_head : (named_envelope_595_20.map Internal.SnakyRows010.namedCellKey).head? = some (390 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_20_last : (named_envelope_595_20.map Internal.SnakyRows010.namedCellKey).getLast? = some (514 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_18 : List Cell := Internal.SnakyRows010.named_envelope_595_19 ++ Internal.SnakyRows010.named_envelope_595_20
theorem Internal.SnakyRows010.named_envelope_595_18_chain : (named_envelope_595_18.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_19 Internal.SnakyRows010.named_envelope_595_20 (389 : ℤ) (390 : ℤ)
    Internal.SnakyRows010.named_envelope_595_19_chain Internal.SnakyRows010.named_envelope_595_20_chain Internal.SnakyRows010.named_envelope_595_19_last Internal.SnakyRows010.named_envelope_595_20_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_18_head : (named_envelope_595_18.map Internal.SnakyRows010.namedCellKey).head? = some (264 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_19 Internal.SnakyRows010.named_envelope_595_20 (264 : ℤ) Internal.SnakyRows010.named_envelope_595_19_head
theorem Internal.SnakyRows010.named_envelope_595_18_last : (named_envelope_595_18.map Internal.SnakyRows010.namedCellKey).getLast? = some (514 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_19 Internal.SnakyRows010.named_envelope_595_20 (514 : ℤ) Internal.SnakyRows010.named_envelope_595_20_last
def Internal.SnakyRows010.named_envelope_595_22 : List Cell := ([(4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_22_chain : (named_envelope_595_22.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_22_head : (named_envelope_595_22.map Internal.SnakyRows010.namedCellKey).head? = some (515 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_22_last : (named_envelope_595_22.map Internal.SnakyRows010.namedCellKey).getLast? = some (639 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_23 : List Cell := ([(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -6), (6, -5), (6, -4), (6, -3)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_23_chain : (named_envelope_595_23.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_23_head : (named_envelope_595_23.map Internal.SnakyRows010.namedCellKey).head? = some (640 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_23_last : (named_envelope_595_23.map Internal.SnakyRows010.namedCellKey).getLast? = some (765 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_21 : List Cell := Internal.SnakyRows010.named_envelope_595_22 ++ Internal.SnakyRows010.named_envelope_595_23
theorem Internal.SnakyRows010.named_envelope_595_21_chain : (named_envelope_595_21.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_22 Internal.SnakyRows010.named_envelope_595_23 (639 : ℤ) (640 : ℤ)
    Internal.SnakyRows010.named_envelope_595_22_chain Internal.SnakyRows010.named_envelope_595_23_chain Internal.SnakyRows010.named_envelope_595_22_last Internal.SnakyRows010.named_envelope_595_23_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_21_head : (named_envelope_595_21.map Internal.SnakyRows010.namedCellKey).head? = some (515 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_22 Internal.SnakyRows010.named_envelope_595_23 (515 : ℤ) Internal.SnakyRows010.named_envelope_595_22_head
theorem Internal.SnakyRows010.named_envelope_595_21_last : (named_envelope_595_21.map Internal.SnakyRows010.namedCellKey).getLast? = some (765 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_22 Internal.SnakyRows010.named_envelope_595_23 (765 : ℤ) Internal.SnakyRows010.named_envelope_595_23_last
def Internal.SnakyRows010.named_envelope_595_17 : List Cell := Internal.SnakyRows010.named_envelope_595_18 ++ Internal.SnakyRows010.named_envelope_595_21
theorem Internal.SnakyRows010.named_envelope_595_17_chain : (named_envelope_595_17.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_18 Internal.SnakyRows010.named_envelope_595_21 (514 : ℤ) (515 : ℤ)
    Internal.SnakyRows010.named_envelope_595_18_chain Internal.SnakyRows010.named_envelope_595_21_chain Internal.SnakyRows010.named_envelope_595_18_last Internal.SnakyRows010.named_envelope_595_21_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_17_head : (named_envelope_595_17.map Internal.SnakyRows010.namedCellKey).head? = some (264 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_18 Internal.SnakyRows010.named_envelope_595_21 (264 : ℤ) Internal.SnakyRows010.named_envelope_595_18_head
theorem Internal.SnakyRows010.named_envelope_595_17_last : (named_envelope_595_17.map Internal.SnakyRows010.namedCellKey).getLast? = some (765 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_18 Internal.SnakyRows010.named_envelope_595_21 (765 : ℤ) Internal.SnakyRows010.named_envelope_595_21_last
def Internal.SnakyRows010.named_envelope_595_26 : List Cell := ([(6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_26_chain : (named_envelope_595_26.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_26_head : (named_envelope_595_26.map Internal.SnakyRows010.namedCellKey).head? = some (766 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_26_last : (named_envelope_595_26.map Internal.SnakyRows010.namedCellKey).getLast? = some (892 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_27 : List Cell := ([(7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -5), (8, -4), (8, -3), (8, -2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_27_chain : (named_envelope_595_27.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_27_head : (named_envelope_595_27.map Internal.SnakyRows010.namedCellKey).head? = some (893 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_27_last : (named_envelope_595_27.map Internal.SnakyRows010.namedCellKey).getLast? = some (1022 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_25 : List Cell := Internal.SnakyRows010.named_envelope_595_26 ++ Internal.SnakyRows010.named_envelope_595_27
theorem Internal.SnakyRows010.named_envelope_595_25_chain : (named_envelope_595_25.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_26 Internal.SnakyRows010.named_envelope_595_27 (892 : ℤ) (893 : ℤ)
    Internal.SnakyRows010.named_envelope_595_26_chain Internal.SnakyRows010.named_envelope_595_27_chain Internal.SnakyRows010.named_envelope_595_26_last Internal.SnakyRows010.named_envelope_595_27_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_25_head : (named_envelope_595_25.map Internal.SnakyRows010.namedCellKey).head? = some (766 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_26 Internal.SnakyRows010.named_envelope_595_27 (766 : ℤ) Internal.SnakyRows010.named_envelope_595_26_head
theorem Internal.SnakyRows010.named_envelope_595_25_last : (named_envelope_595_25.map Internal.SnakyRows010.namedCellKey).getLast? = some (1022 : ℤ) :=
  Internal.SnakyRows010.named_last_append Internal.SnakyRows010.named_envelope_595_26 Internal.SnakyRows010.named_envelope_595_27 (1022 : ℤ) Internal.SnakyRows010.named_envelope_595_27_last
def Internal.SnakyRows010.named_envelope_595_29 : List Cell := ([(8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_29_chain : (named_envelope_595_29.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_29_head : (named_envelope_595_29.map Internal.SnakyRows010.namedCellKey).head? = some (1023 : ℤ) := by decide
theorem Internal.SnakyRows010.named_envelope_595_29_last : (named_envelope_595_29.map Internal.SnakyRows010.namedCellKey).getLast? = some (1154 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_30 : List Cell := ([(9, 3), (10, -5), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (11, -3), (11, -2), (11, -1), (12, -3), (12, -1)] : List Cell)
theorem Internal.SnakyRows010.named_envelope_595_30_chain : (named_envelope_595_30.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) := by decide
theorem Internal.SnakyRows010.named_envelope_595_30_head : (named_envelope_595_30.map Internal.SnakyRows010.namedCellKey).head? = some (1155 : ℤ) := by decide
def Internal.SnakyRows010.named_envelope_595_28 : List Cell := Internal.SnakyRows010.named_envelope_595_29 ++ Internal.SnakyRows010.named_envelope_595_30
theorem Internal.SnakyRows010.named_envelope_595_28_chain : (named_envelope_595_28.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_29 Internal.SnakyRows010.named_envelope_595_30 (1154 : ℤ) (1155 : ℤ)
    Internal.SnakyRows010.named_envelope_595_29_chain Internal.SnakyRows010.named_envelope_595_30_chain Internal.SnakyRows010.named_envelope_595_29_last Internal.SnakyRows010.named_envelope_595_30_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_28_head : (named_envelope_595_28.map Internal.SnakyRows010.namedCellKey).head? = some (1023 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_29 Internal.SnakyRows010.named_envelope_595_30 (1023 : ℤ) Internal.SnakyRows010.named_envelope_595_29_head
def Internal.SnakyRows010.named_envelope_595_24 : List Cell := Internal.SnakyRows010.named_envelope_595_25 ++ Internal.SnakyRows010.named_envelope_595_28
theorem Internal.SnakyRows010.named_envelope_595_24_chain : (named_envelope_595_24.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_25 Internal.SnakyRows010.named_envelope_595_28 (1022 : ℤ) (1023 : ℤ)
    Internal.SnakyRows010.named_envelope_595_25_chain Internal.SnakyRows010.named_envelope_595_28_chain Internal.SnakyRows010.named_envelope_595_25_last Internal.SnakyRows010.named_envelope_595_28_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_24_head : (named_envelope_595_24.map Internal.SnakyRows010.namedCellKey).head? = some (766 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_25 Internal.SnakyRows010.named_envelope_595_28 (766 : ℤ) Internal.SnakyRows010.named_envelope_595_25_head
def Internal.SnakyRows010.named_envelope_595_16 : List Cell := Internal.SnakyRows010.named_envelope_595_17 ++ Internal.SnakyRows010.named_envelope_595_24
theorem Internal.SnakyRows010.named_envelope_595_16_chain : (named_envelope_595_16.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_17 Internal.SnakyRows010.named_envelope_595_24 (765 : ℤ) (766 : ℤ)
    Internal.SnakyRows010.named_envelope_595_17_chain Internal.SnakyRows010.named_envelope_595_24_chain Internal.SnakyRows010.named_envelope_595_17_last Internal.SnakyRows010.named_envelope_595_24_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_16_head : (named_envelope_595_16.map Internal.SnakyRows010.namedCellKey).head? = some (264 : ℤ) :=
  Internal.SnakyRows010.named_head_append Internal.SnakyRows010.named_envelope_595_17 Internal.SnakyRows010.named_envelope_595_24 (264 : ℤ) Internal.SnakyRows010.named_envelope_595_17_head
def Internal.SnakyRows010.named_envelope_595_0 : List Cell := Internal.SnakyRows010.named_envelope_595_1 ++ Internal.SnakyRows010.named_envelope_595_16
theorem Internal.SnakyRows010.named_envelope_595_0_chain : (named_envelope_595_0.map Internal.SnakyRows010.namedCellKey).IsChain (· < ·) :=
  Internal.SnakyRows010.named_chain_append Internal.SnakyRows010.named_envelope_595_1 Internal.SnakyRows010.named_envelope_595_16 (263 : ℤ) (264 : ℤ)
    Internal.SnakyRows010.named_envelope_595_1_chain Internal.SnakyRows010.named_envelope_595_16_chain Internal.SnakyRows010.named_envelope_595_1_last Internal.SnakyRows010.named_envelope_595_16_head (by decide)
theorem Internal.SnakyRows010.named_envelope_595_nodup : (Internal.SnakyRows010.named_envelope_595_0 : Multiset Cell).Nodup :=
  Internal.SnakyRows010.named_nodup_of_chain Internal.SnakyRows010.named_envelope_595_0 Internal.SnakyRows010.named_envelope_595_0_chain
def envelope_595 : Finset Cell := ⟨(Internal.SnakyRows010.named_envelope_595_0 : Multiset Cell), Internal.SnakyRows010.named_envelope_595_nodup⟩
end SnakyConditional

end OAI
