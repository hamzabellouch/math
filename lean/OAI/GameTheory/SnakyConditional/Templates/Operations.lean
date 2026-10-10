import OAI.GameTheory.SnakyConditional.Semantics.Foundation

namespace OAI

namespace SnakyConditional
def placedSet (r : Fin 8) (t : Cell) (A : Finset Cell) : Finset Cell :=
  A.map (placementEquiv r t).toEmbedding
theorem placedSet_eq_image (r : Fin 8) (t : Cell) (A : Finset Cell) :
    placedSet r t A = A.image (placement r t) := by
  rw [placedSet, Finset.map_eq_image]
  rfl
theorem placed_template_map {n : ℕ} {A H : Finset Cell}
    (h : Template HasSnaky n A H) (r : Fin 8) (t : Cell) :
    Template HasSnaky n (placedSet r t A) (placedSet r t H) := by
  simpa only [placedSet_eq_image] using placed_template h r t
def commonEnvelope {r : ℕ} (D : Fin (r + 1) → Finset Cell) : Finset Cell :=
  (D 0).filter (fun b => ∀ j, b ∈ D j)
theorem mem_commonEnvelope {r : ℕ} (D : Fin (r + 1) → Finset Cell)
    (b : Cell) (hb : ∀ j, b ∈ D j) : b ∈ commonEnvelope D :=
  Finset.mem_filter.mpr ⟨hb 0, hb⟩
def Internal.SnakyRows008.cf17CellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows008.cf17_multiset_nodup_of_key_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows008.cf17CellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows008.cf17CellKey h.pairwise.nodup)
theorem Internal.SnakyRows008.cf17_key_chain_append (xs ys : List Cell)
    (hx : (xs.map Internal.SnakyRows008.cf17CellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows008.cf17CellKey).IsChain (· < ·))
    (hxy : ∀ x ∈ (xs.map Internal.SnakyRows008.cf17CellKey).getLast?,
      ∀ y ∈ (ys.map Internal.SnakyRows008.cf17CellKey).head?, x < y) :
    ((xs ++ ys).map Internal.SnakyRows008.cf17CellKey).IsChain (· < ·) := by
  rw [List.map_append]
  exact hx.append hy hxy
def Internal.SnakyRows009.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows009.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows009.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows009.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows009.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows009.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows009.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows009.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows009.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows009.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows009.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows009.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows009.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows009.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011A.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011A.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011A.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011A.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011A.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011A.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011A.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011A.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011A.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011A.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011A.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011A.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011A.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011B.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011B.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011B.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011B.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011B.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011B.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011B.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011B.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011B.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011B.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011B.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011B.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011B.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011C.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011C.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011C.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011C.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011C.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011C.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011C.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011C.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011C.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011C.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011C.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011C.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011C.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011D.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011D.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011D.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011D.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011D.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011D.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011D.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011D.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011D.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011D.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011D.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011D.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011D.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011E.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011E.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011E.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011E.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011E.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011E.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011E.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011E.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011E.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011E.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011E.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011E.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011E.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011F.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011F.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011F.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011F.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011F.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011F.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011F.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011F.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011F.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011F.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011F.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011F.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011F.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011G.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011G.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011G.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011G.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011G.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011G.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011G.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011G.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011G.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011G.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011G.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011G.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011G.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011I.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011I.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011I.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011I.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011I.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011I.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011I.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011I.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011I.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011I.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011I.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011I.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011I.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows011.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows011.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows011.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows011.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows011.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows011.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows011.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows011.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows011.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows011.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows011.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows011.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows011.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows011.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows012A.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows012A.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows012A.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows012A.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows012A.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows012A.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows012A.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows012A.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows012A.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows012A.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows012A.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows012A.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows012A.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows012B.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows012B.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows012B.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows012B.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows012B.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows012B.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows012B.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows012B.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows012B.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows012B.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows012B.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows012B.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows012B.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
def Internal.SnakyRows012C.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows012C.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows012C.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows012C.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows012C.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows012C.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows012C.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows012C.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows012C.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows012C.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows012C.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows012C.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows012C.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows012C.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows012C.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows012C.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows012C.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
def Internal.SnakyRows012D.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows012D.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows012D.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows012D.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows012D.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows012D.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows012D.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows012D.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows012D.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows012D.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows012D.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows012D.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows012D.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows012D.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
def Internal.SnakyRows012.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows012.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows012.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows012.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows012.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows012.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows012.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows012.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows012.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows012.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows012.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows012.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows012.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows012.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows012.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
def Internal.SnakyRows013.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows013.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows013.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows013.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows013.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows013.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows013.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows013.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows013.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows013.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows013.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows013.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows013.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows013.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows013.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
def Internal.SnakyRows014.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows014.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows014.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows014.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows014.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows014.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows014.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows014.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows014.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows014.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows014.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows014.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows014.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows014.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows014.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
def Internal.SnakyRows015.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows015.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows015.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows015.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows015.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows015.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows015.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows015.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows015.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows015.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows015.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows015.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows015.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows015.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows015.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows015.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows015.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
def Internal.SnakyRows016.namedCellKey (p : Cell) : ℤ := 128 * p.1 + p.2
theorem Internal.SnakyRows016.named_nodup_of_chain (xs : List Cell)
    (h : (xs.map Internal.SnakyRows016.namedCellKey).IsChain (· < ·)) : (xs : Multiset Cell).Nodup :=
  Multiset.coe_nodup.mpr (List.Nodup.of_map Internal.SnakyRows016.namedCellKey h.pairwise.nodup)
theorem Internal.SnakyRows016.named_chain_append (xs ys : List Cell) (a b : ℤ)
    (hx : (xs.map Internal.SnakyRows016.namedCellKey).IsChain (· < ·))
    (hy : (ys.map Internal.SnakyRows016.namedCellKey).IsChain (· < ·))
    (hlast : (xs.map Internal.SnakyRows016.namedCellKey).getLast? = some a)
    (hhead : (ys.map Internal.SnakyRows016.namedCellKey).head? = some b) (hab : a < b) :
    ((xs ++ ys).map Internal.SnakyRows016.namedCellKey).IsChain (· < ·) := by
  rw [List.map_append]
  apply hx.append hy
  intro x hx' y hy'
  have hax : a = x := by simpa only [hlast, Option.mem_some] using hx'
  have hby : b = y := by simpa only [hhead, Option.mem_some] using hy'
  subst x
  subst y
  exact hab
theorem Internal.SnakyRows016.named_head_append (xs ys : List Cell) (a : ℤ)
    (h : (xs.map Internal.SnakyRows016.namedCellKey).head? = some a) :
    ((xs ++ ys).map Internal.SnakyRows016.namedCellKey).head? = some a := by
  rw [List.map_append, List.head?_append, h]
  rfl
theorem Internal.SnakyRows016.named_last_append (xs ys : List Cell) (b : ℤ)
    (h : (ys.map Internal.SnakyRows016.namedCellKey).getLast? = some b) :
    ((xs ++ ys).map Internal.SnakyRows016.namedCellKey).getLast? = some b := by
  rw [List.map_append, List.getLast?_append, h]
  rfl
theorem Internal.SnakyRows016.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
theorem Internal.SnakyRows017.placedSet_subset_of_points {A H : Finset Cell}
    (r : Fin 8) (t : Cell)
    (h : ∀ p ∈ A, placement r t p ∈ H) : placedSet r t A ⊆ H := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  rw [← hpq]
  exact h p hp
end SnakyConditional

end OAI
