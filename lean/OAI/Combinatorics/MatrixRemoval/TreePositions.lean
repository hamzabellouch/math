import Mathlib

namespace OAI

/-!
Concrete depth-first orders for variable positions.
Each class has 2^h positions. Classes 2*i and 2*i+1 are respectively
plus and minus at i<h; class 2*h is the shared leaf class.
The final two key components retain the original coordinates, making
injectivity immediate without uniqueness assumptions on dyadic data.
-/

namespace Problem348.TreePositions

abbrev VariablePosition (h : ℕ) := Fin (2 * h + 1) × Fin (2 ^ h)
abbrev OrderKey := ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ

def key (endpoint phase tie cls coordinate : ℕ) : OrderKey :=
  toLex (endpoint, toLex (phase, toLex (tie, toLex (cls, coordinate))))

def earlyKey (depth blockSize node cls coordinate : ℕ) : OrderKey :=
  key (2 * node * blockSize) 1 depth cls coordinate

def lateKey (remaining blockSize node cls coordinate : ℕ) : OrderKey :=
  key (2 * (node + 1) * blockSize) 0 remaining cls coordinate

def leafKey (h coordinate : ℕ) : OrderKey :=
  key (2 * coordinate + 1) 2 0 (2 * h) coordinate

/-- `column = false` gives row order; `true` reverses the signs. -/
def orderKey (column : Bool) (h : ℕ) (p : VariablePosition h) : OrderKey :=
  if p.1.val = 2 * h then leafKey h p.2.val
  else
    let depth := p.1.val / 2
    let size := 2 ^ (h - depth)
    let node := p.2.val / size
    if p.1.val % 2 = (if column then 0 else 1) then
      earlyKey depth size node p.1.val p.2.val
    else
      lateKey (h - depth) size node p.1.val p.2.val

abbrev rowKey (h : ℕ) := orderKey false h
abbrev columnKey (h : ℕ) := orderKey true h

def keyClass (k : OrderKey) : ℕ := (ofLex (ofLex (ofLex (ofLex k).2).2).2).1
def keyCoordinate (k : OrderKey) : ℕ := (ofLex (ofLex (ofLex (ofLex k).2).2).2).2

@[simp] theorem keyClass_key (a b c d e : ℕ) : keyClass (key a b c d e) = d := rfl
@[simp] theorem keyCoordinate_key (a b c d e : ℕ) :
    keyCoordinate (key a b c d e) = e := rfl

@[simp] theorem keyClass_orderKey (column : Bool) (h : ℕ) (p : VariablePosition h) :
    keyClass (orderKey column h p) = p.1.val := by
  simp only [orderKey]
  split_ifs <;> simp_all [leafKey, earlyKey, lateKey]

@[simp] theorem keyCoordinate_orderKey (column : Bool) (h : ℕ)
    (p : VariablePosition h) : keyCoordinate (orderKey column h p) = p.2.val := by
  simp only [orderKey]
  split_ifs <;> rfl

theorem orderKey_injective (column : Bool) (h : ℕ) :
    Function.Injective (orderKey column h) := by
  intro p q hpq
  apply Prod.ext
  · apply Fin.ext
    simpa using congrArg keyClass hpq
  · apply Fin.ext
    simpa using congrArg keyCoordinate hpq

/-- Explicit order structures, not global instances: the same raw positions
carry different row and column orders. -/
abbrev positionOrder (column : Bool) (h : ℕ) : LinearOrder (VariablePosition h) :=
  LinearOrder.lift' (orderKey column h) (orderKey_injective column h)

@[simp] theorem card_variablePosition (h : ℕ) :
    Fintype.card (VariablePosition h) = (2 * h + 1) * 2 ^ h := by
  simp [VariablePosition]

end Problem348.TreePositions

namespace Problem348.TreePositions

theorem key_lt_iff_endpoint_le_of_tie_lt
    (a b phase t u cls₁ cls₂ x y : ℕ) (htu : t < u) :
    key a phase t cls₁ x < key b phase u cls₂ y ↔ a ≤ b := by
  simp [key, Prod.Lex.lt_iff, htu, ne_of_lt htu, le_iff_lt_or_eq]

theorem lateKey_child_lt_parent (b r p a cls₁ cls₂ x y : ℕ) (hb : 0 < b) :
    lateKey r b p cls₁ x < lateKey (r + 1) (2 * b) a cls₂ y ↔ p / 2 ≤ a := by
  rw [lateKey, lateKey, key_lt_iff_endpoint_le_of_tie_lt _ _ _ _ _ _ _ _ _
    (Nat.lt_succ_self r)]
  have heq : 2 * (a + 1) * (2 * b) = (2 * (2 * a + 2)) * b := by ring
  rw [heq, mul_le_mul_iff_left₀ hb]
  omega

theorem earlyKey_parent_lt_child (b i p a cls₁ cls₂ x y : ℕ) (hb : 0 < b) :
    earlyKey i (2 * b) a cls₁ x < earlyKey (i + 1) b p cls₂ y ↔ a ≤ p / 2 := by
  rw [earlyKey, earlyKey, key_lt_iff_endpoint_le_of_tie_lt _ _ _ _ _ _ _ _ _
    (Nat.lt_succ_self i)]
  have heq : 2 * a * (2 * b) = (4 * a) * b := by ring
  rw [heq, mul_le_mul_iff_left₀ hb]
  omega

end Problem348.TreePositions

namespace Problem348.TreePositions

theorem leafKey_lt_lateKey_parent (h r p a cls y : ℕ) :
    leafKey h p < lateKey r 2 a cls y ↔ p / 2 ≤ a := by
  simp [leafKey, lateKey, key, Prod.Lex.lt_iff]
  omega

theorem earlyKey_parent_lt_leafKey (h i p a cls x : ℕ) :
    earlyKey i 2 a cls x < leafKey h p ↔ a ≤ p / 2 := by
  simp only [earlyKey, leafKey, key, Prod.Lex.lt_iff, ofLex_toLex,
    ]
  omega

/-- The plus class; at depth h this is the shared leaf class. -/
def plusPos {h : ℕ} (i : ℕ) (hi : i ≤ h) (x : Fin (2 ^ h)) : VariablePosition h :=
  (⟨2 * i, by omega⟩, x)

/-- The minus class, identified with the plus class exactly at the leaf. -/
def minusPos {h : ℕ} (i : ℕ) (hi : i ≤ h) (x : Fin (2 ^ h)) : VariablePosition h :=
  (⟨if i = h then 2 * h else 2 * i + 1, by split_ifs <;> omega⟩, x)

def node {h : ℕ} (i : ℕ) (x : Fin (2 ^ h)) : ℕ := x.val / 2 ^ (h - i)

@[simp] theorem minusPos_leaf (h : ℕ) (x : Fin (2 ^ h)) :
    minusPos h le_rfl x = plusPos h le_rfl x := by
  simp [minusPos, plusPos]

@[simp] theorem orderKey_leaf (column : Bool) (h : ℕ) (x : Fin (2 ^ h)) :
    orderKey column h (plusPos h le_rfl x) = leafKey h x.val := by
  simp [orderKey, plusPos]

@[simp] theorem rowKey_leaf (h : ℕ) (x : Fin (2 ^ h)) :
    rowKey h (plusPos h le_rfl x) = leafKey h x.val :=
  orderKey_leaf false h x

@[simp] theorem columnKey_leaf (h : ℕ) (x : Fin (2 ^ h)) :
    columnKey h (plusPos h le_rfl x) = leafKey h x.val :=
  orderKey_leaf true h x

theorem rowKey_plus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    rowKey h (plusPos i (Nat.le_of_lt hi) x) =
      lateKey (h - i) (2 ^ (h - i)) (node i x) (2 * i) x.val := by
  have hh : 2 * i ≠ 2 * h := by omega
  simp [rowKey, orderKey, plusPos, hh, node]

theorem columnKey_plus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    columnKey h (plusPos i (Nat.le_of_lt hi) x) =
      earlyKey i (2 ^ (h - i)) (node i x) (2 * i) x.val := by
  have hh : 2 * i ≠ 2 * h := by omega
  simp [columnKey, orderKey, plusPos, hh, node]

theorem rowKey_minus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    rowKey h (minusPos i (Nat.le_of_lt hi) x) =
      earlyKey i (2 ^ (h - i)) (node i x) (2 * i + 1) x.val := by
  have hh : 2 * i + 1 ≠ 2 * h := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [rowKey, orderKey, minusPos, hh, hd, Nat.ne_of_lt hi, node]

theorem columnKey_minus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    columnKey h (minusPos i (Nat.le_of_lt hi) x) =
      lateKey (h - i) (2 ^ (h - i)) (node i x) (2 * i + 1) x.val := by
  have hh : 2 * i + 1 ≠ 2 * h := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [columnKey, orderKey, minusPos, hh, hd, Nat.ne_of_lt hi, node]

end Problem348.TreePositions

namespace Problem348.TreePositions

/-- The plus row-order equivalence, including shared leaves. -/
theorem row_plus_child_lt_parent {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    rowKey h (plusPos (i + 1) (by omega) x) <
        rowKey h (plusPos i (Nat.le_of_lt hi) y) ↔
      node (i + 1) x / 2 ≤ node i y := by
  by_cases he : i + 1 = h
  · subst h
    rw [rowKey_leaf, rowKey_plus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using leafKey_lt_lateKey_parent (i + 1) 1 x.val
      (node i y) (2 * i) y.val
  · have hic : i + 1 < h := by omega
    rw [rowKey_plus_internal hic, rowKey_plus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb, hr]
    exact lateKey_child_lt_parent _ _ _ _ _ _ _ _ (by positivity)

/-- The minus row-order equivalence, including shared leaves. -/
theorem row_minus_parent_lt_child {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    rowKey h (minusPos i (Nat.le_of_lt hi) y) <
        rowKey h (minusPos (i + 1) (by omega) x) ↔
      node i y ≤ node (i + 1) x / 2 := by
  by_cases he : i + 1 = h
  · subst h
    rw [minusPos_leaf, rowKey_leaf, rowKey_minus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using earlyKey_parent_lt_leafKey (i + 1) i x.val
      (node i y) (2 * i + 1) y.val
  · have hic : i + 1 < h := by omega
    rw [rowKey_minus_internal hic, rowKey_minus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb]
    exact earlyKey_parent_lt_child _ _ _ _ _ _ _ _ (by positivity)

/-- The plus column-order equivalence, including shared leaves. -/
theorem column_plus_parent_lt_child {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    columnKey h (plusPos i (Nat.le_of_lt hi) y) <
        columnKey h (plusPos (i + 1) (by omega) x) ↔
      node i y ≤ node (i + 1) x / 2 := by
  by_cases he : i + 1 = h
  · subst h
    rw [columnKey_leaf, columnKey_plus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using earlyKey_parent_lt_leafKey (i + 1) i x.val
      (node i y) (2 * i) y.val
  · have hic : i + 1 < h := by omega
    rw [columnKey_plus_internal hic, columnKey_plus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb]
    exact earlyKey_parent_lt_child _ _ _ _ _ _ _ _ (by positivity)

/-- The minus column-order equivalence, including shared leaves. -/
theorem column_minus_child_lt_parent {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    columnKey h (minusPos (i + 1) (by omega) x) <
        columnKey h (minusPos i (Nat.le_of_lt hi) y) ↔
      node (i + 1) x / 2 ≤ node i y := by
  by_cases he : i + 1 = h
  · subst h
    rw [minusPos_leaf, columnKey_leaf, columnKey_minus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using leafKey_lt_lateKey_parent (i + 1) 1 x.val
      (node i y) (2 * i + 1) y.val
  · have hic : i + 1 < h := by omega
    rw [columnKey_minus_internal hic, columnKey_minus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb, hr]
    exact lateKey_child_lt_parent _ _ _ _ _ _ _ _ (by positivity)

end Problem348.TreePositions

end OAI
