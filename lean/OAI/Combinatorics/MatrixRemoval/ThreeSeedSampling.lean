import Mathlib

namespace OAI

/-!
# Three-seed sampling for the tree-matrix repair argument

Choices in different groups on the same axis need not be independent.
Three uniform seeds suffice: a common leaf, a row seed and a column seed.
The equal-fiber calculation gives uniform marginals.
-/

universe uX uY uZ

namespace Problem348.TreeSampling

/-- Replace the within-block coordinate of a leaf by that of a second seed. -/
def mix {a b : ℕ} (z u : Fin (a * b)) : Fin (a * b) :=
  finProdFinEquiv ((finProdFinEquiv.symm z).1,
    (finProdFinEquiv.symm u).2)

@[simp] theorem mix_div {a b : ℕ} (z u : Fin (a * b)) :
    (finProdFinEquiv.symm (mix z u)).1 =
      (finProdFinEquiv.symm z).1 := by
  simp [mix]

@[simp] theorem mix_mod {a b : ℕ} (z u : Fin (a * b)) :
    (finProdFinEquiv.symm (mix z u)).2 =
      (finProdFinEquiv.symm u).2 := by
  simp [mix]

/-- The output of the mixer and the two unused coordinates determine both seeds. -/
def splitMix {a b : ℕ} :
    (Fin (a * b) × Fin (a * b)) ≃
      (Fin (a * b) × (Fin b × Fin a)) where
  toFun p := (mix p.1 p.2,
    ((finProdFinEquiv.symm p.1).2, (finProdFinEquiv.symm p.2).1))
  invFun p :=
    (finProdFinEquiv ((finProdFinEquiv.symm p.1).1, p.2.1),
      finProdFinEquiv (p.2.2, (finProdFinEquiv.symm p.1).2))
  left_inv p := by
    rcases p with ⟨z,u⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply z)
      (finProdFinEquiv.apply_symm_apply u)
  right_inv p := by
    rcases p with ⟨x,r,s⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply x) rfl

/-- A first-coordinate fiber of a product decomposition is the second factor. -/
def fiberOfEquiv {X : Type uX} {Y : Type uY} {Z : Type uZ} (e : X ≃ Y × Z) (y : Y) :
    {x : X // (e x).1 = y} ≃ Z where
  toFun x := (e x.1).2
  invFun z := ⟨e.symm (y, z), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext x.property.symm rfl
  right_inv z := by simp

/-- Every level-class position occurs equally often in the pair of seeds. -/
theorem card_mix_fiber {a b : ℕ} (x : Fin (a * b)) :
    Fintype.card {p : Fin (a * b) × Fin (a * b) // mix p.1 p.2 = x} =
      a * b := by
  classical
  calc
    _ = Fintype.card (Fin b × Fin a) :=
      Fintype.card_congr (fiberOfEquiv (splitMix (a := a) (b := b)) x)
    _ = _ := by simp [Nat.mul_comm]

/-- The three seeds are the common leaf, an axis-one seed and an axis-two seed. -/
abbrev Seeds (m : ℕ) := Fin m × (Fin m × Fin m)

/-- A variable row and an anchor/dummy column, together with unused coordinates. -/
def splitRow {a b : ℕ} :
    Seeds (a * b) ≃ (Fin (a * b) × Fin (a * b)) × (Fin b × Fin a) where
  toFun s := ((mix s.1 s.2.1, s.2.2),
    ((finProdFinEquiv.symm s.1).2, (finProdFinEquiv.symm s.2.1).1))
  invFun p := (finProdFinEquiv ((finProdFinEquiv.symm p.1.1).1, p.2.1),
    (finProdFinEquiv (p.2.2, (finProdFinEquiv.symm p.1.1).2), p.1.2))
  left_inv s := by
    rcases s with ⟨z,u,v⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply z)
      (Prod.ext (finProdFinEquiv.apply_symm_apply u) rfl)
  right_inv p := by
    rcases p with ⟨⟨x,y⟩,r,t⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (Prod.ext (finProdFinEquiv.apply_symm_apply x) rfl) rfl

/-- An anchor/dummy row and a variable column, with the unused coordinates. -/
def splitColumn {a b : ℕ} :
    Seeds (a * b) ≃ (Fin (a * b) × Fin (a * b)) × (Fin b × Fin a) where
  toFun s := ((s.2.1, mix s.1 s.2.2),
    ((finProdFinEquiv.symm s.1).2, (finProdFinEquiv.symm s.2.2).1))
  invFun p := (finProdFinEquiv ((finProdFinEquiv.symm p.1.2).1, p.2.1),
    (p.1.1, finProdFinEquiv (p.2.2, (finProdFinEquiv.symm p.1.2).2)))
  left_inv s := by
    rcases s with ⟨z,u,v⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply z)
      (Prod.ext rfl (finProdFinEquiv.apply_symm_apply v))
  right_inv p := by
    rcases p with ⟨⟨x,y⟩,r,t⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (Prod.ext rfl (finProdFinEquiv.apply_symm_apply y)) rfl

/-- Two independent axis seeds, with the common-leaf coordinate unused. -/
def splitBoth {m : ℕ} : Seeds m ≃ (Fin m × Fin m) × Fin m where
  toFun s := (s.2, s.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact protected-cell multiplicity when the row is variable. -/
theorem card_row_fiber {a b : ℕ} (x y : Fin (a * b)) :
    Fintype.card {s : Seeds (a * b) // (mix s.1 s.2.1, s.2.2) = (x,y)} =
      a * b := by
  classical
  calc
    _ = Fintype.card (Fin b × Fin a) :=
      Fintype.card_congr (fiberOfEquiv (splitRow (a := a) (b := b)) (x,y))
    _ = _ := by simp [Nat.mul_comm]

/-- Exact protected-cell multiplicity when the column is variable. -/
theorem card_column_fiber {a b : ℕ} (x y : Fin (a * b)) :
    Fintype.card {s : Seeds (a * b) // (s.2.1, mix s.1 s.2.2) = (x,y)} =
      a * b := by
  classical
  calc
    _ = Fintype.card (Fin b × Fin a) :=
      Fintype.card_congr (fiberOfEquiv (splitColumn (a := a) (b := b)) (x,y))
    _ = _ := by simp [Nat.mul_comm]

/-- Exact multiplicity for two anchor/dummy positions or two root positions. -/
theorem card_both_fiber {m : ℕ} (x y : Fin m) :
    Fintype.card {s : Seeds m // s.2 = (x,y)} = m := by
  classical
  calc
    _ = Fintype.card (Fin m) :=
      Fintype.card_congr (fiberOfEquiv (splitBoth (m := m)) (x,y))
    _ = _ := Fintype.card_fin m

@[simp] theorem card_seeds (m : ℕ) : Fintype.card (Seeds m) = m ^ 3 := by
  simp [Seeds, pow_succ, Nat.mul_assoc]

@[simp] theorem mix_val {a b : ℕ} (z u : Fin (a * b)) :
    (mix z u).val = u.val % b + b * (z.val / b) := rfl

/-- The two coordinates of a depth-i level class multiply to the leaf count. -/
theorem level_factor {h i : ℕ} (hi : i ≤ h) :
    2 ^ i * 2 ^ (h-i) = 2 ^ h := by
  rw [← pow_add, Nat.add_sub_of_le hi]

/-- Transport the mixer to a size presented by an equality rather than a product. -/
def mixCast {a b m : ℕ} (hm : a * b = m) (z u : Fin m) : Fin m :=
  Fin.cast hm (mix (Fin.cast hm.symm z) (Fin.cast hm.symm u))

@[simp] theorem card_mixCast_row_fiber {a b m : ℕ} (hm : a*b=m) (x y : Fin m) :
    Fintype.card {s : Seeds m // (mixCast hm s.1 s.2.1, s.2.2) = (x,y)} = m := by
  subst m
  exact card_row_fiber x y

@[simp] theorem card_mixCast_column_fiber {a b m : ℕ} (hm : a*b=m) (x y : Fin m) :
    Fintype.card {s : Seeds m // (s.2.1, mixCast hm s.1 s.2.2) = (x,y)} = m := by
  subst m
  exact card_column_fiber x y

/-- The class-coordinate selected at depth i by a common leaf and an axis seed. -/
def atLevel (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) : Fin (2 ^ h) :=
  mixCast (level_factor hi) z u

@[simp] theorem atLevel_val (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    (atLevel h i hi z u).val =
      u.val % (2 ^ (h-i)) + (2 ^ (h-i)) * (z.val / (2 ^ (h-i))) := rfl

/-- Root selections depend only on the corresponding axis seed. -/
@[simp] theorem atLevel_root (h : ℕ) (z u : Fin (2 ^ h)) :
    atLevel h 0 (Nat.zero_le h) z u = u := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt u.isLt, Nat.div_eq_of_lt z.isLt]

/-- Both signs at the leaf select the same common leaf, regardless of axis seed. -/
@[simp] theorem atLevel_leaf (h : ℕ) (z u : Fin (2 ^ h)) :
    atLevel h h le_rfl z u = z := by
  apply Fin.ext
  simp [Nat.mod_one]

/-- Every selected position lies in the ancestor block of the common leaf. -/
theorem atLevel_node (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    (atLevel h i hi z u).val / (2 ^ (h-i)) = z.val / (2 ^ (h-i)) := by
  rw [atLevel_val, Nat.add_mul_div_left _ _ (by positivity)]
  rw [Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), Nat.zero_add]

/-- The sampler's node at a child level has the prescribed parent. -/
theorem ancestor_parent (h i z : ℕ) (hi : i < h) :
    (z / 2 ^ (h - (i+1))) / 2 = z / 2 ^ (h-i) := by
  rw [Nat.div_div_eq_div_mul]
  congr 1
  have he : h-i = (h-(i+1))+1 := by omega
  rw [he, pow_succ]

/-- Every variable-row / anchor-column cell has exactly m seed preimages. -/
theorem card_atLevel_row_fiber (h i : ℕ) (hi : i ≤ h) (x y : Fin (2^h)) :
    Fintype.card {s : Seeds (2^h) //
      (atLevel h i hi s.1 s.2.1, s.2.2) = (x,y)} = 2^h :=
  card_mixCast_row_fiber (level_factor hi) x y

/-- Every anchor-row / variable-column cell has exactly m seed preimages. -/
theorem card_atLevel_column_fiber (h i : ℕ) (hi : i ≤ h) (x y : Fin (2^h)) :
    Fintype.card {s : Seeds (2^h) //
      (s.2.1, atLevel h i hi s.1 s.2.2) = (x,y)} = 2^h :=
  card_mixCast_column_fiber (level_factor hi) x y

end Problem348.TreeSampling

end OAI
