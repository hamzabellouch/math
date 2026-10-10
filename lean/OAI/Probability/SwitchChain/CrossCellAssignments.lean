import OAI.Probability.SwitchChain.CrossCellMoments

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCellAssignments

attribute [local instance] Classical.propDecidable

variable {O P : Type*} [Fintype O] [Fintype P]

abbrev Marginal (A : Finset O) (q : ℕ) :=
  {z : Fin 3 × Finset O // z.2 ⊆ A ∧ z.2.card + z.1.val = q}

instance marginalFintype (A : Finset O) (q : ℕ) : Fintype (Marginal A q) :=
  Fintype.ofFinite _

def margin {A : Finset O} {q : ℕ} (x : Marginal A q) : Fin 3 := x.val.1

def assignment {A : Finset O} {q : ℕ} (x : Marginal A q) : Finset O := x.val.2

abbrev Coordinates (A : Finset O) (B : Finset P) (q₀ q₁ s : ℕ) :=
  {z : CrossBlock.Matrix × Finset O × Finset P //
    z.2.1 ⊆ A ∧ z.2.2 ⊆ B ∧ CrossBlock.total z.1 = s ∧
      z.2.1.card + CrossBlock.row z.1 0 = q₀ ∧
      z.2.2.card + CrossBlock.col z.1 0 = q₁}

instance coordinatesFintype (A : Finset O) (B : Finset P) (q₀ q₁ s : ℕ) :
    Fintype (Coordinates A B q₀ q₁ s) := Fintype.ofFinite _

def rowFin (M : CrossBlock.Matrix) : Fin 3 :=
  ⟨CrossBlock.row M 0, Nat.lt_succ_of_le (CrossBlock.row_le_two M 0)⟩

def colFin (M : CrossBlock.Matrix) : Fin 3 :=
  ⟨CrossBlock.col M 0, Nat.lt_succ_of_le (CrossBlock.col_le_two M 0)⟩

def encode {A : Finset O} {B : Finset P} {q₀ q₁ s : ℕ}
    (z : Coordinates A B q₀ q₁ s) :
    CrossCellMoments.Cell s (@margin O A q₀) (@margin P B q₁) :=
  ⟨(z.val.1,
    ⟨(rowFin z.val.1, z.val.2.1), z.property.1, z.property.2.2.2.1⟩,
    ⟨(colFin z.val.1, z.val.2.2), z.property.2.1, z.property.2.2.2.2⟩),
    z.property.2.2.1, rfl, rfl⟩

def decode {A : Finset O} {B : Finset P} {q₀ q₁ s : ℕ}
    (z : CrossCellMoments.Cell s (@margin O A q₀) (@margin P B q₁)) :
    Coordinates A B q₀ q₁ s :=
  ⟨(z.val.1, assignment z.val.2.1, assignment z.val.2.2),
    z.val.2.1.property.1, z.val.2.2.property.1, z.property.1,
    by simpa only [z.property.2.1, assignment, margin] using z.val.2.1.property.2,
    by simpa only [z.property.2.2, assignment, margin] using z.val.2.2.property.2⟩

def coordinatesEquiv (A : Finset O) (B : Finset P) (q₀ q₁ s : ℕ) :
    Coordinates A B q₀ q₁ s ≃
      CrossCellMoments.Cell s (@margin O A q₀) (@margin P B q₁) where
  toFun := encode
  invFun := decode
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        exact z.property.2.1
      · rfl
    · apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        exact z.property.2.2
      · rfl

theorem sum_coordinates (A : Finset O) (B : Finset P) (q₀ q₁ s : ℕ)
    (F : Marginal A q₀ → Marginal B q₁ → ℝ) :
    (∑ z : Coordinates A B q₀ q₁ s, F (encode z).val.2.1 (encode z).val.2.2) =
      ∑ x, ∑ y, (CrossBlock.count s (margin x) (margin y) : ℝ) * F x y := by
  have h := Equiv.sum_comp (coordinatesEquiv A B q₀ q₁ s)
    (fun z => F z.val.2.1 z.val.2.2)
  change (∑ z : Coordinates A B q₀ q₁ s, F (encode z).val.2.1 (encode z).val.2.2) = _ at h
  rw [h]
  exact CrossCellMoments.sum_cell s _ _ F

theorem card_coordinates_two (A : Finset O) (B : Finset P) (q₀ q₁ : ℕ) :
    (Fintype.card (Coordinates A B q₀ q₁ 2) : ℝ) =
      CrossCovariance.mass (fun _ : Marginal A q₀ => 1)
        (fun _ : Marginal B q₁ => 1)
        (CrossCellMoments.offCenter margin) (CrossCellMoments.offCenter margin) := by
  rw [Fintype.card_congr (coordinatesEquiv A B q₀ q₁ 2)]
  exact CrossCellMoments.card_cell_two _ _

theorem average_coordinates_two_product (A : Finset O) (B : Finset P) (q₀ q₁ : ℕ)
    (f : Marginal A q₀ → ℝ) (g : Marginal B q₁ → ℝ) :
    (∑ z : Coordinates A B q₀ q₁ 2,
      f (encode z).val.2.1 * g (encode z).val.2.2) /
        (Fintype.card (Coordinates A B q₀ q₁ 2) : ℝ) =
      CrossCovariance.jointAverage (fun _ : Marginal A q₀ => 1)
        (fun _ : Marginal B q₁ => 1)
        (CrossCellMoments.offCenter margin) (CrossCellMoments.offCenter margin) f g := by
  have h := Equiv.sum_comp (coordinatesEquiv A B q₀ q₁ 2)
    (fun z => f z.val.2.1 * g z.val.2.2)
  change (∑ z : Coordinates A B q₀ q₁ 2,
    f (encode z).val.2.1 * g (encode z).val.2.2) = _ at h
  rw [h, Fintype.card_congr (coordinatesEquiv A B q₀ q₁ 2)]
  exact CrossCellMoments.average_product_eq _ _ f g

end Problem315.CrossCellAssignments

end

end OAI
