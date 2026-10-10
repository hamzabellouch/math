import OAI.Combinatorics.ContingencyTables.Transport.SignedMarginTranslation

namespace OAI

/-! # Accepted completion translations are exact finite bijections -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def Accepted (R : I → ℕ) (P : J → ℕ) (D : I → J → ℤ) :=
  {X : Table R P // ∀ i j,0 ≤ (X.val i j:ℤ)+D i j}

noncomputable instance acceptedFintype (R : I → ℕ) (P : J → ℕ) (D : I → J → ℤ) :
    Fintype (Accepted R P D) := by
  unfold Accepted
  classical
  infer_instance

def translate (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) : Table R₁ P₁ := by
  refine ⟨fun i j => ((X.val.val i j:ℤ)+D i j).toNat,?_,?_⟩
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [Int.toNat_of_nonneg (X.property _ _)]
    rw [Finset.sum_add_distrib,← Nat.cast_sum,X.val.property.1,hR]
    ring
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [Int.toNat_of_nonneg (X.property _ _)]
    rw [Finset.sum_add_distrib,← Nat.cast_sum,X.val.property.2,hP]
    ring

lemma translate_cast (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) (i : I) (j : J) :
    ((translate R₀ R₁ P₀ P₁ D hR hP X).val i j:ℤ)=(X.val.val i j:ℤ)+D i j :=
  Int.toNat_of_nonneg (X.property i j)

omit [Fintype I] in
lemma reverse_rows (R₀ R₁ : I → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i) (i : I) :
    (∑ j,-D i j)=(R₀ i:ℤ)-R₁ i := by
  rw [Finset.sum_neg_distrib,hR]
  ring

omit [Fintype J] in
lemma reverse_columns (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (j : J) :
    (∑ i,-D i j)=(P₀ j:ℤ)-P₁ j := by
  rw [Finset.sum_neg_distrib,hP]
  ring

def forward (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) :
    Accepted R₁ P₁ (fun i j => -D i j) := by
  refine ⟨translate R₀ R₁ P₀ P₁ D hR hP X,?_⟩
  intro i j
  rw [translate_cast]
  dsimp only
  omega

lemma forward_cast (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) (i : I) (j : J) :
    ((forward R₀ R₁ P₀ P₁ D hR hP X).val.val i j:ℤ)=(X.val.val i j:ℤ)+D i j :=
  translate_cast R₀ R₁ P₀ P₁ D hR hP X i j

def backward (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₁ P₁ (fun i j => -D i j)) :
    Accepted R₀ P₀ D := by
  refine ⟨translate R₁ R₀ P₁ P₀ (fun i j => -D i j)
    (reverse_rows R₀ R₁ D hR) (reverse_columns P₀ P₁ D hP) X,?_⟩
  intro i j
  rw [translate_cast]
  omega

lemma backward_cast (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₁ P₁ (fun i j => -D i j))
    (i : I) (j : J) :
    ((backward R₀ R₁ P₀ P₁ D hR hP X).val.val i j:ℤ)=(X.val.val i j:ℤ)-D i j := by
  change ((translate R₁ R₀ P₁ P₀ (fun i j => -D i j)
    (reverse_rows R₀ R₁ D hR) (reverse_columns P₀ P₁ D hP) X).val i j:ℤ)=_
  rw [translate_cast]
  rfl

def acceptedEquiv (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) :
    Accepted R₀ P₀ D ≃ Accepted R₁ P₁ (fun i j => -D i j) where
  toFun := forward R₀ R₁ P₀ P₁ D hR hP
  invFun := backward R₀ R₁ P₀ P₁ D hR hP
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    apply Int.natCast_inj.mp
    change ((backward R₀ R₁ P₀ P₁ D hR hP (forward R₀ R₁ P₀ P₁ D hR hP X)).val.val i j:ℤ)=_
    rw [backward_cast,forward_cast]
    ring
  right_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    apply Int.natCast_inj.mp
    change ((forward R₀ R₁ P₀ P₁ D hR hP (backward R₀ R₁ P₀ P₁ D hR hP X)).val.val i j:ℤ)=_
    rw [forward_cast,backward_cast]
    ring

theorem accepted_card_symmetric (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) :
    Fintype.card (Accepted R₀ P₀ D)=Fintype.card (Accepted R₁ P₁ (fun i j => -D i j)) :=
  Fintype.card_congr (acceptedEquiv R₀ R₁ P₀ P₁ D hR hP)

end ContingencyTables.CompletionTranslation

end OAI
