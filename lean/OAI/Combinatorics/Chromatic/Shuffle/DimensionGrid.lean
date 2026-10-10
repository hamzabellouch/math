import Mathlib

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*}

abbrev DimensionSplit (d : I → ℕ) := ∀ i, Fin (d i + 1)

namespace DimensionSplit

def left {d : I → ℕ} (s : DimensionSplit d) : I → ℕ := fun i => (s i).val
def right {d : I → ℕ} (s : DimensionSplit d) : I → ℕ := fun i => d i - (s i).val

@[simp] lemma left_add_right {d : I → ℕ} (s : DimensionSplit d) : left s + right s = d := by
  funext i
  have hi := (s i).isLt
  simp only [Pi.add_apply, left, right]
  omega

@[ext] lemma ext {d : I → ℕ} {s t : DimensionSplit d} (h : left s = left t) : s = t := by
  funext i
  exact Fin.ext (congrFun h i)

def ofPair (a b : I → ℕ) {d : I → ℕ} (h : a+b=d) : DimensionSplit d :=
  fun i => ⟨a i, by have hi := congrFun h i; simp only [Pi.add_apply] at hi; omega⟩

@[simp] lemma left_ofPair (a b : I → ℕ) {d : I → ℕ} (h : a+b=d) :
    left (ofPair a b h) = a := rfl

@[simp] lemma right_ofPair (a b : I → ℕ) {d : I → ℕ} (h : a+b=d) :
    right (ofPair a b h) = b := by
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply] at hi
  simp only [right, ofPair]
  omega

@[simp] lemma ofPair_left_right {d : I → ℕ} (s : DimensionSplit d) :
    ofPair (left s) (right s) (left_add_right s) = s := by
  apply ext
  rfl

def pairEquiv (d : I → ℕ) : DimensionSplit d ≃ {p : (I→ℕ) × (I→ℕ) // p.1+p.2=d} where
  toFun s := ⟨(left s,right s),left_add_right s⟩
  invFun p := ofPair p.val.1 p.val.2 p.property
  left_inv := ofPair_left_right
  right_inv p := by apply Subtype.ext; simp

end DimensionSplit

open DimensionSplit

abbrev RowDimensionGrid (d e α β : I → ℕ) :=
  {s : DimensionSplit α × DimensionSplit β //
    left s.1 + left s.2 = d ∧ right s.1 + right s.2 = e}

abbrev ColumnDimensionGrid (d e α β : I → ℕ) :=
  {s : DimensionSplit d × DimensionSplit e //
    left s.1 + left s.2 = α ∧ right s.1 + right s.2 = β}

def transposeDimensionGrid (d e α β : I → ℕ) :
    RowDimensionGrid d e α β ≃ ColumnDimensionGrid d e α β where
  toFun s := ⟨(ofPair (left s.val.1) (left s.val.2) s.property.1,
      ofPair (right s.val.1) (right s.val.2) s.property.2), by simp⟩
  invFun s := ⟨(ofPair (left s.val.1) (left s.val.2) s.property.1,
      ofPair (right s.val.1) (right s.val.2) s.property.2), by simp⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · apply DimensionSplit.ext
      simp
    · apply DimensionSplit.ext
      simp
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · apply DimensionSplit.ext
      simp
    · apply DimensionSplit.ext
      simp

@[simp] lemma transposeDimensionGrid_first_left (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    left (transposeDimensionGrid d e α β s).val.1 = left s.val.1 := rfl

@[simp] lemma transposeDimensionGrid_first_right (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    right (transposeDimensionGrid d e α β s).val.1 = left s.val.2 :=
  right_ofPair _ _ s.property.1

@[simp] lemma transposeDimensionGrid_second_left (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    left (transposeDimensionGrid d e α β s).val.2 = right s.val.1 := rfl

@[simp] lemma transposeDimensionGrid_second_right (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    right (transposeDimensionGrid d e α β s).val.2 = right s.val.2 :=
  right_ofPair _ _ s.property.2

attribute [local instance] Classical.propDecidable

lemma sum_transposeDimensionGrid [Fintype I] [DecidableEq I] (d e α β : I → ℕ)
    {M : Type*} [AddCommMonoid M] (F : ColumnDimensionGrid d e α β → M) :
    ∑ s : RowDimensionGrid d e α β, F (transposeDimensionGrid d e α β s) =
      ∑ s : ColumnDimensionGrid d e α β, F s := by
  classical
  exact Equiv.sum_comp (transposeDimensionGrid d e α β) F

lemma sum_transposeDimensionGrid_congr [Fintype I] [DecidableEq I] (d e α β : I → ℕ)
    {M : Type*} [AddCommMonoid M] (F : RowDimensionGrid d e α β → M)
    (G : ColumnDimensionGrid d e α β → M)
    (h : ∀ s,F s=G (transposeDimensionGrid d e α β s)) :
    ∑ s : RowDimensionGrid d e α β,F s=∑ s : ColumnDimensionGrid d e α β,G s := by
  classical
  calc
    _=∑ s : RowDimensionGrid d e α β,G (transposeDimensionGrid d e α β s) := by
      apply Finset.sum_congr rfl
      intro s _
      exact h s
    _=_ := sum_transposeDimensionGrid d e α β G

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
noncomputable section
variable {I A B : Type*} (δ : A → I → ℕ) (ε : B → I → ℕ)

private lemma subtypePair_heq {p q : A → Prop} {r s : B → Prop}
    (hp : p=q) (hr : r=s) (x : A) (y : B)
    (hx : p x) (hy : r y) (hx' : q x) (hy' : s y) :
    HEq ((⟨x,hx⟩ : Subtype p),(⟨y,hy⟩ : Subtype r))
      ((⟨x,hx'⟩ : Subtype q),(⟨y,hy'⟩ : Subtype s)) := by
  cases hp
  cases hr
  rfl

def dimensionProduct (d : I → ℕ) :
    (Σ s : DimensionSplit d,{x : A // δ x=s.left} × {y : B // ε y=s.right}) ≃
      {p : A×B // δ p.1+ε p.2=d} where
  toFun x:=⟨(x.2.1.val,x.2.2.val),by rw [x.2.1.property,x.2.2.property,DimensionSplit.left_add_right]⟩
  invFun p:=⟨DimensionSplit.ofPair (δ p.val.1) (ε p.val.2) p.property,
    ⟨p.val.1,rfl⟩,⟨p.val.2,(DimensionSplit.right_ofPair _ _ _).symm⟩⟩
  right_inv p:=rfl
  left_inv x:=by
    rcases x with ⟨s,⟨x,hx⟩,⟨y,hy⟩⟩
    dsimp only
    have hs : DimensionSplit.ofPair (δ x) (ε y) (by rw [hx,hy,DimensionSplit.left_add_right])=s := by
      apply DimensionSplit.ext
      exact hx
    apply Sigma.ext hs
    exact subtypePair_heq (congrArg (fun t : DimensionSplit d=>fun z=>δ z=t.left) hs)
      (congrArg (fun t : DimensionSplit d=>fun z=>ε z=t.right) hs) x y _ _ _ _

end
end ElementaryPositivity.RawShuffle

end

end OAI
