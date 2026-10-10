import OAI.NumberTheory.Ostmann.Characters.FrequencyTreeSum
import OAI.NumberTheory.Ostmann.Characters.HistoryReconstruction

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HistoryFrequencyLabels
open HistoryReconstruction

@[reducible] def RangeSupported (S : List Bool → Finset ℤ) :
    (k : ℕ) → List Bool → ℤ → Tree k → Prop
  | 0, p, s, _ => s ∈ S p
  | k+1, p, s, t => s ∈ S p ∧
      RangeSupported S k (false::p) t.1.1 t.2.1 ∧
      RangeSupported S k (true::p) t.1.2 t.2.2

def SupportedHistory (S : List Bool → Finset ℤ) (k : ℕ) (p : List Bool) :=
  {z : ℤ × Tree k // RangeSupported S k p z.1 z.2}

def treeOf (S : List Bool → Finset ℤ) :
    {k : ℕ} → {p : List Bool} → FrequencyTreeSum.Assignment S k p → Tree k
  | 0, _, _ => PUnit.unit
  | _+1, _, x => ((FrequencyTreeSum.root S x.2.1, FrequencyTreeSum.root S x.2.2),
      treeOf S x.2.1, treeOf S x.2.2)

theorem treeOf_supported (S : List Bool → Finset ℤ) {k : ℕ} {p : List Bool}
    (x : FrequencyTreeSum.Assignment S k p) :
    RangeSupported S k p (FrequencyTreeSum.root S x) (treeOf S x) := by
  induction k generalizing p with
  | zero => exact x.property
  | succ k ih => exact ⟨x.1.property, ih x.2.1, ih x.2.2⟩

def fromTree (S : List Bool → Finset ℤ) : (k : ℕ) → (p : List Bool) →
    (s : ℤ) → (t : Tree k) → RangeSupported S k p s t →
    FrequencyTreeSum.Assignment S k p
  | 0, _, s, _, h => ⟨s, h⟩
  | k+1, p, s, t, h => (⟨s, h.1⟩,
      fromTree S k (false::p) t.1.1 t.2.1 h.2.1,
      fromTree S k (true::p) t.1.2 t.2.2 h.2.2)

@[simp] theorem root_fromTree (S : List Bool → Finset ℤ) (k : ℕ) (p : List Bool)
    (s : ℤ) (t : Tree k) (h : RangeSupported S k p s t) :
    FrequencyTreeSum.root S (fromTree S k p s t h) = s := by
  cases k <;> rfl

@[simp] theorem treeOf_fromTree (S : List Bool → Finset ℤ) (k : ℕ) (p : List Bool)
    (s : ℤ) (t : Tree k) (h : RangeSupported S k p s t) :
    treeOf S (fromTree S k p s t h) = t := by
  induction k generalizing p s with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    rcases t with ⟨⟨v,w⟩,l,r⟩
    simp only [fromTree, treeOf, root_fromTree, ih]

@[simp] theorem fromTree_treeOf (S : List Bool → Finset ℤ) {k : ℕ} {p : List Bool}
    (x : FrequencyTreeSum.Assignment S k p) :
    fromTree S k p (FrequencyTreeSum.root S x) (treeOf S x)
      (treeOf_supported S x) = x := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rcases x with ⟨s,l,r⟩
    change (s, fromTree S k (false::p) (FrequencyTreeSum.root S l)
      (treeOf S l) (treeOf_supported S l),
      fromTree S k (true::p) (FrequencyTreeSum.root S r)
        (treeOf S r) (treeOf_supported S r)) = (s,l,r)
    exact Prod.ext rfl (Prod.ext (ih l) (ih r))

def assignmentEquiv (S : List Bool → Finset ℤ) (k : ℕ) (p : List Bool) :
    FrequencyTreeSum.Assignment S k p ≃ SupportedHistory S k p where
  toFun x := ⟨(FrequencyTreeSum.root S x, treeOf S x), treeOf_supported S x⟩
  invFun h := fromTree S k p h.val.1 h.val.2 h.property
  left_inv := fromTree_treeOf S
  right_inv h := by
    apply Subtype.ext
    exact Prod.ext (root_fromTree S k p _ _ _) (treeOf_fromTree S k p _ _ _)

instance supportedHistoryFintype (S : List Bool → Finset ℤ) (k : ℕ) (p : List Bool) :
    Fintype (SupportedHistory S k p) :=
  Fintype.ofEquiv (FrequencyTreeSum.Assignment S k p) (assignmentEquiv S k p)

@[simp] theorem assignmentEquiv_root (S : List Bool → Finset ℤ) (k : ℕ)
    (p : List Bool) (x : FrequencyTreeSum.Assignment S k p) :
    (assignmentEquiv S k p x).val.1 = FrequencyTreeSum.root S x := rfl

@[simp] theorem assignmentEquiv_tree (S : List Bool → Finset ℤ) (k : ℕ)
    (p : List Bool) (x : FrequencyTreeSum.Assignment S k p) :
    (assignmentEquiv S k p x).val.2 = treeOf S x := rfl

@[simp] theorem treeOf_left_frequency (S : List Bool → Finset ℤ) (k : ℕ)
    (p : List Bool) (x : FrequencyTreeSum.Assignment S (k+1) p) :
    (treeOf S x).1.1 = FrequencyTreeSum.root S x.2.1 := rfl

@[simp] theorem treeOf_right_frequency (S : List Bool → Finset ℤ) (k : ℕ)
    (p : List Bool) (x : FrequencyTreeSum.Assignment S (k+1) p) :
    (treeOf S x).1.2 = FrequencyTreeSum.root S x.2.2 := rfl

@[simp] theorem treeOf_left (S : List Bool → Finset ℤ) (k : ℕ)
    (p : List Bool) (x : FrequencyTreeSum.Assignment S (k+1) p) :
    (treeOf S x).2.1 = treeOf S x.2.1 := rfl

@[simp] theorem treeOf_right (S : List Bool → Finset ℤ) (k : ℕ)
    (p : List Bool) (x : FrequencyTreeSum.Assignment S (k+1) p) :
    (treeOf S x).2.2 = treeOf S x.2.2 := rfl

theorem sum_reindex {A : Type*} [AddCommMonoid A] (S : List Bool → Finset ℤ)
    (k : ℕ) (p : List Bool) (F : ℤ → Tree k → A) :
    (∑ x : FrequencyTreeSum.Assignment S k p,
      F (FrequencyTreeSum.root S x) (treeOf S x)) =
    ∑ h : SupportedHistory S k p, F h.val.1 h.val.2 :=
  (assignmentEquiv S k p).sum_comp (fun h => F h.val.1 h.val.2)

end Ostmann.Characters.HistoryFrequencyLabels

end

end OAI
