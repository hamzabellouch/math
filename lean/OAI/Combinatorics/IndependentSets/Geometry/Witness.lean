import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LabelCoverData

namespace OAI

namespace LargeIndependentSets

instance (priority := 1100) mixedTupleComputableFintype {A B : Type*} [Fintype A] [Fintype B]
    (n i : ℕ) : Fintype (MixedTuple A B n i) :=
  inferInstanceAs (Fintype {x : Fin n → B ⊕ A // ∀ h, (x h).isLeft = decide (h.val < i)})

instance mixedTupleDecidableEq {A B : Type*} [DecidableEq A] [DecidableEq B]
    (n i : ℕ) : DecidableEq (MixedTuple A B n i) :=
  inferInstanceAs (DecidableEq {x : Fin n → B ⊕ A // ∀ h, (x h).isLeft = decide (h.val < i)})

namespace LayerImposed

abbrev Witness (U V C : Type) (n : ℕ) :=
  Σ h : Fin n, MixedTuple U V n h.val × MixedTuple U V n (h.val+1) × C

abbrev Arrow (U V L R : Type) (n : ℕ) :=
  Σ q : LayerQuestion U V n, Σ q' : LayerQuestion U V n, LayerAnswer L R q → LayerAnswer L R q'

def valid {U V L R C : Type} (lc : LabelCoverData U V L R C) {n : ℕ}
    (w : Witness U V C n) : Prop :=
  w.2.1.val w.1 = Sum.inr (lc.left w.2.2.2) ∧
  w.2.2.1.val w.1 = Sum.inl (lc.right w.2.2.2) ∧
  ∀ k, k ≠ w.1 → w.2.1.val k = w.2.2.1.val k

instance valid_decidable {U V L R C : Type} [DecidableEq U] [DecidableEq V]
    (lc : LabelCoverData U V L R C) {n : ℕ} (w : Witness U V C n) : Decidable (valid lc w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _, _ → _))

def arrow {U V L R C : Type} (lc : LabelCoverData U V L R C) {n : ℕ}
    (w : Witness U V C n) : Arrow U V L R n :=
  ⟨⟨w.1.castSucc,w.2.1⟩,⟨w.1.succ,w.2.2.1⟩, mixedProject w.1 (lc.project w.2.2.2)⟩

def arrowImposed {U V L R C : Type} (lc : LabelCoverData U V L R C) {n : ℕ}
    (a : Arrow U V L R n) : Prop := LayerImposed lc n a.1 a.2.1 a.2.2

lemma iff_witness {U V L R C : Type} (lc : LabelCoverData U V L R C) {n : ℕ}
    (q q' : LayerQuestion U V n) (π : LayerAnswer L R q → LayerAnswer L R q') :
    LayerImposed lc n q q' π ↔
      ∃ w : Witness U V C n, valid lc w ∧ arrow lc w = ⟨q,q',π⟩ := by
  constructor
  · intro h
    cases h with
    | adjacent k x y c hl hr ho => exact ⟨⟨k,x,y,c⟩,⟨hl,hr,ho⟩,rfl⟩
  · rintro ⟨w,hw,he⟩
    have h : arrowImposed lc (arrow lc w) :=
      .adjacent w.1 w.2.1 w.2.2.1 w.2.2.2 hw.1 hw.2.1 hw.2.2
    rw [he] at h
    exact h

instance imposed_decidable {U V L R C : Type} [Fintype U] [Fintype V] [Fintype C]
    [Fintype L] [Fintype R] [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    (lc : LabelCoverData U V L R C) (n : ℕ) (q q' : LayerQuestion U V n)
    (π : LayerAnswer L R q → LayerAnswer L R q') : Decidable (LayerImposed lc n q q' π) := by
  letI : Fintype (Witness U V C n) := inferInstance
  letI : DecidableEq (Arrow U V L R n) := inferInstance
  exact decidable_of_iff _ (iff_witness lc q q' π).symm

end LayerImposed
end LargeIndependentSets

end OAI
