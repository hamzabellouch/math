import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePrimeCore
import OAI.NumberTheory.Ostmann.Characters.PermutedAdditiveCancellation

namespace OAI

/-! # Reindexing the original pivot, compensation, and surviving slots -/

namespace Ostmann
open scoped Classical BigOperators

/-- Reindexing changes neither the cofactor nor its local transform. -/
theorem movingRegularTransform_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (g : ∀ j, ZMod (p j) → ℂ) (D : ℕ) (s : ℤ) :
    let _ : ∀ i, NeZero (p (e i)) := fun _i => inferInstance
    movingRegularTransform (fun i => p (e i)) (fun i => g (e i)) D s =
      movingRegularTransform p g D s := by
  dsimp only
  unfold movingRegularTransform
  simp_rw [tupleCofactor_equiv e p (fun j => NeZero.ne (p j))]
  exact e.prod_comp (fun j => g j ((s : ZMod (p j)) *
    ((D * tupleCofactor p j : ℕ) : ZMod (p j))⁻¹))

/-- The first block is the removed giant and compensation. The second is
one surviving giant and its remaining regular slots. -/
def movingTransferSlotEquiv (n r m : ℕ) :
    ((Unit ⊕ (TreeLeafIndex n × Fin 4)) ⊕ (Unit ⊕ MovingRegularSlot n r m)) ≃
      (Bool ⊕ MovingRegularSlot n (4 + r) m) where
  toFun
    | .inl (.inl _) => .inl true
    | .inl (.inr i) => .inr (movingReverseTemplate n r m (.inl i))
    | .inr (.inl _) => .inl false
    | .inr (.inr i) => .inr (movingReverseTemplate n r m (.inr i))
  invFun
    | .inl true => .inl (.inl ())
    | .inl false => .inr (.inl ())
    | .inr j => match (movingReverseTemplate n r m).symm j with
      | .inl i => .inl (.inr i)
      | .inr i => .inr (.inr i)
  left_inv := by
    intro i
    rcases i with ((u | i) | (u | i))
    · cases u; rfl
    · change (match (movingReverseTemplate n r m).symm (movingReverseTemplate n r m (.inl i)) with
        | .inl j => Sum.inl (Sum.inr j)
        | .inr j => Sum.inr (Sum.inr j)) = _
      rw [Equiv.symm_apply_apply]
    · cases u; rfl
    · change (match (movingReverseTemplate n r m).symm (movingReverseTemplate n r m (.inr i)) with
        | .inl j => Sum.inl (Sum.inr j)
        | .inr j => Sum.inr (Sum.inr j)) = _
      rw [Equiv.symm_apply_apply]
  right_inv := by
    intro i
    rcases i with (b | j)
    · cases b <;> rfl
    · have h := (movingReverseTemplate n r m).apply_symm_apply j
      cases he : (movingReverseTemplate n r m).symm j with
      | inl k =>
        simp only [he] at h ⊢
        exact congrArg Sum.inr h
      | inr k =>
        simp only [he] at h ⊢
        exact congrArg Sum.inr h

@[simp] theorem movingTransferSlotEquiv_pivot (n r m : ℕ) :
    movingTransferSlotEquiv n r m (.inl (.inl ())) = .inl true := rfl

@[simp] theorem movingTransferSlotEquiv_old_giant (n r m : ℕ) :
    movingTransferSlotEquiv n r m (.inr (.inl ())) = .inl false := rfl

/-- The reindexing inserts precisely the same sampled compensation vector
which appears in the two child coefficients. -/
theorem movingTransferSlotEquiv_values {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) (XL XR : ℕ) :
    (fun i => Sum.elim (fun b => if b then XL else XR)
      (value ∘ movingRestoreSample n r m u y) (movingTransferSlotEquiv n r m i)) =
    Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ u))
      (Sum.elim (fun _ : Unit => XR) (value ∘ y)) := by
  funext i
  rcases i with ((j | j) | (j | j))
  · rfl
  · change value (movingRestoreSample n r m u y (movingReverseTemplate n r m (.inl j))) = value (u j)
    simp only [movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  · rfl
  · change value (movingRestoreSample n r m u y (movingReverseTemplate n r m (.inr j))) = value (y j)
    simp only [movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]

end Ostmann

end OAI
