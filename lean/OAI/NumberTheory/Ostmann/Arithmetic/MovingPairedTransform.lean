import OAI.NumberTheory.Ostmann.Arithmetic.MovingTransferTransform

namespace OAI

/-! # The surviving Fourier factors in the paired regular template -/

namespace Ostmann
open scoped Classical BigOperators

local instance pairedSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

def movingPairedGiantEquiv (n r m : ℕ) :
    ((Unit ⊕ MovingRegularSlot n r m) ⊕ (Unit ⊕ MovingRegularSlot n r m)) ≃
      (Bool ⊕ MovingRegularSlot (n + 1) r m) where
  toFun
    | .inl (.inl _) => .inl true
    | .inl (.inr i) => .inr (.inl i.1, i.2)
    | .inr (.inl _) => .inl false
    | .inr (.inr i) => .inr (.inr i.1, i.2)
  invFun
    | .inl true => .inl (.inl ())
    | .inl false => .inr (.inl ())
    | .inr (.inl i, j) => .inl (.inr (i, j))
    | .inr (.inr i, j) => .inr (.inr (i, j))
  left_inv := by
    intro i
    rcases i with ((u | ⟨i, j⟩) | (u | ⟨i, j⟩))
    · cases u; rfl
    · rfl
    · cases u; rfl
    · rfl
  right_inv := by
    intro i
    rcases i with (b | ⟨i, j⟩)
    · cases b <;> rfl
    · cases i <;> rfl

/-- Both surviving giants and every regular factor occur once in the next
full transform. This is independent of the reconstructed pivot. -/
theorem movingTaggedTransform_paired {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (left right : MovingRegularSlot n r m → A) (XL XR : ℕ)
    (hXL : XL ≠ 0) (hXR : XR ≠ 0)
    (hleft : ∀ i, value (left i) ≠ 0) (hright : ∀ i, value (right i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform
      (Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ left))
        (Sum.elim (fun _ : Unit => XR) (value ∘ right)))
      (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false))) greg ggiant favorable D s =
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then XL else XR)
        (value ∘ movingTemplatePairSample n r m left right))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s := by
  let p : Bool ⊕ MovingRegularSlot (n + 1) r m → ℕ :=
    Sum.elim (fun b => if b then XL else XR)
      (value ∘ movingTemplatePairSample n r m left right)
  let t : Bool ⊕ MovingRegularSlot (n + 1) r m → Bool :=
    Sum.elim (fun _ => true) (fun _ => false)
  have hp : ∀ i, p i ≠ 0 := by
    intro i
    rcases i with (b | ⟨j, k⟩)
    · cases b <;> assumption
    · cases j with
      | inl j => exact hleft (j, k)
      | inr j => exact hright (j, k)
  have ht : t ∘ movingPairedGiantEquiv n r m =
      Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false)) := by
    funext i
    rcases i with ((i | i) | (i | i)) <;> rfl
  have hv : p ∘ movingPairedGiantEquiv n r m =
      Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ left))
        (Sum.elim (fun _ : Unit => XR) (value ∘ right)) := by
    funext i
    rcases i with ((i | i) | (i | i)) <;> rfl
  have he := movingTaggedTransform_equiv (movingPairedGiantEquiv n r m) p hp t
    greg ggiant favorable D s
  rw [ht, hv] at he
  exact he

/-- The tagged presentation is the same full transform used by the
coefficient-to-prime-statistic identity. -/
theorem movingTaggedTransform_full {I : Type*} [Fintype I]
    (q : Bool → ℕ) (p : I → ℕ) [∀ b, NeZero (q b)] [∀ i, NeZero (p i)]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform (Sum.elim q p)
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingRegularTransform (Sum.elim q p)
      (fun i => match i with
        | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
        | .inr j => greg (p j)) D s := by
  unfold movingTaggedTransform movingRegularTransform
  apply Finset.prod_congr rfl
  intro i _
  cases i <;> rfl

end Ostmann

end OAI
