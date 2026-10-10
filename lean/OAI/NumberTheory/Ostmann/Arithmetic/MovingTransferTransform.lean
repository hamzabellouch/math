import OAI.NumberTheory.Ostmann.Arithmetic.MovingTransferSlots

namespace OAI

/-! # The full Fourier transform in the actual transfer slot order -/

namespace Ostmann
open scoped Classical BigOperators

/-- A common formula for regular factors and the two marked giant phases.
Using the modulus as an explicit argument makes reindexing independent of
presentation of the dependent residue types. -/
noncomputable def movingTaggedTransform {I : Type*} [Fintype I]
    (p : I → ℕ) (giant : I → Bool)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) : ℂ :=
  ∏ i, (if giant i then
      (fun t => if favorable (p i) then complexUnitPhase (ggiant (p i) t) else 0)
    else greg (p i))
      ((s : ZMod (p i)) * ((D * tupleCofactor p i : ℕ) : ZMod (p i))⁻¹)

theorem movingTaggedTransform_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (giant : J → Bool)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform (p ∘ e) (giant ∘ e) greg ggiant favorable D s =
      movingTaggedTransform p giant greg ggiant favorable D s := by
  unfold movingTaggedTransform
  dsimp only [Function.comp_def]
  simp_rw [tupleCofactor_equiv e p hp]
  exact e.prod_comp (fun j => (if giant j then
      (fun t => if favorable (p j) then complexUnitPhase (ggiant (p j) t) else 0)
    else greg (p j))
      ((s : ZMod (p j)) * ((D * tupleCofactor p j : ℕ) : ZMod (p j))⁻¹))

/-- Restoring a compensation sample places precisely the extracted giant
and its compensation factors before the surviving giant and regular factors. -/
theorem movingTaggedTransform_restored {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → A)
    (y : MovingRegularSlot n r m → A) (XL XR : ℕ)
    (hXL : XL ≠ 0) (hXR : XR ≠ 0)
    (hu : ∀ i, value (u i) ≠ 0) (hy : ∀ i, value (y i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then XL else XR)
        (value ∘ movingRestoreSample n r m u y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingTaggedTransform
      (Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ u))
        (Sum.elim (fun _ : Unit => XR) (value ∘ y)))
      (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false))) greg ggiant favorable D s := by
  let p : Bool ⊕ MovingRegularSlot n (4 + r) m → ℕ :=
    Sum.elim (fun b : Bool => if b then XL else XR)
    (value ∘ movingRestoreSample n r m u y)
  let t : Bool ⊕ MovingRegularSlot n (4 + r) m → Bool :=
    Sum.elim (fun _ => true) (fun _ => false)
  have hp : ∀ i, p i ≠ 0 := by
    intro i
    rcases i with (b | i)
    · cases b <;> assumption
    · change value (movingRestoreSample n r m u y i) ≠ 0
      unfold movingRestoreSample
      dsimp only [Function.comp_apply]
      cases he : (movingReverseTemplate n r m).symm i with
      | inl j => exact hu j
      | inr j => exact hy j
  have ht : t ∘ movingTransferSlotEquiv n r m =
      Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false)) := by
    funext i
    rcases i with ((i | i) | (i | i)) <;> rfl
  have he := movingTaggedTransform_equiv (movingTransferSlotEquiv n r m) p hp t
    greg ggiant favorable D s
  rw [ht] at he
  have hv := movingTransferSlotEquiv_values value n r m u y XL XR
  change p ∘ movingTransferSlotEquiv n r m = _ at hv
  rw [hv] at he
  exact he.symm

end Ostmann

end OAI
