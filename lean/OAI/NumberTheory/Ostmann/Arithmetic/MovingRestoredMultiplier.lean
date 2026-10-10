import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularMultiplierIdentity
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTransferSlots

namespace OAI

/-! # The surviving Fourier factors in the restored compensation coordinates -/

namespace Ostmann
open scoped Classical BigOperators

/-- The extracted compensation primes retain their places in every cofactor,
but the Cauchy step leaves no Fourier factor at those places. -/
def movingRestoredActive (n r m : ℕ) : MovingRegularSlot n (4 + r) m → Bool :=
  Sum.elim (fun _ => false) (fun _ => true) ∘ (movingReverseTemplate n r m).symm

@[simp] theorem movingRestoredActive_compensation (n r m : ℕ)
    (i : TreeLeafIndex n × Fin 4) :
    movingRestoredActive n r m (movingReverseTemplate n r m (.inl i)) = false := by
  simp only [movingRestoredActive, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem movingRestoredActive_surviving (n r m : ℕ)
    (i : MovingRegularSlot n r m) :
    movingRestoredActive n r m (movingReverseTemplate n r m (.inr i)) = true := by
  simp only [movingRestoredActive, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]

/-- In particular every protected bulk coordinate remains active. -/
@[simp] theorem movingRestoredActive_bulk (n r m : ℕ) (i : TreeLeafIndex n × Fin m) :
    movingRestoredActive n r m (movingTemplateBulk n (4 + r) m i) = true := by
  rw [← movingReverseTemplate_bulk, movingRestoredActive_surviving]

theorem movingRestoredActive_inactive_not_bulk (n r m : ℕ)
    (i : MovingRegularSlot n (4 + r) m) (hi : movingRestoredActive n r m i = false) :
    i ∉ Set.range (movingTemplateBulk n (4 + r) m) := by
  rintro ⟨j, rfl⟩
  simp only [movingRestoredActive_bulk, Bool.true_eq_false] at hi

/-- The restored masked transform is exactly the surviving transform, with
the same sampled compensation product in its outside denominator. -/
theorem movingRegularTransform_restored_active {A : Type*} (value : A → ℕ)
    (hprime : ∀ a, (value a).Prime) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D : ℕ) (s : ℤ) :
    let x := movingRestoreSample n r m u y
    let _ : ∀ i, NeZero ((value ∘ x) i) := fun i => ⟨(hprime (x i)).ne_zero⟩
    let _ : ∀ i, NeZero ((value ∘ y) i) := fun i => ⟨(hprime (y i)).ne_zero⟩
    movingRegularTransform (value ∘ x)
      (fun i z => if movingRestoredActive n r m i then g (value (x i)) z else 1) D s =
      movingRegularTransform (value ∘ y) (fun i => g (value (y i)))
        (D * ∏ i, value (u i)) s := by
  dsimp only
  let x := movingRestoreSample n r m u y
  let p := value ∘ x
  let _ : ∀ i, NeZero (p i) := fun i => ⟨(hprime (x i)).ne_zero⟩
  let _ : ∀ i, Fact (value (u i)).Prime := fun _ => ⟨hprime _⟩
  let _ : ∀ i, Fact (value (y i)).Prime := fun _ => ⟨hprime _⟩
  have he := movingRegularTransform_equiv (movingReverseTemplate n r m) p
    (fun i z => if movingRestoredActive n r m i then g (p i) z else 1) D s
  dsimp only at he
  apply he.symm.trans
  have hp : (fun i => p (movingReverseTemplate n r m i)) =
      Sum.elim (value ∘ u) (value ∘ y) := by
    funext i
    simp only [p, x, Function.comp_apply, movingRestoreSample, Equiv.symm_apply_apply]
    cases i <;> rfl
  -- Reindexing the cofactor product directly avoids transporting dependent functions.
  unfold movingRegularTransform
  rw [Fintype.prod_sum_type]
  have hu : (∏ i : TreeLeafIndex n × Fin 4,
      (if movingRestoredActive n r m (movingReverseTemplate n r m (.inl i)) then
        g (p (movingReverseTemplate n r m (.inl i)))
          ((s : ZMod (p (movingReverseTemplate n r m (.inl i)))) *
            ((D * tupleCofactor (fun j => p (movingReverseTemplate n r m j)) (.inl i) : ℕ) :
              ZMod (p (movingReverseTemplate n r m (.inl i))))⁻¹)
      else 1)) = 1 := by simp only [movingRestoredActive_compensation, Bool.false_eq_true,
        ite_false, Finset.prod_const_one]
  rw [hu, one_mul]
  apply Finset.prod_congr rfl
  intro i _
  simp only [movingRestoredActive_surviving, ite_true]
  have hc : tupleCofactor (fun j => p (movingReverseTemplate n r m j)) (.inr i) =
      (∏ j, value (u j)) * tupleCofactor (value ∘ y) i := by
    rw [hp, tupleCofactor_sum_right (value ∘ u) (value ∘ y) i (hprime (y i)).ne_zero]
    rfl
  rw [hc]
  let T (a : A) (M : ℕ) : ℂ :=
    g (value a) ((s : ZMod (value a)) * (M : ZMod (value a))⁻¹)
  change T (Sum.elim u y ((movingReverseTemplate n r m).symm
      (movingReverseTemplate n r m (.inr i))))
      (D * ((∏ j, value (u j)) * tupleCofactor (value ∘ y) i)) =
    T (y i) ((D * ∏ j, value (u j)) * tupleCofactor (value ∘ y) i)
  rw [Equiv.symm_apply_apply]
  congr 1
  ac_rfl

/-- The arithmetic multiplier with inactive compensation slots gives the
same surviving transform, retaining every compensation prime in its denominator. -/
theorem naturalRegularMultiplier_restored_active {A : Type*} (value : A → ℕ)
    (hprime : ∀ a, (value a).Prime) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D XL XR : ℕ) (s : ℤ) :
    let x := movingRestoreSample n r m u y
    let _ : ∀ i, Fact ((value ∘ x) i).Prime := fun i => ⟨hprime (x i)⟩
    let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime (y i)⟩
    naturalRegularMultiplier (value ∘ x) (movingRestoredActive n r m) s
      (fun i => ((D * tupleCofactor (value ∘ x) i : ℕ) : ZMod ((value ∘ x) i)))
      (fun i => g (value (x i))) XL XR =
    ‖movingRegularTransform (value ∘ y) (fun i => g (value (y i)))
      (D * XL * XR * ∏ i, value (u i)) s‖ ^ 2 := by
  dsimp only
  let _ : ∀ i, Fact ((value ∘ movingRestoreSample n r m u y) i).Prime :=
    fun i => ⟨hprime _⟩
  let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime _⟩
  rw [naturalRegularMultiplier_eq_transform_norm]
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (movingRegularTransform_restored_active value hprime n r m u y g (D * XL * XR) s)

/-- Distinct surviving primes put the same identity in product coordinates. -/
theorem naturalRegularMultiplier_restored_primeProduct {A : Type*} (value : A → ℕ)
    (hprime : ∀ a, (value a).Prime) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (hy : Function.Injective (value ∘ y))
    (g : ∀ q : ℕ, ZMod q → ℂ) (D XL XR : ℕ) (s : ℤ) :
    let x := movingRestoreSample n r m u y
    let _ : ∀ i, Fact ((value ∘ x) i).Prime := fun i => ⟨hprime (x i)⟩
    naturalRegularMultiplier (value ∘ x) (movingRestoredActive n r m) s
      (fun i => ((D * tupleCofactor (value ∘ x) i : ℕ) : ZMod ((value ∘ x) i)))
      (fun i => g (value (x i))) XL XR =
    ‖primeProductTransform g (D * XL * XR * ∏ i, value (u i)) (∏ i, value (y i)) s‖ ^ 2 := by
  dsimp only
  let _ : ∀ i, Fact ((value ∘ movingRestoreSample n r m u y) i).Prime :=
    fun i => ⟨hprime _⟩
  let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime _⟩
  rw [naturalRegularMultiplier_restored_active value hprime]
  simpa only [Function.comp_def] using congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (movingRegularTransform_eq_primeProduct (value ∘ y) hy g
      (D * XL * XR * ∏ i, value (u i)) s)

end Ostmann

end OAI
