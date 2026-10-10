import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularDiagonal
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternRegularUnits
import OAI.NumberTheory.Ostmann.Construction.RegularGiantMultiplier

namespace OAI

/-! # The literal diagonal multiplier is the squared regular Fourier product -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRegularOther_eq_cofactor {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (slots : List σ) (j : Fin slots.length) :
    movingRegularOther value outside slots j =
      ((outside.prod * tupleCofactor (fun i => value (slots.get i)) j : ℕ) : ℤ) := by
  unfold movingRegularOther tupleCofactor
  congr 2
  apply Finset.prod_congr
  · ext i
    simp only [Finset.mem_erase, Finset.mem_univ]
  · intro i _
    rfl

theorem naturalRegularMultiplier_eq_transform_norm {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (D : ℕ) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) :
    naturalRegularMultiplier p active s
      (fun i => ((D * tupleCofactor p i : ℕ) : ZMod (p i))) g XL XR =
      ‖movingRegularTransform p (fun i x => if active i then g i x else 1)
        (D * XL * XR) s‖ ^ 2 := by
  rw [movingRegularTransform, norm_prod, ← Finset.prod_pow]
  unfold naturalRegularMultiplier
  apply Finset.prod_congr rfl
  intro i _
  cases ha : active i
  · simp only [Bool.false_eq_true, ite_false, norm_one, one_pow]
  · simp only [ite_true]
    congr 2
    simp only [div_eq_mul_inv, Nat.cast_mul]
    congr 2
    ring

theorem movingPattern_regular_multiplier_eq_transform {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (value : Fin (N + 1) → ℕ)
    (hprime : ∀ i, (value i).Prime) (outside : List ℕ)
    (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
    (g : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (XL XR : ℕ) :
    let slots := movingPatternRegularSlots e n m small slot
    let p := fun i : Fin slots.length => value (slots.get i)
    let : ∀ i, Fact (p i).Prime := fun _ => ⟨hprime _⟩
    naturalRegularMultiplier p active s
      (fun i => (movingRegularOther value outside slots i : ZMod (p i)))
      (fun i => g (p i)) XL XR =
      ‖movingRegularTransform p (fun i x => if active i then g (p i) x else 1)
        (outside.prod * XL * XR) s‖ ^ 2 := by
  dsimp only
  let : ∀ i : Fin (movingPatternRegularSlots e n m small slot).length,
      Fact (value ((movingPatternRegularSlots e n m small slot).get i)).Prime := fun _ => ⟨hprime _⟩
  simp only [movingRegularOther_eq_cofactor, Int.cast_natCast]
  exact naturalRegularMultiplier_eq_transform_norm _ active s outside.prod _ XL XR

/-- On the original support, the squared regular factor depends only on the
prime product, frequency, outside product, and the two current giants. -/
theorem movingPattern_regular_multiplier_eq_primeProduct {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ)
    (hprime : ∀ i, (value i).Prime) (outside : List ℕ)
    (g : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (XL XR : ℕ)
    (h : movingRegularOutsidePairwise value outside
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern false)) :
    let slots := movingPatternRegularSlots e n m small slot
    let p := fun i : Fin slots.length => value (slots.get i)
    let : ∀ i, Fact (p i).Prime := fun _ => ⟨hprime _⟩
    naturalRegularMultiplier p (fun _ => true) s
      (fun i => (movingRegularOther value outside slots i : ZMod (p i)))
      (fun i => g (p i)) XL XR =
      ‖primeProductTransform g (outside.prod * XL * XR)
        (MovingSlotReversal.naturalProduct value slots) s‖ ^ 2 := by
  dsimp only
  let slots := movingPatternRegularSlots e n m small slot
  let p := fun i : Fin slots.length => value (slots.get i)
  let : ∀ i, Fact (p i).Prime := fun _ => ⟨hprime _⟩
  have hp := movingPattern_regular_pairwise e t small slot pattern value outside false h
  have hinj : Function.Injective p := by
    intro i j he
    by_contra hne
    have hc := hp hne
    change (p i).Coprime (p j) at hc
    rw [he, Nat.coprime_self] at hc
    exact (hprime _).ne_one hc
  rw [movingPattern_regular_multiplier_eq_transform e small slot value hprime outside
    (fun _ => true) g s XL XR]
  simp only [ite_true]
  change ‖movingRegularTransform p (fun i => g (p i)) (outside.prod * XL * XR) s‖ ^ 2 =
    ‖primeProductTransform g (outside.prod * XL * XR)
      (MovingSlotReversal.naturalProduct value slots) s‖ ^ 2
  rw [movingRegularTransform_eq_primeProduct p hinj, naturalProduct_eq_finprod]

end Ostmann

end OAI
