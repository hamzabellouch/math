import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkOriginalCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogTrees

namespace OAI

/-! # The actual terminal log factors in the original giant coefficient -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The terminal weights factor from the full original recursion, with its
sharp windows, cutoffs and support retained. -/
theorem movingOriginalGiantWeight_bulk_log {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value tier : σ → ℕ)
    (k : ℕ) (outside : List ℕ) (cb cd : ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (XL XR : ℕ) :
    movingOriginalGiantWeight q value childBound pivotBound
        (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s)
        E g Dq S ψ X lo hi φ G T t XL XR =
      (movingBulkTreeLogWeight value tier k outside cb cd T : ℂ) *
        movingOriginalGiantWeight q value childBound pivotBound F E g Dq S
          ψ X lo hi φ G T t XL XR := by
  have hleaf : movingOriginalLeaf value q
      (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s)
      g Dq S ψ X lo hi =
      fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) *
        movingOriginalLeaf value q F g Dq S ψ X lo hi x s := by
    funext x s
    exact movingOriginalLeaf_bulk_log value tier k outside cb cd q F g Dq S ψ X lo hi x s
  change recursiveTransferWeight _ (movingOriginalLeaf value q _ g Dq S ψ X lo hi) _ _ _ _ = _
  rw [hleaf]
  exact movingSlotWeight_bulk_log value tier k outside cb cd childBound pivotBound
    (movingOriginalLeaf value q F g Dq S ψ X lo hi) _ T XL XR t

/-- Both original branches retain their own terminal grouping inside the
common prime average; the fixed outside profile is the only scalar extracted. -/
theorem movingOriginalGiantWeight_pair_bulk_log {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value tier : σ → ℕ)
    (hvalue : ∀ a, 0 < value a) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n) (XL XR : ℕ) :
    let slots := Fin.append
      (fun j : Fin (bulkLogLeafLists tier k (T false)).length => (bulkLogLeafLists tier k (T false))[j])
      (fun j : Fin (bulkLogLeafLists tier k (T true)).length => (bulkLogLeafLists tier k (T true))[j])
    let W := fun b => movingOriginalGiantWeight q value childBound pivotBound
      (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F b T s)
      (E b) g (Dq b) S ψ X lo hi φ G (T b) (t b) XL XR
    W false * star (W true) =
      (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^
        (2 ^ n + 2 ^ n) : ℝ) *
      ((∏ j, bulkLogCutoffWeight (fun a => (value a : ℝ)) cb (slots j) : ℝ) : ℂ) *
      (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g
        (Dq false) S ψ X lo hi φ G (T false) (t false) XL XR *
        star (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g
          (Dq true) S ψ X lo hi φ G (T true) (t true) XL XR)) := by
  dsimp only
  rw [movingOriginalGiantWeight_bulk_log, movingOriginalGiantWeight_bulk_log, star_mul]
  calc
    _ = ((movingBulkTreeLogWeight value tier k outside cb cd (T false) : ℂ) *
        star (movingBulkTreeLogWeight value tier k outside cb cd (T true) : ℂ)) *
      (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g
        (Dq false) S ψ X lo hi φ G (T false) (t false) XL XR *
        star (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g
          (Dq true) S ψ X lo hi φ G (T true) (t true) XL XR)) := by ring
    _ = _ := by rw [movingBulkPairLogWeight_eq_cutoff_product value tier hvalue k outside cb cd T]

end Ostmann

end OAI
