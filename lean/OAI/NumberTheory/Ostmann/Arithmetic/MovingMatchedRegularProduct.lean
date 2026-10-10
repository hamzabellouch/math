import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularMultiplierIdentity
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularCollisionSupport

namespace OAI

/-! # The genuine common-product factor on the entire original sample space -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalSupportedOuterPair_matched_regular_product {B C I : Type*} [Fintype I]
    {N n m : ℕ} (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ)
    (hprime : ∀ i, (value i).Prime) (outside : List ℕ)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (gspec : ∀ i, ZMod (p i) → ℂ) (Dq : Bool → ∀ i, (ZMod (p i))ˣ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ)
    (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
    (E : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (XL XR : ℕ) :
    let slots := movingPatternRegularSlots e n m small slot
    let q := fun i : Fin slots.length => value (slots.get i)
    let : ∀ i, Fact (q i).Prime := fun _ => ⟨hprime _⟩
    let T := movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern
    let W := movingOriginalSupportedOuterPair p value outside childBound pivotBound F E gspec Dq
      Finset.univ ψ X lo hi φ G Jleft Jright diagonal T t XL XR
    W * (naturalRegularMultiplier q (fun _ => true) s
      (fun i => (movingRegularOther value outside slots i : ZMod (q i)))
      (fun i => greg (q i)) XL XR : ℂ) =
    W * (‖primeProductTransform greg (outside.prod * XL * XR)
      (MovingSlotReversal.naturalProduct value slots) s‖ ^ 2 : ℝ) := by
  dsimp only
  let T := movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern
  let slots := movingPatternRegularSlots e n m small slot
  let : ∀ i : Fin slots.length, Fact (value (slots.get i)).Prime := fun _ => ⟨hprime _⟩
  by_cases hgood : movingRegularOutsidePairwise value outside (T false)
  · rw [movingPattern_regular_multiplier_eq_primeProduct e t small slot pattern value hprime
      outside greg s XL XR hgood]
  · have hbad : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b) := fun h => hgood (h false)
    have hz := movingOriginalSupportedOuterPair_zero_of_not_regular p value outside childBound
      pivotBound F E gspec Dq Finset.univ ψ X lo hi φ G Jleft Jright diagonal T t hbad XL XR
    change _ * _ = _ * _
    rw [hz, zero_mul, zero_mul]

end Ostmann

end OAI
