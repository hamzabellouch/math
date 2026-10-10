import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternDiagonalObservable
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedRegularProduct

namespace OAI

/-! # The original diagonal observable with its genuine common-product multiplier -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalPatternDiagonalObservable_primeProduct {B C : Type*}
    {N n m : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (x : Fin (N + 1) → primes) :
    let slots := movingPatternRegularSlots e n m small slot
    let value := fun i => (x i : ℕ)
    movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes p g Dq
      slots.get (fun _ => true) s
      (fun x => movingRegularOther (fun i => (x i : ℕ)) outside slots) greg f outside
      childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center x =
    complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
      movingOriginalSupportedOuterPair p value outside childBound pivotBound
        (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
        ψ X lo hi φ G Jleft Jright diagonal
        (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern)
        t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
      (‖primeProductTransform greg (outside.prod * ⌊Real.exp z⌋₊ * ⌊Real.exp y⌋₊)
        (MovingSlotReversal.naturalProduct value slots) s‖ ^ 2 : ℝ))) := by
  dsimp only
  unfold movingOriginalPatternDiagonalObservable
  dsimp only
  apply congrArg (complexPrimeInterval 1 0 a b)
  funext y
  apply congrArg (complexIntegerInterval 1 0 u v center)
  funext z
  exact movingOriginalSupportedOuterPair_regular_product e t small slot pattern
    (fun i => (x i : ℕ)) (fun i => hprimes _ (x i).property) outside p g (fun _ => Dq)
    greg s childBound pivotBound (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1)
    ψ X lo hi φ G Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊

end Ostmann

end OAI
