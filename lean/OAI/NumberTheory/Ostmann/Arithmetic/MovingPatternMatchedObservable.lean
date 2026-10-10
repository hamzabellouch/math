import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedOuterFactor
import OAI.NumberTheory.Ostmann.Construction.RegularGiantMultiplier

namespace OAI

/-! # The original matched-history observable on the finite pattern sample space -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalPatternMatchedObservable {B C J : Type*} [Fintype J]
    {N n m : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (reg : J → Fin (N + 1)) (active : J → Bool) (sreg : ℤ)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (x : Fin (N + 1) → primes) : ℂ := by
  let value := fun i => (x i : ℕ)
  let : ∀ j, Fact (value (reg j)).Prime := fun j => ⟨hprimes _ (x (reg j)).property⟩
  exact complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
    movingOriginalSupportedOuterPair p value outside childBound pivotBound
      (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
      ψ X lo hi φ G Jleft Jright diagonal
      (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern)
      t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
    (naturalRegularMultiplier (fun j => value (reg j)) active sreg
      (fun j => (other x j : ZMod (value (reg j)))) (fun j => greg (value (reg j)))
      ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ)))

end Ostmann

end OAI
