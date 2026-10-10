import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeHaarComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternCoefficientMass

namespace OAI

/-! # Carrying the literal pattern integral to the signed arithmetic norm -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem movingPattern_original_integral_norm {B C I : Type}
    [Fintype B] [Fintype C] [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
    (childBound pivotBound : ℕ → ℕ)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
    (f : ℤ → ℂ) (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
    (Dq : ∀ i, (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (u v a b : ℝ)
    (E U ε : ℝ) (hE : 0 ≤ E) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (hμ : ∀ j q, 0 ≤ μ j q) (hν : ∀ j q, 0 ≤ ν j q)
    (hμmass : ∀ j, ∑ q, μ j q = 1) (hνmass : ∀ j, ∑ q, ν j q = 1)
    (hbound : ∀ j (q : primes), (q : ℝ) * μ j q ≤ E)
    (hsize : ∀ q : primes, (q : ℝ) ≤ U) :
    let actual := movingOriginalPatternPrimeObservable e pattern p
      (fun q : primes => (q : ℕ)) outside childBound pivotBound (fun {_} _ => f) g Dq Finset.univ
      ψ X lo hi φ G t small (bulkSlotLeaves n m slot) u v a b
    let integral := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      movingPatternTwoPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
        primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1)
        outside R r p g (fun i _ => Dq i) input Q z y ψ X lo hi hlo hhi φ G
        (Real.exp z) (Real.exp y) x / ((z : ℂ) * (y : ℂ))
    let haar := movingPatternPrimeHaarProduct e (fun q : primes => (q : ℕ))
      (fun q => hprimes _ q.property) n t (fun _ => small)
      (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern
    (∀ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (fun _ => 1) x ≠ 0 → ‖actual x - integral x * haar x‖ ≤ ε) →
    ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern actual x‖ ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) * ε +
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x * haar x‖ := by
  intro actual integral haar hcompare
  have h := movingPattern_comparison_norm e μ ν (fun q : primes => (q : ℕ)) pattern rep
    E U ε hE hU hε (fun q => hprimes _ q.property) hμ hν hμmass hνmass hbound hsize
    actual (fun x => integral x * haar x) hcompare
  have he (x) : movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
      (fun x => integral x * haar x) x =
      movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x * haar x := by
    simp only [movingOriginalPatternWeight, movingPatternInjectionGuard]
    split_ifs <;> ring
  simpa only [he] using h

end Ostmann

end OAI
