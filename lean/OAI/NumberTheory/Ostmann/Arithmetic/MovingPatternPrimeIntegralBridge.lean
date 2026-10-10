import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeRelabel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeCRT
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedPairHaarComparison

namespace OAI

/-! # The original prime integrand and the integrated pattern CRT identity -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The leaf frequency mask has no dependence on the names of sampled slots. -/
theorem movingOriginalPatternPrimeObservable_pair_frequency {σ I B C : Type}
    {N n m : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (pattern : Bool × MovingSampleIndex n → C)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (x : Fin (N + 1) → σ) (u v r s : ℝ) :
    movingOriginalPatternPrimeObservable e pattern q value outside childBound pivotBound
      (fun {_} _ => f) g Dq S ψ X lo hi φ G t small (bulkSlotLeaves n m slot) u v r s x =
    complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun z =>
      movingOriginalSupportedPair q (value ∘ x) outside childBound pivotBound
        (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) S ψ X lo hi φ G
        (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern) t
        ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊)) := by
  rw [movingOriginalPatternPrimeObservable_fin]
  congr 1

section
variable {B C I : Type} [Fintype C] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

theorem movingPatternTwoPrimeObservable_integral_crt (x : Fin (N + 1) → primes)
    (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
    [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
    [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
    (hP : P = Finset.univ.image (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hinj : Function.Injective (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hprecision : R ^ (n + 1) ∣ (r : ℤ))
    (hcover : ∀ b, ∀ o ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).occurrences,
      ∀ i ∈ o.current.compensationSlots, (x i : ℕ) ∈ P)
    (hc : Pairwise (fun b c => (movingArithmeticModuli r p P Finset.univ b).Coprime
      (movingArithmeticModuli r p P Finset.univ c)))
    (hpage : pageAtModulus (∏ b, movingArithmeticModuli r p P Finset.univ b)
      (selectedPageZero input Q) = pageAtModulus r (selectedPageZero input Q))
    (u v a b : ℝ) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun side => (T side).formulaNodes value
      (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq side)
      (.prime false) (.prime true)
    (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      movingPatternTwoPrimeObservable e t small slot perm pattern primes hprimes childBound pivotBound
        hfreq F E outside R r p g twist input Q z y ψ X lo hi hlo hhi φ G
        (Real.exp z) (Real.exp y) x / ((z : ℂ) * (y : ℂ))) *
      movingPatternPrimeHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
        n t small (movingPatternBulkLeaves n m slot perm) pattern x =
    ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) *
        correctedPrimePairAverage input Q (∏ j, movingArithmeticModuli r p P Finset.univ j)
          (movingSeparatedPairResidueCoefficient p value outside F E g (fun side i => twist i side)
            Finset.univ T nodes R) z y / ((z : ℂ) * (y : ℂ)) := by
  dsimp only
  rw [← integral_mul_const]
  congr 1
  funext z
  rw [← integral_mul_const]
  congr 1
  funext y
  rw [← mul_div_right_comm]
  rw [movingPatternTwoPrimeObservable_crt e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist input Q ψ X lo hi hlo hhi φ G
    x P hP hinj hR hprecision hcover hc hpage z y]

end
end Ostmann

end OAI
