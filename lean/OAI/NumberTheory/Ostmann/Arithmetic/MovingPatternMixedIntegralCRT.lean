import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMixedCRT
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterKernel

namespace OAI

/-! # Integrating the exact mixed CRT identity with its original outer factors -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype C] [Fintype I] {N n m : ℕ}
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

/-- Any outer factor can be retained through the finite CRT identity and both
giant integrals. The physical integer measure is `exp(z-center) dz`. -/
theorem movingPatternPrimeObservable_weighted_integral_crt (x : Fin (N + 1) → primes)
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
    (W : ℝ → ℝ → ℂ) (u v a b center : ℝ) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun side => (T side).formulaNodes value
      (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq side)
      (.prime false) (.prime true)
    (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      (W z y * movingPatternPrimeObservable e t small slot perm pattern primes hprimes childBound pivotBound
        hfreq F E outside R r p g twist input Q y ψ X lo hi hlo hhi φ G
        (Real.exp z) (Real.exp y) x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) *
      movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
        n t small (movingPatternBulkLeaves n m slot perm) pattern x =
    ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      (W z y * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) *
        correctedMixedPairAverage input Q (∏ j, movingArithmeticModuli r p P Finset.univ j)
          (movingSeparatedPairResidueCoefficient p value outside F E g (fun side i => twist i side)
            Finset.univ T nodes R) y) * (Real.exp (z - center) : ℂ) / (y : ℂ) := by
  dsimp only
  rw [← integral_mul_const]
  congr 1
  funext z
  rw [← integral_mul_const]
  congr 1
  funext y
  have he := movingPatternPrimeObservable_crt e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist input Q ψ X lo hi hlo hhi φ G
    x P hP hinj hR hprecision hcover hc hpage z y
  dsimp only at he
  calc
    _ = (W z y * (movingPatternPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist input Q y ψ X lo hi hlo hhi φ G
      (Real.exp z) (Real.exp y) x * movingPatternHaarProduct e (fun q : primes => (q : ℕ))
        (fun q => hprimes _ q.property) n t small (movingPatternBulkLeaves n m slot perm) pattern x)) *
          (Real.exp (z - center) : ℂ) / (y : ℂ) := by ring
    _ = _ := by rw [he]; ring

/-- The ideal diagonal environment is exactly the same CRT integral, with
the two outer cutoffs and remaining inactive regular density retained. -/
theorem movingPatternPrimeObservable_outer_integral_crt (x : Fin (N + 1) → primes)
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
    (density Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun side => (T side).formulaNodes value
      (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq side)
      (.prime false) (.prime true)
    (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) * (density : ℂ)) *
        movingPatternPrimeObservable e t small slot perm pattern primes hprimes childBound pivotBound
          hfreq F E outside R r p g twist input Q y ψ X lo hi hlo hhi φ G
          (Real.exp z) (Real.exp y) x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) *
      movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
        n t small (movingPatternBulkLeaves n m slot perm) pattern x =
    ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (Real.exp z) (Real.exp y) * (Real.exp (z - center) : ℂ) *
        ((density : ℂ) * correctedMixedPairAverage input Q
          (∏ j, movingArithmeticModuli r p P Finset.univ j)
          (movingSeparatedPairResidueCoefficient p value outside F E g (fun side i => twist i side)
            Finset.univ T nodes R) y) / (y : ℂ) := by
  dsimp only
  rw [movingPatternPrimeObservable_weighted_integral_crt e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist input Q ψ X lo hi hlo hhi φ G
    x P hP hinj hR hprecision hcover hc hpage]
  congr 1
  funext z
  congr 1
  funext y
  unfold movingOuterKernel
  ring

end
end Ostmann

end OAI
