import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeIndexedProbability
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLineProductComparison

namespace OAI

/-! # Symbolic replacement for the actual two-history internal line factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem moving_prime_actual_line_product_comparison {A J : Type*}
    [Fintype A] [Nonempty A] [Fintype J] {N n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (T : Bool → MovingSlotData (Fin (N + 1)) n) (tier : Fin (N + 1) → ℕ)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : J → Fin (N + 1)) (base : ∀ j, MovingPairRepresentativeOccurrences T (rep j))
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ side, (T side).SizeLE d)
    (hfreq : ∀ side, (T side).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : Fin (N + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (rep j) a ≤ β)
    (hprimeSize : ∀ j a, μ (rep j) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (weight : (Fin (N + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hweight : ∀ x, ‖weight x‖ * ∏ j, internalLineScalar false (prime (x (rep j))) ≤ B)
    (hdisjoint : ∀ x, weight x ≠ 0 → ∀ i j,
      tier i ≠ tier j → prime (x i) ≠ prime (x j))
    (hunique : ∀ x, weight x ≠ 0 → ∀ j i, prime (x i) = prime (x (rep j)) → i = rep j)
    (hfmod : ∀ x, weight x ≠ 0 → ∀ j side,
      (T side).Frequencies (fun s => (s : ZMod (prime (x (rep j)))) ≠ 0)) :
    ‖∑ x, (productPrior μ x : ℂ) * weight x *
      ((∏ j, (movingSampledInternalPrimeProbability prime hprime T x (rep j) : ℂ)) -
       ∏ j, (internalLineFlagWeight false (prime (x (rep j)))
         (fun s => arithmeticTestFlag (lineTestPolynomials
           (movingIndexedLine T (rep j) (base j)) ⟨(base j).1, (base j).2.val⟩ s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card (MovingPairOccurrenceIndex T))) *
        ((2 * ((n + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β) := by
  let path := fun j o => (movingIndexedOccurrence T (rep j) (base j) o).path
  let current := fun j o => (movingIndexedOccurrence T (rep j) (base j) o).current
  let b : J → MovingPairOccurrenceIndex T := fun j => ⟨(base j).1, (base j).2.val⟩
  have hi : Function.Injective (fun a => (prime a : ℤ)) := by
    intro a b h
    apply hpInj
    exact Int.ofNat.inj h
  have hu (x : Fin (N + 1) → A) (hx : weight x ≠ 0) (j : J) (o : MovingPairOccurrenceIndex T) :=
    movingIndexedOccurrence_units T tier (fun i => prime (x i)) (fun i => hprime (x i))
      (hdisjoint x hx) hlevels (rep j) (base j) (hfmod x hx j) o
  have h := moving_slot_line_product_comparison (fun a => (prime a : ℤ)) hi prime hpInj hprime
    path current b rep (fun _ => false) n d F U hF hU
    (fun j o => movingIndexedOccurrence_path_length T tier hlevels (rep j) (base j) o)
    (fun j o => movingIndexedOccurrence_size T d F hsize hfreq (rep j) (base j) o)
    (fun j o => movingIndexedOccurrence_absent T tier hlevels (rep j) (base j) o)
    hvalues μ hμ hmass α β V hα hβ hV hmax hpmax hprimeSize weight B hB hweight
    (by
      intro x hx j o s hs
      simpa only [integerLineReduction, MovingSlotReversal.naturalReduction, Int.cast_natCast] using
        (hu x hx j o).1 s hs)
    (by
      intro x hx j
      simpa only [integerLineReduction, MovingSlotReversal.naturalReduction, Int.cast_natCast] using
        (hu x hx j (b j)).2)
  have he (x : Fin (N + 1) → A) :
      weight x * (∏ j, (movingSampledInternalPrimeProbability prime hprime T x (rep j) : ℂ)) =
      weight x * ∏ j, (movingSlotLineProbability (fun a => (prime a : ℤ)) prime hprime
        (path j) (current j) false x (x (rep j)) : ℂ) := by
    by_cases hx : weight x = 0
    · simp only [hx, zero_mul]
    · congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact congrArg (fun r : ℝ => (r : ℂ))
        (movingSampledIndexedPrimeProbability prime hprime x T tier (hdisjoint x hx) hlevels
          (rep j) (base j) (hunique x hx j) (hfmod x hx j))
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_assoc, mul_sub, he, ← mul_sub, ← mul_assoc]
  rfl

end Ostmann

end OAI
