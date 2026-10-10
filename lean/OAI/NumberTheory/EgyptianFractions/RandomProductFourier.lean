import OAI.NumberTheory.EgyptianFractions.BilinearFourier
import OAI.NumberTheory.EgyptianFractions.PrimeProductFibers

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Regroup a finite sum by the fibers of a map, with explicit fiber cardinalities. -/
lemma sum_fiber_card_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (g : κ → ℂ) :
    (∑ r : κ, ((Finset.univ.filter (fun a : ι => f a = r)).card : ℂ) * g r) =
      ∑ a : ι, g (f a) := by
  classical
  calc
    _ = ∑ r : κ, ∑ a ∈ Finset.univ.filter (fun a : ι => f a = r), g (f a) := by
      apply Finset.sum_congr rfl
      intro r _
      symm
      calc
        _ = ∑ a ∈ Finset.univ.filter (fun a : ι => f a = r), g r := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
        _ = _ := by simp
    _ = _ := Finset.sum_fiberwise _ f (fun a => g (f a))

/-- The mass function of a prime product is the pushforward of uniform counting. -/
lemma primeProductModMass_average (P : Finset ℕ) (s q : ℕ) [NeZero q]
    (g : ZMod q → ℂ) :
    (∑ r : ZMod q, (primeProductModMass P s q r : ℂ) * g r) =
      (∑ a : Fin s → ↥P, g ((∏ i, (a i : ℕ)) : ZMod q)) / (P.card : ℂ)^s := by
  simp only [primeProductModMass, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow, div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_fiber_card_mul]

/-- Two independent prime products correspond to the product of their residue masses. -/
lemma primeProductModMass_double_average (P : Finset ℕ) (s q : ℕ) [NeZero q]
    (g : ZMod q → ZMod q → ℂ) :
    (∑ x : ZMod q, ∑ y : ZMod q,
      (primeProductModMass P s q x : ℂ) *
        (primeProductModMass P s q y : ℂ) * g x y) =
      (∑ a : Fin s → ↥P, ∑ b : Fin s → ↥P,
        g ((∏ i, (a i : ℕ)) : ZMod q) ((∏ i, (b i : ℕ)) : ZMod q)) /
          ((P.card : ℂ)^s)^2 := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [primeProductModMass_average]
  simp_rw [← Finset.sum_div]
  rw [div_div, pow_two]

/-- Exponential cancellation for two independent uniform prime products whenever
all attainable integer products are smaller than the modulus. Repetitions among
sampled primes are permitted. -/
theorem prime_product_bilinear_average_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hne : P.Nonempty)
    (s q : ℕ) [NeZero q]
    (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q)
    (c : (ZMod q)ˣ) :
    ‖(∑ a : Fin s → ↥P, ∑ b : Fin s → ↥P,
      ZMod.stdAddChar ((c : ZMod q) * ((∏ i, (a i : ℕ)) : ZMod q) *
        ((∏ i, (b i : ℕ)) : ZMod q))) / ((P.card : ℂ)^s)^2‖ ≤
      Real.sqrt (q : ℝ) * ((s.factorial : ℝ) / (P.card : ℝ)^s) := by
  have h := residue_bilinear_probability_bound
    (primeProductModMass P s q) (primeProductModMass P s q)
    ((s.factorial : ℝ) / (P.card : ℝ)^s)
    ((s.factorial : ℝ) / (P.card : ℝ)^s) c
    (primeProductModMass_nonneg P s q) (primeProductModMass_nonneg P s q)
    (primeProductModMass_le P hP s q hsmall) (primeProductModMass_le P hP s q hsmall)
    (sum_primeProductModMass P hne s q) (sum_primeProductModMass P hne s q)
  rw [primeProductModMass_double_average] at h
  simpa only [mul_assoc, Real.mul_self_sqrt (by positivity :
      0 ≤ (s.factorial : ℝ) / (P.card : ℝ)^s)] using h

end Problem337

end

end OAI
