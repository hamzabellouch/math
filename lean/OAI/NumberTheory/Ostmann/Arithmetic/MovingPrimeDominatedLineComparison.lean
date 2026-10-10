import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeActualLineComparison
import OAI.NumberTheory.Ostmann.ZeroDensity.FinitePriorDensity

namespace OAI

/-! # Symbolic line comparison under the dominated equality-pattern law -/

namespace Ostmann
open scoped Classical BigOperators

/-- The complete original pattern weight may be used directly once its product
of line scalars is dominated by the representative priors. In particular, the
pattern law is not assumed to be independent. -/
theorem moving_prime_dominated_line_product_comparison {A J : Type*}
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
    (hweight : ∀ x, ‖weight x‖ * ∏ j, internalLineScalar false (prime (x (rep j))) ≤ B * productPrior μ x)
    (hdisjoint : ∀ x, weight x ≠ 0 → ∀ i j,
      tier i ≠ tier j → prime (x i) ≠ prime (x j))
    (hunique : ∀ x, weight x ≠ 0 → ∀ j i, prime (x i) = prime (x (rep j)) → i = rep j)
    (hfmod : ∀ x, weight x ≠ 0 → ∀ j side,
      (T side).Frequencies (fun s => (s : ZMod (prime (x (rep j)))) ≠ 0)) :
    ‖∑ x, weight x *
      ((∏ j, (movingSampledInternalPrimeProbability prime hprime T x (rep j) : ℂ)) -
       ∏ j, (internalLineFlagWeight false (prime (x (rep j)))
         (fun s => arithmeticTestFlag (lineTestPolynomials
           (movingIndexedLine T (rep j) (base j)) ⟨(base j).1, (base j).2.val⟩ s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card (MovingPairOccurrenceIndex T))) *
        ((2 * ((n + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β) := by
  let prior := fun x : Fin (N + 1) → A => productPrior μ x
  let c := fun x : Fin (N + 1) → A =>
    ∏ j, internalLineScalar false (prime (x (rep j)))
  have hc (x : Fin (N + 1) → A) : 0 < c x := by
    apply Finset.prod_pos
    intro j _
    simp only [internalLineScalar, Bool.false_eq_true, ite_false]
    exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.sub_pos_of_lt (hprime (x (rep j))).one_lt))
  have hprior (x : Fin (N + 1) → A) : 0 ≤ prior x := productPrior_nonneg μ hμ x
  have hd (x : Fin (N + 1) → A) : finitePriorDensity prior weight x ≠ 0 → weight x ≠ 0 :=
    finitePriorDensity_ne_zero prior weight x
  have h := moving_prime_actual_line_product_comparison prime hpInj hprime T tier hlevels rep base
    d F U hF hU hsize hfreq hvalues μ hμ hmass α β V hα hβ hV hmax hpmax hprimeSize
    (finitePriorDensity prior weight) B hB
    (finitePriorDensity_bound prior weight c B hprior hB hweight)
    (fun x hx => hdisjoint x (hd x hx)) (fun x hx => hunique x (hd x hx))
    (fun x hx => hfmod x (hd x hx))
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [finitePriorDensity_cancel prior weight c B hc hweight x]

end Ostmann

end OAI
