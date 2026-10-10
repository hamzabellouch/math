import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternSquareError
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternLineComparison

namespace OAI

/-! # Original-pattern arithmetic for two prime giant residues -/

namespace Ostmann
open scoped Classical BigOperators

/-- Remove the actual prime-square exclusions and replace the remaining
simultaneous line probabilities by their symbolic flags under the original
pattern law. No injectivity assumption is imposed on the sampling measure. -/
theorem movingPrimePattern_arithmetic_comparison {A B C : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (tierB : B → ℕ) (tierC : C → ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ b, (movingPatternFinData e n t small bulk pattern b).SizeLE d)
    (hfreq : ∀ b, (movingPatternFinData e n t small bulk pattern b).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (E α β V : ℝ) (hE : 0 ≤ E) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hmax : ∀ j a, μ j a ≤ α) (hnmax : ∀ j a, ν j a ≤ α)
    (hpmax : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≤ β)
    (hprimeSize : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≠ 0 →
      Real.exp V ≤ prime a)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hcross : ∀ x, G x ≠ 0 → ∀ b c,
      prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hfmod : ∀ x, G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let κ := D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x)‖ ≤
      κ * (((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) +
        2 * ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
          ((2 * ((n + 1) * d) : ℕ) * α +
            (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)) := by
  let H := movingPatternInjectionGuard e G
  have hH : ∀ x, ‖H x‖ ≤ D := movingPatternInjectionGuard_norm e G D hD hG
  have hsupp (x) (hx : H x ≠ 0) : G x ≠ 0 :=
    (movingPatternInjectionGuard_nonzero e G x hx).2
  have hsq := movingPrimePattern_averaged_square_error e prime hprime tierB tierC t small bulk pattern rep
    hsmall hbulk htier μ ν hμ hν hmass hnmass E V hbound hprimeSize H D hD hH
    (fun x hx => hdisjoint x (hsupp x hx)) (fun x hx => hfmod x (hsupp x hx))
  have hline := movingPrimePattern_line_comparison e prime hpInj hprime tierB tierC t small bulk pattern rep
    hsmall hbulk htier d F U hF hU hsize hfreq hvalues μ ν hμ hν hmass hnmass E α β V
    hE hα hβ hV hbound hmax hnmax hpmax
    (fun c a ha => (Real.le_log_iff_exp_le (Nat.cast_pos.mpr (hprime a).pos)).mpr
      (hprimeSize c a ha))
    H D hD hH (fun x hx => hdisjoint x (hsupp x hx))
    (fun x hx => (movingPatternInjectionGuard_nonzero e G x hx).1)
    (fun x hx => hcross x (hsupp x hx)) (fun x hx => hfmod x (hsupp x hx))
  dsimp only at hsq hline ⊢
  have heq : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x)) =
    (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPrimePatternSquareDifference e prime hprime n t small bulk pattern x) +
    ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternPrimeLineProduct e prime hprime n t small bulk pattern x -
        movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    unfold movingPatternPrimeHaarProduct movingPrimePatternSquareDifference movingPatternPrimeLineProduct
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ _ + _ := add_le_add hsq hline
    _ = _ := by ring

end Ostmann

end OAI
