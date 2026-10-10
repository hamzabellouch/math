import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternSupportedMean
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternPriorSupport

namespace OAI

/-! # Combining arithmetic and bulk cancellation on the original support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPrimePattern_signed_arithmetic_on_support {A B C : Type*}
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
    (hdisjoint : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hcross : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ b c,
      prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hfmod : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0))
    (m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (hbulkEq : bulk = movingPatternBulkLeaves n m slot perm)
    (Dminor : ℝ)
    (hminor : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      ‖movingPatternBulkMean e ν slot G x‖ ≤ Dminor)
    (seed : TreeLeafIndex n × Fin m → A) :
    let κ := (4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern x‖ ≤
      κ * (D * (((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) +
        2 * ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
          ((2 * ((n + 1) * d) : ℕ) * α +
            (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)) + Dminor) := by
  have ha := movingPrimePattern_arithmetic_comparison_on_support e prime hpInj hprime tierB tierC t small bulk pattern rep
    hsmall hbulk htier d F U hF hU hsize hfreq hvalues μ ν hμ hν hmass hnmass
    E α β V hE hα hβ hV hbound hmax hnmax hpmax hprimeSize G D hD hG hdisjoint hcross hfmod
  have hb : ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x‖ ≤
      Dminor * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) := by
    rw [hbulkEq]
    simpa only [mul_comm] using
      movingPrimePattern_signed_bulk_mean_on_support e μ ν prime t small slot perm pattern rep E hE
        hprime hμ hν hmass hnmass hbound G Dminor hminor seed
  dsimp only at ha ⊢
  let X := ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
    movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern x
  let Y := ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
    movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x
  have heq : X - Y = ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x) := by
    dsimp only [X, Y]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have htriangle : ‖X‖ ≤ ‖X - Y‖ + ‖Y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (X - Y) Y
  rw [heq] at htriangle
  exact htriangle.trans ((add_le_add ha hb).trans_eq (by ring))

end Ostmann

end OAI
