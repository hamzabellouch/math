import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternProducts
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLineScalar
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternAveragedSquare

namespace OAI

/-! # Original-pattern arithmetic for two prime giant residues -/

namespace Ostmann
open scoped Classical BigOperators

open scoped Classical BigOperators

noncomputable def movingPrimePatternSquareDifference {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A) : ℂ :=
  let T := movingPatternFinData e n t small bulk pattern
  letI : ∀ c : C, Fact (prime (x (e.symm (.inr c)))).Prime := fun _ => ⟨hprime _⟩
  (∏ c, movingInternalPrimeAverage (fun i => prime (x i)) T (prime (x (e.symm (.inr c))))) -
    ∏ c, (movingSampledInternalPrimeProbability prime hprime T x (e.symm (.inr c)) : ℂ)

/-- All square exclusions can be removed under the literal dependent pattern
law. The loss keeps the inverse-prime scale from every internal class. -/
theorem movingPrimePattern_averaged_square_error {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (tierB : B → ℕ) (tierC : C → ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (E V : ℝ) (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hprimeSize : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≠ 0 →
      Real.exp V ≤ prime a)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hfmod : ∀ x, G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let W := fun x : Fin (N + 1) → A =>
      ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
    ‖∑ x, W x * movingPrimePatternSquareDifference e prime hprime n t small bulk pattern x‖ ≤
      (D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        ((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) := by
  dsimp only
  let T := movingPatternFinData e n t small bulk pattern
  let prior := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let W := fun x : Fin (N + 1) → A =>
    ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
  have hm (i) : ∑ a, prior i a = 1 := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hnmass b
    | inr c => exact hmass _
  have hdom (x) : ‖W x‖ *
      (∏ c, internalLineScalar false (prime (x (e.symm (.inr c))))) ≤
      (D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior prior x :=
    movingPattern_fin_prime_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound G D hD hG x
  apply productPrior_relative_error prior hm W
    (movingPrimePatternSquareDifference e prime hprime n t small bulk pattern)
    (fun x => ∏ c, internalLineScalar false (prime (x (e.symm (.inr c)))))
    (D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)))
    ((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) (by positivity)
    hdom
  intro x hx
  have hg : G x ≠ 0 := by
    intro hz
    exact hx (by simp only [W, hz, mul_zero])
  have hscalar : 0 < ∏ c, internalLineScalar false (prime (x (e.symm (.inr c)))) := by
    apply Finset.prod_pos
    intro c _
    simp only [internalLineScalar, Bool.false_eq_true, ite_false]
    exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.sub_pos_of_lt (hprime _).one_lt))
  have hprior : productPrior prior x ≠ 0 := by
    intro hz
    have hh := hdom x
    rw [hz, mul_zero] at hh
    exact (not_le_of_gt (mul_pos (norm_pos_iff.mpr hx) hscalar)) hh
  have hsample (c) : μ (movingSampleTier (rep c).val.2) (x (e.symm (.inr c))) ≠ 0 := by
    have hh := (Finset.prod_ne_zero_iff.mp hprior) (e.symm (.inr c)) (Finset.mem_univ _)
    simpa only [prior, Equiv.apply_symm_apply, Sum.elim_inr] using hh
  have h := movingPrimeRepresentativeProduct_error ((Sum.elim tierB tierC) ∘ e)
    (fun i => prime (x i)) (fun i => hprime _) (hdisjoint x hg) T
    (movingPatternFinData_levels e tierB tierC n t small bulk pattern hsmall hbulk htier)
    (fun c => e.symm (.inr c)) (movingPatternFinRepresentative e n t small bulk pattern rep)
    (hfmod x hg) V (fun c => hprimeSize c _ (hsample c))
  simpa only [movingPrimePatternSquareDifference, movingInternalPrimeLineProbability,
    movingSampledInternalPrimeProbability] using h

end Ostmann

end OAI
