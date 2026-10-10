import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternProducts
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLineScalar
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeDominatedLineComparison

namespace OAI

/-! # Original-pattern arithmetic for two prime giant residues -/

namespace Ostmann
open scoped Classical BigOperators

open scoped Classical BigOperators

/-- Apply the proved comparison to the actual pattern tree and its original
external priors. All occurrence rows and unique representatives are derived
from that constructor. The loss involves internal classes, not bulk size. -/
theorem movingPrimePattern_line_comparison {A B C : Type*}
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
      V ≤ Real.log (prime a : ℝ))
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hclasses : ∀ x, G x ≠ 0 → Function.Injective (fun c => x (e.symm (.inr c))))
    (hcross : ∀ x, G x ≠ 0 → ∀ b c,
      prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hfmod : ∀ x, G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let T := movingPatternFinData e n t small bulk pattern
    let base := movingPatternFinRepresentative e n t small bulk pattern rep
    let W := fun x : Fin (N + 1) → A =>
      ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
    ‖∑ x, W x *
      ((∏ c, (movingSampledInternalPrimeProbability prime hprime T x (e.symm (.inr c)) : ℂ)) -
        ∏ c, (internalLineFlagWeight false (prime (x (e.symm (.inr c))))
          (fun s => arithmeticTestFlag (lineTestPolynomials
            (movingIndexedLine T (e.symm (.inr c)) (base c))
            ⟨(base c).1, (base c).2.val⟩ s = 0)) : ℂ))‖ ≤
      2 * (D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
        ((2 * ((n + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β) := by
  dsimp only
  let T := movingPatternFinData e n t small bulk pattern
  let prior := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let W := fun x : Fin (N + 1) → A =>
    ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
  have hnz (x) (hx : W x ≠ 0) : G x ≠ 0 := by
    intro hz
    exact hx (by simp only [W, hz, mul_zero])
  have hprior (i a) : 0 ≤ prior i a := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hν b a
    | inr c => exact hμ _ a
  have hmass' (i) : ∑ a, prior i a = 1 := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hnmass b
    | inr c => exact hmass _
  have hmax' (i a) : prior i a ≤ α := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hnmax b a
    | inr c => exact hmax _ a
  have hpmax' (c a) : prior (e.symm (.inr c)) a ≤ β := by
    simpa only [prior, Equiv.apply_symm_apply, Sum.elim_inr] using hpmax c a
  have h := moving_prime_dominated_line_product_comparison prime hpInj hprime T
    ((Sum.elim tierB tierC) ∘ e)
    (movingPatternFinData_levels e tierB tierC n t small bulk pattern hsmall hbulk htier)
    (fun c => e.symm (.inr c)) (movingPatternFinRepresentative e n t small bulk pattern rep)
    d F U hF hU hsize hfreq hvalues prior hprior hmass' α β V hα hβ hV hmax' hpmax'
    (fun c a ha => hprimeSize c a (by
      simpa only [prior, Equiv.apply_symm_apply, Sum.elim_inr] using ha)) W (D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)))
    (by positivity)
    (fun x => movingPattern_fin_prime_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound G D hD hG x)
    (fun x hx => hdisjoint x (hnz x hx))
    (fun x hx c i hi => movingPatternFin_unique e prime hpInj x
      (hclasses x (hnz x hx)) (hcross x (hnz x hx)) c i hi)
    (fun x hx c b => hfmod x (hnz x hx) c b)
  simpa only [movingPairOccurrenceIndex_card, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h

end Ostmann

end OAI
