import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticComparison

namespace OAI

/-! # Arithmetic comparison restricted to the original product support -/

namespace Ostmann
open scoped Classical BigOperators

/-- Vanishing representative prior forces the original compensated coefficient
it dominates to vanish as well. -/
theorem movingPattern_coefficient_zero_of_prior {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x = 0) :
    ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) = 0 := by
  have hd := movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound
    (fun _ => 1) 1 (by norm_num) (fun _ => by norm_num) x
  rw [hx, mul_zero] at hd
  simp only [mul_one] at hd
  have hscalar : 0 < ∏ c, internalLineScalar true (prime (x (e.symm (.inr c)))) := by
    apply Finset.prod_pos
    intro c _
    simp only [internalLineScalar, ite_true]
    exact inv_pos.mpr (Nat.cast_pos.mpr (hprime _).pos)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
    (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => x (e.symm (.inr (pattern i))))) : ℂ))]

/-- Restricting the observable to the representative product support preserves
its exact original, compensated pattern weight. -/
theorem movingOriginalPatternWeight_support_restrict {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => if productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x = 0 then 0 else G x) x =
      movingOriginalPatternWeight e μ ν prime n pattern G x := by
  by_cases hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x = 0
  · have hz := movingPattern_coefficient_zero_of_prior e μ ν prime pattern rep E
      hprime hμ hν hbound x hx
    simp only [movingOriginalPatternWeight, hz, zero_mul]
  · unfold movingOriginalPatternWeight movingPatternInjectionGuard
    split_ifs <;> simp only [hx, ite_false]

theorem movingPattern_arithmetic_comparison_on_support {A B C : Type*}
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
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let κ := D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternFlagProduct e prime n t small bulk pattern rep x)‖ ≤
      κ * (((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) +
        2 * ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
          ((2 * ((n + 1) * d) : ℕ) * α +
            (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)) := by
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let H := fun x => if productPrior law x = 0 then 0 else G x
  have hsupp (x) (hx : H x ≠ 0) : productPrior law x ≠ 0 ∧ G x ≠ 0 := by
    dsimp only [H] at hx
    split_ifs at hx with hz
    · exact False.elim (hx rfl)
    · exact ⟨hz, hx⟩
  have hH (x) : ‖H x‖ ≤ D := by
    dsimp only [H]
    split_ifs
    · simpa only [norm_zero] using hD
    · exact hG x
  have hh := movingPattern_arithmetic_comparison e prime hpInj hprime tierB tierC t small bulk
    pattern rep hsmall hbulk htier d F U hF hU hsize hfreq hvalues μ ν hμ hν hmass hnmass
    E α β V hE hα hβ hV hbound hmax hnmax hpmax hprimeSize H D hD hH
    (fun x hx => hdisjoint x (hsupp x hx).1 (hsupp x hx).2)
    (fun x hx => hcross x (hsupp x hx).1 (hsupp x hx).2)
    (fun x hx => hfmod x (hsupp x hx).1 (hsupp x hx).2)
  have heq (x) : movingOriginalPatternWeight e μ ν prime n pattern H x =
      movingOriginalPatternWeight e μ ν prime n pattern G x :=
    movingOriginalPatternWeight_support_restrict e μ ν prime pattern rep E hprime hμ hν hbound G x
  simp_rw [heq] at hh
  exact hh

end Ostmann

end OAI
