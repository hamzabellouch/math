import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternExternalPrior

namespace OAI

/-! # The bounded cost of restricting both giants to prime residues -/

namespace Ostmann
open scoped Classical BigOperators

theorem internalLineScalar_prime_le_twice (p : ℕ) (hp : p.Prime) :
    internalLineScalar false p ≤ 2 * internalLineScalar true p := by
  have hsub : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hsubpos : (0 : ℝ) < (p - 1 : ℕ) := Nat.cast_pos.mpr hsub
  have hsize : (p : ℝ) ≤ 2 * (p - 1 : ℕ) := by
    have h := Nat.sub_add_cancel hp.one_le
    have := hp.two_le
    exact_mod_cast (show p ≤ 2 * (p - 1) by omega)
  simp only [internalLineScalar, Bool.false_eq_true, ite_false, ite_true]
  have h : (1 : ℝ) / (p - 1 : ℕ) ≤ 2 / p := by
    apply (div_le_div_iff₀ hsubpos hpos).mpr
    simpa only [one_mul] using hsize
  simpa only [div_eq_mul_inv, one_mul] using h

theorem prime_line_scalar_product_le {C : Type*} [Fintype C]
    (p : C → ℕ) (hp : ∀ c, (p c).Prime) :
    (∏ c, internalLineScalar false (p c)) ≤
      (2 : ℝ) ^ Fintype.card C * ∏ c, internalLineScalar true (p c) := by
  calc
    _ ≤ ∏ c, (2 * internalLineScalar true (p c)) :=
      Finset.prod_le_prod₀ (fun c _ => internalLineScalar_nonneg false (p c))
        (fun c _ => internalLineScalar_prime_le_twice (p c) (hp c))
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The change of giant law costs two per internal equality class, never per
external or bulk coordinate. -/
theorem movingPattern_fin_prime_prior_bound {A B C : Type*}
    [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (x : Fin (N + 1) → A) :
    let W := ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
    ‖W‖ * (∏ c, internalLineScalar false (prime (x (e.symm (.inr c))))) ≤
      (D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior (fun i => Sum.elim ν
          (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  intro W
  have h := movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound
    G D hD hG x
  have hc := prime_line_scalar_product_le (fun c => prime (x (e.symm (.inr c))))
    (fun _ => hprime _)
  calc
    _ ≤ ‖W‖ * ((2 : ℝ) ^ Fintype.card C *
        ∏ c, internalLineScalar true (prime (x (e.symm (.inr c))))) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = (2 : ℝ) ^ Fintype.card C * (‖W‖ *
        ∏ c, internalLineScalar true (prime (x (e.symm (.inr c))))) := by ring
    _ ≤ (2 : ℝ) ^ Fintype.card C * ((D * ((2 : ℝ) ^ Fintype.card C *
        E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior (fun i => Sum.elim ν
          (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

end Ostmann

end OAI
