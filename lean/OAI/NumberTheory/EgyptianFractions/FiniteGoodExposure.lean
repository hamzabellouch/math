import OAI.NumberTheory.EgyptianFractions.ConcreteGoodExposure

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Reindex independent coordinates in a uniform finite product average. -/
lemma expect_product_reindex {A B X : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Fintype X] (e : A ≃ B) (g : X → ℕ) (F : ℕ → ℂ) :
    (𝔼 w : A → X, F (∏ i, g (w i))) =
      𝔼 w : B → X, F (∏ i, g (w i)) := by
  classical
  apply Fintype.expect_equiv (e.arrowCongr (Equiv.refl X))
  intro w
  congr 1
  simpa [Equiv.arrowCongr_apply, Function.comp_def] using
    (e.symm.prod_comp (fun i => g (w i))).symm

/-- Conversion of two uniform finite function averages to the explicit
normalization used in the bilinear exponential-sum estimate. -/
lemma double_expect_fin_eq_sum (P : Finset ℕ) (s : ℕ)
    (F : (Fin s → ↥P) → (Fin s → ↥P) → ℂ) :
    (𝔼 a : Fin s → ↥P, 𝔼 b : Fin s → ↥P, F a b) =
      (∑ a : Fin s → ↥P, ∑ b : Fin s → ↥P, F a b) /
        ((P.card : ℂ)^s)^2 := by
  classical
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, div_div]
  simp [pow_two]

/-- Reindex two independent coordinate families simultaneously. -/
lemma double_expect_product_reindex {A B C D X : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (eA : A ≃ C) (eB : B ≃ D) (g : X → ℕ) (F : ℕ → ℕ → ℂ) :
    (𝔼 a : A → X, 𝔼 b : B → X, F (∏ i, g (a i)) (∏ i, g (b i))) =
      𝔼 a : C → X, 𝔼 b : D → X, F (∏ i, g (a i)) (∏ i, g (b i)) := by
  classical
  calc
    _ = 𝔼 a : C → X, 𝔼 b : B → X, F (∏ i, g (a i)) (∏ i, g (b i)) :=
      expect_product_reindex eA g (fun x => 𝔼 b : B → X, F x (∏ i, g (b i)))
    _ = _ := by
      apply Finset.expect_congr rfl
      intro a ha
      exact expect_product_reindex eB g (fun y => F (∏ i, g (a i)) y)

/-- The actual good-exposure bound with arbitrary finite coordinate types,
in the nested uniform-expectation form used after conditioning. -/
theorem concrete_good_exposure_expect {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S V : ℝ) (hA : Fintype.card A = freshLength S V)
    (hB : Fintype.card B = freshLength S V)
    (hS : 2 ≤ S) (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hPcard : S ^ 99 ≤ (P.card : ℝ))
    (hPupper : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (c u : ℕ) (hu : 0 < u) [NeZero u]
    (huV : (u : ℝ) ≤ Real.exp V)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ ((u / c.gcd u : ℕ) : ℝ))
    (t : ZMod u) :
    ‖𝔼 a : A → ↥P, 𝔼 b : B → ↥P,
      ZMod.stdAddChar
        (((c * (∏ i, (a i : ℕ)) * (∏ i, (b i : ℕ)) : ℕ) : ZMod u) - t)‖ ≤
      Real.exp (-V / 5) := by
  classical
  let F : ℕ → ℕ → ℂ := fun x y =>
    ZMod.stdAddChar (((c * x * y : ℕ) : ZMod u) - t)
  change ‖𝔼 a : A → ↥P, 𝔼 b : B → ↥P,
    F (∏ i, (a i : ℕ)) (∏ i, (b i : ℕ))‖ ≤ _
  rw [double_expect_product_reindex
    (Fintype.equivFinOfCardEq hA) (Fintype.equivFinOfCardEq hB)
    (fun p : ↥P => (p : ℕ)) F]
  rw [double_expect_fin_eq_sum]
  exact concrete_good_exposure_bound S V hS hV hVS P hPprime hPcard hPupper
    c u hu huV hq t

end Problem337.RandomProducts

end

end OAI
