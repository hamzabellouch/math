import OAI.NumberTheory.Ostmann.Construction.HalfPrimeStatistic

namespace OAI

/-! # Separating the giant mean from the positive nongiant scalar -/

namespace Ostmann
open scoped Classical BigOperators

theorem weighted_tuple_mean_cons {A : Type*} [Fintype A] {n : ℕ}
    (μ₀ : A → ℝ) (μ : Fin n → A → ℝ) (f₀ : A → ℂ) (f : Fin n → A → ℂ)
    (w : (Fin n → A) → ℂ) :
    (∑ y : Fin (n + 1) → A, (productPrior (Fin.cons μ₀ μ) y : ℂ) *
      w (Fin.tail y) * ∏ i, Fin.cons (α := fun _ => A → ℂ) f₀ f i (y i)) =
      (∑ p : A, (μ₀ p : ℂ) * f₀ p) *
        ∑ x : Fin n → A, (productPrior μ x : ℂ) * w x * ∏ i, f i (x i) := by
  let e : A × (Fin n → A) ≃ (Fin (n + 1) → A) := Fin.consEquiv (fun _ => A)
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro x _
  change (productPrior (Fin.cons μ₀ μ) (Fin.cons (α := fun _ => A) p x) : ℂ) *
    w (Fin.tail (Fin.cons (α := fun _ => A) p x)) * ∏ i, Fin.cons (α := fun _ => A → ℂ) f₀ f i (Fin.cons (α := fun _ => A) p x i) = _
  simp only [productPrior_cons, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
    Fin.prod_univ_succ, Complex.ofReal_mul]
  ring

noncomputable def halfPrimeScalar {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ) : ℝ :=
  ∑ x : Fin n → P, productPrior μ x * w x * ∏ i, c i (x i)

/-- At an endpoint all nongiant residue tests have values independent of
the endpoint. Their original expectation is therefore one common scalar. -/
theorem halfPrimeMean_cons_scalar {n : ℕ} (P : Finset ℕ)
    (μ₀ : P → ℝ) (μ : Fin n → P → ℝ)
    (F₀ : (q : P) → ZMod (q : ℕ) → ℂ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ) (a : ℤ)
    (hc : ∀ i q, F i q (a : ZMod (q : ℕ)) = (c i q : ℂ)) :
    halfPrimeMean P (Fin.cons μ₀ μ) (Fin.cons F₀ F)
      (fun y => (w (Fin.tail y) : ℂ)) a =
      (halfPrimeScalar P μ w c : ℂ) * ∑ q : P, (μ₀ q : ℂ) * F₀ q (a : ZMod (q : ℕ)) := by
  let f₀ := fun q : P => F₀ q (a : ZMod (q : ℕ))
  let f := fun i q => F i q (a : ZMod (q : ℕ))
  have hfun (y : Fin (n + 1) → P) (i : Fin (n + 1)) :
      Fin.cons (α := fun _ => (q : P) → ZMod (q : ℕ) → ℂ) F₀ F i (y i) (a : ZMod (y i : ℕ)) = Fin.cons (α := fun _ => P → ℂ) f₀ f i (y i) := by
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  unfold halfPrimeMean
  simp_rw [hfun]
  rw [weighted_tuple_mean_cons μ₀ μ f₀ f (fun x => (w x : ℂ))]
  have hscalar : (∑ x : Fin n → P, (productPrior μ x : ℂ) * (w x : ℂ) * ∏ i, f i (x i)) =
      (halfPrimeScalar P μ w c : ℂ) := by
    dsimp only [f]
    simp_rw [hc]
    simp only [halfPrimeScalar, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]
  rw [hscalar, mul_comm]

/-- The balanced-event mass lower bound becomes the positive scalar used
in every endpoint mean, with both cutoff weights kept in the expectation. -/
theorem halfPrimeScalar_lower {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hw : ∀ x, 0 ≤ w x) (hc : ∀ i p, 0 ≤ c i p)
    (S : Finset (Fin n → P)) (β γ : ℝ) (hγ : 0 ≤ γ)
    (hmass : β ≤ ∑ x ∈ S, productPrior μ x * w x)
    (hgood : ∀ x ∈ S, ∀ i, γ ≤ c i (x i)) :
    β * γ ^ n ≤ halfPrimeScalar P μ w c := by
  have hpoint (x : Fin n → P) (hx : x ∈ S) : γ ^ n ≤ ∏ i, c i (x i) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => hγ) (fun i _ => hgood x hx i)
  calc
    _ ≤ (∑ x ∈ S, productPrior μ x * w x) * γ ^ n :=
      mul_le_mul_of_nonneg_right hmass (pow_nonneg hγ n)
    _ = ∑ x ∈ S, productPrior μ x * w x * γ ^ n := Finset.sum_mul ..
    _ ≤ ∑ x ∈ S, productPrior μ x * w x * ∏ i, c i (x i) :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hpoint x hx)
        (mul_nonneg (productPrior_nonneg μ hμ x) (hw x)))
    _ ≤ halfPrimeScalar P μ w c := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun x _ _ => mul_nonneg
        (mul_nonneg (productPrior_nonneg μ hμ x) (hw x))
        (Finset.prod_nonneg (fun i _ => hc i (x i))))

end Ostmann

end OAI
