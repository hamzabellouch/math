import OAI.NumberTheory.Ostmann.Characters.PeriodicPolynomialOneSidedBound
import OAI.NumberTheory.Ostmann.Construction.FiniteEmbeddingPrior

namespace OAI

/-! # Original sampling law with the small-frequency residue restrictions -/

namespace Ostmann

open scoped BigOperators Classical

/-- An arbitrary original sample in the long interval is extended by zero.
Its unary factor and mean are retained exactly. -/
theorem original_prior_periodic_polynomial_one_sided_bound {A : Type*} [Fintype A]
    (value : A → ℕ) (hinj : Function.Injective value)
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (gate : Q → ZMod M → ℂ) (hgate : ∀ q z, ‖gate q z‖ ≤ 1)
    (hlow : ∀ x, a ≤ value x) (hhigh : ∀ x, value x < a + K * M)
    {n t : ℕ} (F : Q → Fin n → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (keep : Q → (Fin t → Bool) → Bool)
    (B : ℝ) (R Bq : ℕ) (hB : 0 ≤ B)
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (ρ : A → ℝ) (ν : Q → ℝ) (U : A → ℂ) (V : Q → ℂ)
    (C α : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hρ : ∀ x, 0 ≤ ρ x) (hmassρ : ∑ x, ρ x ≤ 1)
    (hdom : ∀ x, ρ x ≤ C * (value x : ℝ)⁻¹)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ x, (ρ x : ℂ) * (U x * ∑ q : Q, (ν q : ℂ) * V q *
      (χ q (value x : ZMod (q : ℕ)) *
        (gate q (value x : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) (value x : ℝ))))‖ ^ 2 ≤
      C * (α * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  let e := intervalSampleEmbedding value hinj a (K * M) hlow hhigh
  let μ := cellPrior ρ e
  let U' := embeddingExtend e U
  have he (x : A) : a + (e x).val = value x :=
    intervalSampleEmbedding_value value hinj a (K * M) hlow hhigh x
  have hμ : ∀ j, 0 ≤ μ j := cellPrior_nonneg ρ e hρ
  have hμmass : ∑ j, μ j ≤ 1 := by
    change ∑ j, cellPrior ρ e j ≤ 1
    rw [cellPrior_mass]
    exact hmassρ
  have hμdom : ∀ j, μ j ≤ C * ((a + j.val : ℕ) : ℝ)⁻¹ := by
    apply cellPrior_embedding_le e ρ _ (fun j => by positivity)
    intro x
    rw [he]
    exact hdom x
  have hU' : ∀ j, ‖U' j‖ ≤ 1 := embeddingExtend_norm_le e U 1 (by norm_num) hU
  have hb := periodic_polynomial_one_sided_bound Q hprime χ hnonprincipal a M K ha hM gate hgate F H keep B R Bq
    hB hbudget hcomplexity hBq μ ν U' V C α hC hα hμ hμmass hμdom hν hmassν hatom hU' hV
  let f : Fin (K * M) → ℂ := fun j => U' j * ∑ q : Q, (ν q : ℂ) * V q *
    (χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
      (gate q ((a + j.val : ℕ) : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) ((a + j.val : ℕ) : ℝ)))
  have hs := sum_cellPrior_mul ρ e f
  have hf (x : A) : f (e x) = U x * ∑ q : Q, (ν q : ℂ) * V q *
      (χ q (value x : ZMod (q : ℕ)) * (gate q (value x : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) (value x : ℝ))) := by
    dsimp only [f, U']
    rw [embeddingExtend_apply, he]
  simp only [hf] at hs
  rw [hs]
  exact hb

end Ostmann

end OAI
