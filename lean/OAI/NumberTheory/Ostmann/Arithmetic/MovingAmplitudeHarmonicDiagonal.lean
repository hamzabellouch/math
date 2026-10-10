import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeTerms
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateHarmonicDiagonal

namespace OAI

/-! # Harmonic product-fibre control of the whole prime amplitude diagonal -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitude_harmonic_diagonal_le
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hvg : ∀ q : Pg, V n < (q : ℕ)) (hvr : ∀ q : P, V n < (q : ℕ))
    (hsep : ∀ q : Pg, ∀ a : P, (q : ℕ) ≠ (a : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let ν := fun i => primeSubsetPrior P (Q i)
    let A := MovingAmplitudeIndex P Pg n r m V
    let α := fun a : A => movingAmplitudePrior Pg n r m V ρ ν a
    let θ := fun a : A =>
      (Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1))) / (a.1 : ℕ)) *
      ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, (a.2.1 i : ℕ)) : ℝ)⁻¹
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V F φ G n r m Pg I
      ρ ν greg ggiant favorable ≤
    ∑ u : TreeLeafIndex n × Fin 4 → P, (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) *
      ∑ p ∈ I, φ (Real.log p - G (n + 1)) * ∑ a : A, α a * θ a *
        ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
          n (4 + r) m a.2.2.val (movingRestoreSample n r m u a.2.1) p a.1 *
          primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
            (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖ ^ 2 := by
  intro ρ ν A α θ
  unfold movingAmplitudeDiagonal
  dsimp only
  apply Finset.sum_le_sum
  intro u _
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hμ n (u i))) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hφ0 _)
  have hd := movingTemplate_harmonic_diagonal_le P Pg hP hPg outside μ childBound pivotBound V
    F hF φ hφ0 hφ1 G (G (n + 1)) n r m Q u p hvg hvr hsep greg ggiant favorable
  dsimp only at hd
  let : ∀ a : A, Fact (a.1 : ℕ).Prime := fun a => ⟨hPg _ a.1.property⟩
  let : ∀ a : A, ∀ i, Fact (a.2.1 i : ℕ).Prime := fun a i => ⟨hP _ (a.2.1 i).property⟩
  simpa only [movingTemplateTransferWeight, movingAmplitudePrior, movingOneGiant_transform_tagged,
    ρ, ν, α, θ, Nat.cast_prod, Function.comp_def]
    using hd

end Ostmann

end OAI
