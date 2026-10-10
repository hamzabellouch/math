import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeSymmetrizedCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeLiveSymmetrization

namespace OAI

/-! # Harmonic cost for live priors and the literal coefficient support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitude_symmetrized_full_harmonic_cost_live
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ)
    (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hidentical : ∀ j k : TreeLeafIndex n × Fin m,
      primeSubsetPrior P (Q (movingTemplateBulk n r m j)) =
        primeSubsetPrior P (Q (movingTemplateBulk n r m k)))
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (Gmin : ℝ) (hX : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → Real.exp Gmin ≤ (q : ℝ))
    (totalLower : ℝ)
    (hproduct : ∀ (u : TreeLeafIndex n × Fin 4 → P), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (a : MovingAmplitudeIndex P Pg n r m V),
      (∀ i, primeSubsetPrior P (Q i) (a.2.1 i) ≠ 0) →
      ∀ p : ℕ, movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m a.2.2.val u a.2.1 p a.1 ≠ 0 →
      Real.exp totalLower ≤ ((∏ i, (a.2.1 i : ℕ) : ℕ) : ℝ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      totalLower) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V F φ G n r m Pg I
      (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i)) greg ggiant favorable ≤
      K * movingAmplitudeSymmetrizedRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg := by
  intro K
  have hdiag := movingAmplitude_symmetrized_harmonic_diagonal_live P Pg I hP hPg outside μ hμ0
    childBound pivotBound V F hF φ hφ0 hφ1 G n r m Q hidentical hvg hvr hsep greg ggiant favorable
  apply hdiag.trans
  dsimp only at hdiag ⊢
  unfold movingAmplitudeSymmetrizedRegularEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : (∏ i, μ n (u i)) = 0
  · simp only [hu, zero_mul, mul_zero, Finset.sum_const_zero, le_refl]
  have hU : 0 ≤ (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => hμ0 n (u i))) (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro a _
  let α := movingAmplitudePrior Pg n r m V (smoothGiantPrior Pg φ (G (n + 1)))
    (fun i => primeSubsetPrior P (Q i)) a
  have hα : 0 ≤ α := mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ0 a.1)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (a.2.1 i)))
  by_cases ha : α = 0
  · simp only [show movingAmplitudePrior Pg n r m V (smoothGiantPrior Pg φ (G (n + 1)))
      (fun i => primeSubsetPrior P (Q i)) a = 0 from ha, zero_mul, mul_zero, le_refl]
  have hν i : primeSubsetPrior P (Q i) (a.2.1 i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha) i (Finset.mem_univ i)
  by_cases hc : movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m a.2.2.val u a.2.1 p a.1 = 0
  · simp only [hc, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hcost := moving_harmonic_full_counterpart_le n r m Q
    (smoothGiantLogNormalizer Pg φ (G (n + 1))) Gmin totalLower
    (a.1 : ℕ) (fun i => (a.2.1 i : ℕ)) (hX a.1 (left_ne_zero_of_mul ha))
    (hproduct u hu a hν p hc)
  have hpos := mul_nonneg hU (hφ0 (Real.log p - G (n + 1)))
  have hcost' := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg (mul_nonneg hpos hα) (sq_nonneg
      ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m a.2.2.val u a.2.1 p a.1 *
        primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
          (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖))
  dsimp only [α] at hcost'
  simp only [Nat.cast_prod] at hcost'
  dsimp only [K]
  simp only [Nat.cast_prod]
  convert hcost' using 1 <;> ring

end Ostmann

end OAI
