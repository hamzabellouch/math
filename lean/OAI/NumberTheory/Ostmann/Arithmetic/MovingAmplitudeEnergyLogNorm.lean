import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeHarmonicCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogNorm

namespace OAI

/-! # The retained bulk cutoff in the one-branch diagonal energy -/

namespace Ostmann
open scoped Classical BigOperators

/-- This comparison is applied after the harmonic diagonal reduction.
The signed two-branch comparison keeps the log weights throughout. -/
theorem movingAmplitudeRegularEnergy_bulk_log_le
    (P Pg I : Finset ℕ) (tier : P → ℕ) (k : ℕ)
    (outside : List ℕ) (cb cd : ℝ) (μ : ℕ → P → ℝ)
    (hμ0 : ∀ j a, 0 ≤ μ j a) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (n r m : ℕ) (hn : n < k) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) q ≠ 0 → tier q ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inr j.2)) q ≠ 0 → tier q = k)
    (greg : ∀ q : ℕ, ZMod q → ℂ) :
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd x.data : ℂ) * F x s)
      φ G n r m Q greg ≤
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg := by
  unfold movingAmplitudeRegularEnergy
  dsimp only
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : (∏ i, μ n (u i)) = 0
  · simp only [hu, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hμ0 n (u i))) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hφ _)
  apply Finset.sum_le_sum
  intro a _
  let α := movingAmplitudePrior Pg n r m V (smoothGiantPrior Pg φ (G (n + 1)))
    (fun i => primeSubsetPrior P (Q i)) a
  have hα : 0 ≤ α := mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ a.1)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (a.2.1 i)))
  by_cases ha : α = 0
  · simp only [show movingAmplitudePrior Pg n r m V (smoothGiantPrior Pg φ (G (n + 1)))
      (fun i => primeSubsetPrior P (Q i)) a = 0 from ha, zero_mul, le_refl]
  have hν i : primeSubsetPrior P (Q i) (a.2.1 i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha) i (Finset.mem_univ i)
  apply mul_le_mul_of_nonneg_left _ hα
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact movingTemplateCoefficient_restored_bulk_log_norm_le Subtype.val tier k outside cb cd
    μ hμ childBound pivotBound V F φ G n r m a.2.2.val u hu a.2.1 hn
    (fun j => hsmall j _ (hν _)) (fun j => hbulk j _ (hν _)) p a.1

/-- The full diagonal reduces to the original one-branch energy with its explicit counterpart cost. -/
theorem movingAmplitude_harmonic_unweighted_cost_le
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (tier : P → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r m : ℕ) (hn : n < k) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) q ≠ 0 → tier q ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inr j.2)) q ≠ 0 → tier q = k)
    (hvg : ∀ q : Pg, V n < (q : ℕ)) (hvr : ∀ q : P, V n < (q : ℕ))
    (hsep : ∀ q : Pg, ∀ a : P, (q : ℕ) ≠ (a : ℕ))
    (Gmin : ℝ) (hX : ∀ q : Pg, Real.exp Gmin ≤ (q : ℝ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let Fw := fun x s =>
      (movingBulkLeafLogWeight Subtype.val tier k outside cb cd x.data : ℂ) * F x s
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      (2 ^ n : ℕ) * (cb - 1)) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V Fw φ G n r m Pg I
      (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i)) greg ggiant favorable ≤
      K * movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg := by
  intro Fw K
  have hcost := movingAmplitude_harmonic_cost_le P Pg I hP hPg tier k outside cb cd μ hμ0 hμ
    childBound pivotBound V F hF φ hφ0 hφ1 G n r m hn Q hsmall hbulk hvg hvr hsep
    Gmin hX greg ggiant favorable
  have hK : 0 ≤ K := by
    dsimp only [K]
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
        (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))))
  exact hcost.trans (mul_le_mul_of_nonneg_left
    (movingAmplitudeRegularEnergy_bulk_log_le P Pg I tier k outside cb cd μ hμ0 hμ
      childBound pivotBound V F φ hφ0 G n r m hn Q hsmall hbulk greg) hK)

end Ostmann

end OAI
