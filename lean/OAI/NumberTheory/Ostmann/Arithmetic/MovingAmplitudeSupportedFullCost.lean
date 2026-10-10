import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeEnergyLogNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullHarmonicCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeSupportedHarmonic

namespace OAI

/-! # The complete small and bulk denominator in the original diagonal -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitude_full_harmonic_cost_supported
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
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j : TreeLeafIndex n × Fin r, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) q ≠ 0 → Real.exp (lower j) ≤ (q : ℝ))
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ q : P, V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → ∀ a : P, (q : ℕ) ≠ (a : ℕ))
    (Gmin : ℝ) (hX : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → Real.exp Gmin ≤ (q : ℝ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let Fw := fun x s =>
      (movingBulkLeafLogWeight Subtype.val tier k outside cb cd x.data : ℂ) * F x s
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1))) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V Fw φ G n r m Pg I
      (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i)) greg ggiant favorable ≤
      K * movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V Fw φ G n r m Q greg := by
  intro Fw K
  have hFw x : Fw x 0 = 0 := by simp only [Fw, hF, mul_zero]
  have hdiag := movingAmplitude_harmonic_diagonal_supported P Pg I hP hPg outside μ hμ0
    childBound pivotBound V Fw hFw φ hφ0 hφ1 G n r m Q hvg hvr hsep greg ggiant favorable
  apply hdiag.trans
  dsimp only at hdiag ⊢
  unfold movingAmplitudeRegularEnergy
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
  by_cases hc : movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw φ G
      n (4 + r) m a.2.2.val (movingRestoreSample n r m u a.2.1) p a.1 = 0
  · simp only [hc, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hcost := movingTemplate_restored_full_harmonic_cost_le Subtype.val tier
    (fun q => (hP q q.property).pos) k outside cb cd μ hμ childBound pivotBound V F φ G
    n r m a.2.2.val u hu a.2.1 hn (fun j => hsmall j _ (hν _))
    (fun j => hbulk j _ (hν _)) lower (fun j => hlower j _ (hν _)) p a.1 Q (smoothGiantLogNormalizer Pg φ (G (n + 1)))
    Gmin (hX a.1 (left_ne_zero_of_mul ha)) hc
  have hpos := mul_nonneg hU (hφ0 (Real.log p - G (n + 1)))
  have hcost' := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg (mul_nonneg hpos hα) (sq_nonneg
      ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw φ G
        n (4 + r) m a.2.2.val (movingRestoreSample n r m u a.2.1) p a.1 *
        primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
          (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖))
  dsimp only [α] at hcost'
  simp only [Nat.cast_prod] at hcost'
  dsimp only [K]
  simp only [Nat.cast_prod]
  convert hcost' using 1 <;> ring

/-- The full diagonal reduces to the original one-branch energy with its explicit counterpart cost. -/
theorem movingAmplitude_full_harmonic_unweighted_cost_supported
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
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j : TreeLeafIndex n × Fin r, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) q ≠ 0 → Real.exp (lower j) ≤ (q : ℝ))
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ q : P, V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → ∀ a : P, (q : ℕ) ≠ (a : ℕ))
    (Gmin : ℝ) (hX : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → Real.exp Gmin ≤ (q : ℝ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let Fw := fun x s =>
      (movingBulkLeafLogWeight Subtype.val tier k outside cb cd x.data : ℂ) * F x s
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1))) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V Fw φ G n r m Pg I
      (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i)) greg ggiant favorable ≤
      K * movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg := by
  intro Fw K
  have hcost := movingAmplitude_full_harmonic_cost_supported P Pg I hP hPg tier k outside cb cd μ hμ0 hμ
    childBound pivotBound V F hF φ hφ0 hφ1 G n r m hn Q hsmall hbulk lower hlower hvg hvr hsep
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
