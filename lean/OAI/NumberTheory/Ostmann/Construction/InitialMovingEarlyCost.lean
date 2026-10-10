import OAI.NumberTheory.Ostmann.Construction.InitialMovingTemplateProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeSupportedFullCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeLiveHarmonic
import OAI.NumberTheory.Ostmann.Construction.InitialMovingNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalLeafMultiplier

namespace OAI

/-! # The first two diagonal costs retain both original half-cutoffs -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingAmplitude_initial_regular_harmonic_cost {J : Type}
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (b d rinit : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ)
    (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r : ℕ) (hlen : 4 + r + 4 * n = rinit + rinit)
    (Q : MovingRegularSlot n r (b + b) → Finset ℕ)
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j : TreeLeafIndex n × Fin r, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) q ≠ 0 → Real.exp (lower j) ≤ (q : ℝ))
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (Gmin : ℝ) (hX : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → Real.exp Gmin ≤ (q : ℝ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let Fw := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback) g Dq S ψ X lo hi
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) * ((Fintype.card (MovingRegularSlot n r (b + b))).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V Fw φ G n r (b + b) Pg I
      (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i)) greg ggiant favorable ≤
      K * movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V Fw φ G n r (b + b) Q greg := by
  intro Fw K
  have hFw x : Fw x 0 = 0 := movingOriginalLeaf_zero Subtype.val q
    (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
    (fun _ => initialMovingDataCutoff_zero Subtype.val b d rinit cb cd sl sr fallback _)
    g Dq S ψ X lo hi x
  have hdiag := movingAmplitude_harmonic_diagonal_live P Pg I hP hPg outside μ hμ0
    childBound pivotBound V Fw hFw φ hφ0 hφ1 G n r (b + b) Q hvg hvr hsep greg ggiant favorable
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
  let α := movingAmplitudePrior Pg n r (b + b) V (smoothGiantPrior Pg φ (G (n + 1)))
    (fun i => primeSubsetPrior P (Q i)) a
  have hα : 0 ≤ α := mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ0 a.1)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (a.2.1 i)))
  by_cases ha : α = 0
  · simp only [show movingAmplitudePrior Pg n r (b + b) V (smoothGiantPrior Pg φ (G (n + 1)))
      (fun i => primeSubsetPrior P (Q i)) a = 0 from ha, zero_mul, mul_zero, le_refl]
  have hν i : primeSubsetPrior P (Q i) (a.2.1 i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha) i (Finset.mem_univ i)
  by_cases hc : movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw φ G
      n (4 + r) (b + b) a.2.2.val (movingRestoreSample n r (b + b) u a.2.1) p a.1 = 0
  · simp only [hc, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hprod := movingTemplateCoefficient_original_initial_full_lower Subtype.val
    (fun p => (hP _ p.property).pos) b d rinit cb cd sl sr fallback q g Dq S ψ X lo hi
    outside μ childBound pivotBound V φ G n r a.2.2.val u a.2.1 hlen lower
    (fun j => hlower j _ (hν _)) p a.1 hc
  have hcost := moving_harmonic_full_counterpart_le n r (b + b) Q
    (smoothGiantLogNormalizer Pg φ (G (n + 1))) Gmin
    ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) a.1
    (fun i => (a.2.1 i : ℕ)) (hX a.1 (left_ne_zero_of_mul ha)) hprod
  have hpos := mul_nonneg hU (hφ0 (Real.log p - G (n + 1)))
  have hcost' := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg (mul_nonneg hpos hα) (sq_nonneg
      ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw φ G
        n (4 + r) (b + b) a.2.2.val (movingRestoreSample n r (b + b) u a.2.1) p a.1 *
        primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
          (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖))
  dsimp only [α] at hcost'
  simp only [Nat.cast_prod] at hcost'
  dsimp only [K]
  simp only [Nat.cast_prod]
  convert hcost' using 1 <;> ring

end Ostmann

end OAI
